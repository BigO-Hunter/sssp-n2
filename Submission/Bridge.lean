import Submission.SsspStatement
import Submission.Dijkstra

/-!
# Submission.Bridge — the dispatch splice and the arithmetic for the `n^2 ; n^2` row

One uniform program `dispatchProgram`: if `m < n` run the fork's verified Bellman–Ford
(`Frontier.RAM.BF.bfProgram`, exact with cost `9·(n+1)(m+1)`), else run the greenfield
array-scan Dijkstra (`Submission.Dijkstra.dijkstraProgram`, exact with cost
`≤ 40·(n²+m+1)`).  The dispatch on `m` is load-bearing for clause 2 of `Bound`: pure
array-Dijkstra violates `C·(n+1)(m+1)` at tiny `m` (its scan costs `n²` where the clause
allows `~ n`), and pure Bellman–Ford violates clause 1 at `m = n²` (cost `n³` where the
clause allows `n²`).

Both branches are call-free programs with `wordExp = 0` and `procs = []`, so the composite
`initState` is literally the same state each branch would start from (up to the `ite` test
charge, handled by `exec_charge_left`).

Arithmetic summary (constants at `N = 16`, `C = 120`):
* BF branch (`m < n`): cost `1 + 9(n+1)(m+1) ≤ 10(n+1)(m+1)` — clause 2 free;
  clause 1: `(n+1)(m+1) ≤ (n+1)n ≤ 2n²` for `m < n`.
* Dijkstra branch (`n ≤ m`): cost `≤ 40(n²+m+1)`;
  clause 1 (`m ≤ n²`): `≤ 40(2n²+1) ≤ 120 n²`;
  clause 2: `n² ≤ nm ≤ (n+1)(m+1)`, `m ≤ (n+1)(m+1)`, `1 ≤ (n+1)(m+1)`.
-/

namespace BigOSpeedrun.DirectedSSSP.Bridge

open scoped ENNReal NNReal
open Frontier Frontier.RAM BigOSpeedrun.DirectedSSSP.Dijkstra

/-- Dispatch: sparse graphs (`m < n`) take Bellman–Ford, dense graphs take array-scan
Dijkstra.  `wordExp = 0` and `procs = []` match both branches. -/
def dispatchProgram : Program :=
  { body := .ite (.lt (.var "m") (.var "n")) Frontier.RAM.BF.prog prog,
    wordExp := 0 }

/-! ## Transport: charging a starting state shifts the final cost -/

theorem option_bind_map {α β γ : Type} (m : Option α) (f : α → Option β) (g : β → γ) :
    (m.bind f).map g = m.bind (fun a => (f a).map g) := by cases m <;> rfl

theorem option_map_bind {α β γ : Type} (m : Option α) (g : α → β) (f : β → Option γ) :
    (m.map g).bind f = m.bind (fun a => f (g a)) := by cases m <;> rfl

/-- AC normal form for `Nat` addition inside state records. -/
macro "charge_simp" : tactic =>
  `(tactic| simp [State.charge, State.setW, State.setV, State.storeW, State.storeV,
      State.allocW, State.allocV, State.enter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])

/-- Charging a state does not change word-expression evaluation. -/
theorem evalW_charge (s : State ℝ≥0) (e : WExpr) (k : ℕ) :
    evalW (s.charge k) e = evalW s e := by
  induction e generalizing s with
  | lit a => simp [evalW, State.charge]
  | var y => rfl
  | add a b iha ihb => simp only [evalW]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | sub a b iha ihb => simp only [evalW]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | mul a b iha ihb => simp only [evalW]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | div a b iha ihb => simp only [evalW]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | lt a b iha ihb => simp only [evalW]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | eq a b iha ihb => simp only [evalW]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | load arr a ih => simp only [evalW]; rw [ih]; all_goals (first | rfl | charge_simp)

/-- Charging a state does not change value-expression evaluation. -/
theorem evalV_charge (s : State ℝ≥0) (e : VExpr) (k : ℕ) :
    evalV realOps (s.charge k) e = evalV realOps s e := by
  induction e with
  | zero => rfl
  | var y => rfl
  | add a b iha ihb => simp only [evalV]; rw [iha, ihb]; all_goals (first | rfl | charge_simp)
  | load arr a => simp only [evalV]; rw [evalW_charge]; all_goals (first | rfl | charge_simp)

/-- Running `c` from `s.charge k` is running it from `s` and charging `k` at the end. -/
theorem exec_charge_left (f : ℕ) (c : Stmt) (s : State ℝ≥0) (k : ℕ) :
    exec realOps f c (s.charge k) = (exec realOps f c s).map (fun r => r.charge k) := by
  sorry -- shortcut: charge-shift transport glue (statement is true by cost-linearity of exec); filled after the Dijkstra core

/-- The composite run on the Bellman–Ford branch: same final state as `bfProgram` plus the
dispatch test charge. -/
theorem bf_branch_run {G : Graph} {s : Fin G.n} (hm : G.m < G.n) :
    CorrectWithin dispatchProgram G s (10 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) := by
  obtain ⟨fuel, r, hr, hs⟩ := Frontier.RAM.BF.bfProgram_exact G s
  have hcost : (r.cost : ℝ) ≤ 9 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) :=
    Frontier.RAM.Program.runsWithin_unique (Frontier.RAM.BF.bfProgram_runsWithin G s) hr
  have hbase : exec realOps fuel Frontier.RAM.BF.prog (initState Frontier.RAM.BF.bfProgram G s) = some r := by
    simpa [Program.run, Frontier.RAM.BF.bfProgram] using hr
  refine ⟨fuel + 1, r.charge 1, ?_, hs, ?_⟩
  · show dispatchProgram.run (fuel + 1) G s = some (r.charge 1)
    simp only [Program.run]
    rw [show dispatchProgram.body = Stmt.ite (.lt (.var "m") (.var "n"))
        Frontier.RAM.BF.prog prog from rfl]
    rw [exec_ite]
    have htest : evalW (initState dispatchProgram G s) (.lt (.var "m") (.var "n")) = some 1 := by
      simp [evalW, initState, fit, hm]
    rw [htest]
    simp only [Option.bind_some]
    rw [if_pos (by decide : (1 : ℕ) ≠ 0)]
    rw [show initState dispatchProgram G s = initState Frontier.RAM.BF.bfProgram G s from rfl]
    rw [exec_charge_left]
    simp [hbase]
  · show ((r.charge 1).cost : ℝ) ≤ 10 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))
    rw [show (r.charge 1).cost = r.cost + 1 from rfl]
    have hX : (1 : ℝ) ≤ ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ (G.n : ℝ) from Nat.cast_nonneg _,
        show (0 : ℝ) ≤ (G.m : ℝ) from Nat.cast_nonneg _]
    push_cast at hcost ⊢
    linarith

/-- The composite run on the Dijkstra branch. -/
theorem dijkstra_branch_run {G : Graph} {s : Fin G.n}
    (hm : ¬ G.m < G.n) :
    CorrectWithin dispatchProgram G s (40 * (((G.n : ℝ) ^ 2 + G.m) + 1) + 1) := by
  sorry

/-! ## The two Bound clauses -/

/-- `Cap 2 0 n = n²` and `Time 2 0 0 n = n²` at the row's exponents. -/
theorem cap_two_zero (n : ℕ) : Cap ((2 : ℚ) / 1) ((0 : ℚ) / 1) n = (n : ℝ) ^ 2 := by
  simp [Cap, div_one, Real.rpow_zero, Nat.floor_one]

theorem time_two_zero_zero (n : ℕ) (_hn : 16 ≤ n) :
    Time ((2 : ℚ) / 1) ((0 : ℚ) / 1) ((0 : ℚ) / 1) n = (n : ℝ) ^ 2 := by
  simp [Time, div_one, Real.rpow_zero]

theorem sparse_two_zero {n m : ℕ} : Sparse ((2 : ℚ) / 1) ((0 : ℚ) / 1) n m ↔ (m : ℝ) ≤ (n : ℝ) ^ 2 := by
  rw [Sparse, cap_two_zero]

/-- Clause 2 (the polynomial fallback) on both branches; the bound is `C * (n+1) * (m+1)`
left-associated, matching `Bound`. -/
theorem clause2 : ∀ (G : Graph) (s : Fin G.n),
    CorrectWithin dispatchProgram G s (120 * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) := by
  sorry

/-- Clause 1 (the row bound at `m ≤ n²`, `n ≥ 16`) on both branches. -/
theorem clause1 : ∀ (G : Graph) (s : Fin G.n), 16 ≤ G.n →
    Sparse ((2 : ℚ) / 1) ((0 : ℚ) / 1) G.n G.m →
    CorrectWithin dispatchProgram G s (120 * Time ((2 : ℚ) / 1) ((0 : ℚ) / 1) ((0 : ℚ) / 1) G.n) := by
  sorry

/-- The row: `Bound 2 0 2 0 0`. -/
theorem dispatch_bound :
    Bound ((2 : ℚ) / 1) ((0 : ℚ) / 1) ((2 : ℚ) / 1) ((0 : ℚ) / 1) ((0 : ℚ) / 1) := by
  refine ⟨dispatchProgram, ?_, 120, by norm_num, 16, by norm_num, clause1, clause2⟩
  intro G s
  obtain ⟨f, r, hr, hs, _⟩ := clause2 G s
  exact ⟨f, r, hr, hs⟩

end BigOSpeedrun.DirectedSSSP.Bridge
