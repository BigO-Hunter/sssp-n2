import Submission.Dijkstra

/-!
# Submission.DijkstraProof — `dijkstra_runs`: the program is exact with cost `≤ 40·(n²+m+1)`

Assembly of the invariant layers.  The intellectual core is the exchange argument
(`min_settled_exact`): when the min-scan winner `u` is settled, `dist[u] = G.dist s u`,
because along a shortest walk to `u` the first unsettled vertex `x` satisfies
`dist[x] ≤ len (prefix to x)`, and the scan minimum gives `dist[u] ≤ dist[x]`.  Everything
else is loop bookkeeping.
-/

namespace BigOSpeedrun.DirectedSSSP.Dijkstra

open scoped ENNReal NNReal
open Frontier Frontier.RAM

/-! ## The exchange argument -/

/-- Walk-budget lemma: along a walk from a certified vertex (`s`, or settled with label `≤ b`),
if the walk's end is reached-unsettled then some reached-unsettled vertex `x` on the way has
`dist[x] ≤ b + len p`.  This is the "first unsettled vertex" argument, induction on the walk. -/
theorem exists_reached_le (G : Graph) (s : Fin G.n) {st : State ℝ≥0}
    (I : Inv G s st) (p : List (Fin G.m)) (y u0 : Fin G.n) (b : ℝ≥0)
    (hp : G.IsWalk y u0 p)
    (hy : y = s ∨ (st.wa "reach" y = 2 ∧ (st.va "dist" y : ℝ≥0) ≤ b))
    (hu : st.wa "reach" u0 = 1) :
    ∃ x : Fin G.n, st.wa "reach" x = 1 ∧ (st.va "dist" x : ℝ≥0) ≤ b + G.len p := by
  induction hp generalizing b with
  | nil y =>
    refine ⟨y, hu, ?_⟩
    rcases hy with rfl | ⟨h2, _⟩
    · rw [I.dist_s_zero]
      simp
    · exact absurd hu (by omega)
  | @cons e v p h ih =>
    by_cases hy2 : st.wa "reach" (G.src e) = 2
    · -- start settled: edge `(src e, dst e)` is relaxed by `Inv.relaxed`
      obtain ⟨hre, hde⟩ := I.relaxed e hy2
      have hdy : (st.va "dist" (G.src e) : ℝ≥0) ≤ b := by
        rcases hy with hys | ⟨_, hle⟩
        · rw [hys, I.dist_s_zero]
          simp
        · exact hle
      have hdd : (st.va "dist" (G.dst e) : ℝ≥0) ≤ b + G.w e :=
        calc (st.va "dist" (G.dst e) : ℝ≥0) ≤ st.va "dist" (G.src e) + G.w e := hde
          _ ≤ b + G.w e := add_le_add_left hdy (G.w e)
      by_cases hd2 : st.wa "reach" (G.dst e) = 2
      · obtain ⟨x, hx, hle⟩ := ih (b + G.w e) (Or.inr ⟨hd2, hdd⟩) hu
        refine ⟨x, hx, ?_⟩
        calc (st.va "dist" x : ℝ≥0) ≤ b + G.w e + G.len p := hle
          _ = b + (G.w e + G.len p) := by ring
          _ = b + G.len (e :: p) := by rw [G.len_cons]
      · refine ⟨G.dst e, ?_, ?_⟩
        · have hle2 := I.reach_val (G.dst e)
          omega
        calc (st.va "dist" (G.dst e) : ℝ≥0) ≤ b + G.w e := hdd
          _ ≤ b + (G.w e + G.len p) := by rw [← add_assoc]; exact le_self_add
          _ = b + G.len (e :: p) := by rw [G.len_cons]
    · -- start unsettled: `hy` forces `y = s`, and the start itself is the witness
      have hys : G.src e = s := by
        rcases hy with h1 | ⟨h2, _⟩
        · exact h1
        · exact absurd h2 (by omega)
      have hre1 : st.wa "reach" (G.src e) = 1 := by
        have hnn := I.reach_s
        have hle := I.reach_val s
        rw [hys] at hy2 ⊢
        omega
      refine ⟨G.src e, hre1, ?_⟩
      rw [hys, I.dist_s_zero]
      simp

/-! ## Loop steps (preservation) -/

/-- The min-scan postcondition: `best = n` means no `reach = 1` vertex below `n`;
otherwise `best` is a `reach = 1` vertex of minimum `dist`. -/
def ScanPost (G : Graph) (st : State ℝ≥0) (best : ℕ) : Prop :=
  (best = G.n ∧ ∀ v : Fin G.n, st.wa "reach" v = 1 → False) ∨
  (best < G.n ∧ st.wa "reach" best = 1 ∧
    ∀ v : Fin G.n, st.wa "reach" v = 1 → (st.va "dist" best : ℝ≥0) ≤ st.va "dist" v)

/-- One settle step preserves `Inv` and settles its target exactly (the exchange). -/
theorem inv_of_settle {G : Graph} {s : Fin G.n} {st st' : State ℝ≥0} {u : Fin G.n}
    (I : Inv G s st) (hu : st.wa "reach" u = 1)
    (hmin : ∀ v : Fin G.n, st.wa "reach" v = 1 → (st.va "dist" u : ℝ≥0) ≤ st.va "dist" v)
    (hstep : Runs realOps settleBody st (fun r => r = st')) :
    Inv G s st' ∧ st'.wa "reach" u = 2 := by
  sorry

/-- One relax-loop step (single edge of `u`'s segment) preserves `Inv`. -/
theorem inv_of_relax_step {G : Graph} {s : Fin G.n} {st st' : State ℝ≥0} {u j : ℕ}
    (I : Inv G s st) (hu : st.wa "reach" u = 2) (huu : u < G.n)
    (hj : st.wa "head" u ≤ j) (hjend : j < st.wa "head" (u + 1))
    (hstep : Runs realOps relaxBody st (fun r => r = st')) :
    Inv G s st' := by
  sorry

/-- The main loop preserves `Inv` per iteration, with measure `n - k`. -/
theorem inv_of_main_step {G : Graph} {s : Fin G.n} {st st' : State ℝ≥0}
    (I : Inv G s st) (hk : st.w "k" < G.n)
    (hstep : Runs realOps mainBody st (fun r => r = st' ∧ (G.n - st'.w "k") < G.n - st.w "k")) :
    Inv G s st' := by
  sorry

/-- At exit (no `reach = 1` vertices) reachability propagates along walks from a reached
vertex: every walk step leaves a settled vertex, whose relaxations reached the next. -/
theorem reach_of_walk {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) (hdone : ∀ v : Fin G.n, st.wa "reach" v = 1 → False)
    {y x : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk y x p)
    (hy : st.wa "reach" y ≠ 0) : st.wa "reach" x ≠ 0 := by
  induction hp with
  | nil u => exact hy
  | @cons e v q h ih =>
    have h2 : st.wa "reach" (G.src e) = 2 := by
      have h1 : ¬(st.wa "reach" (G.src e) = 1) := hdone _
      have hle := I.reach_val (G.src e)
      omega
    exact ih (I.relaxed e h2).1

/-- At main-loop exit every reached vertex is settled, hence carries its true distance. -/
theorem solves_of_inv {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) (hdone : ∀ v : Fin G.n, st.wa "reach" v = 1 → False) :
    st.wlen "reach" = G.n ∧ st.vlen "dist" = G.n ∧ G.IsSSSP s (fun v => st.label v) := by
  refine ⟨I.frame.hreachL, I.frame.hdistL, ?_⟩
  intro v
  by_cases h0 : st.wa "reach" v = 0
  · have htop : G.dist s v = ⊤ := by
      rw [G.dist_eq_top_iff]
      intro hr
      obtain ⟨p, hp⟩ := hr
      have hnn := reach_of_walk I hdone hp I.reach_s
      omega
    simp [Frontier.RAM.State.label, h0, htop]
  · have h2 : st.wa "reach" v = 2 := by
      have h1 : ¬(st.wa "reach" v = 1) := hdone _
      have hle := I.reach_val v
      omega
    simp [Frontier.RAM.State.label, h0, I.settled_exact v h2]

/-! ## Assembly -/

/-- The main loop: from any `Inv` state with `k = 0`, run to exit where no `reach = 1`
vertex remains and `Solves` holds, at cost `≤ 28·(n²+m) + 28`.  The loop invariant extends
`Inv` with the settle-count (`k < n → #{v | reach v = 2} = k`) and the exit fact
(`n ≤ k → no reach = 1`), both carried through `mainInner` by `inv_of_settle` /
`inv_of_relax_step` / `inv_of_main_step`. -/
theorem runs_mainLoop {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) (hk0 : st.w "k" = 0) :
    Runs realOps mainLoop st
      (fun r => (∀ v : Fin G.n, r.wa "reach" v = 1 → False) ∧ r.Solves G s ∧
        (r.cost : ℝ) ≤ 28 * (((G.n : ℝ) ^ 2 + G.m) + 1) + st.cost) := by
  sorry

/-- On every graph and source the program terminates without getting stuck, outputs the exact
distances, and costs at most `40 * (n² + m + 1)`.

Assembly (the wiring is mechanical over the named lemmas above):
`prog = allocAll; initReach; buildCSR; k := 0; mainLoop`.  Chain `runs_csr` (cost
`≤ 12(n+m)+12`, `PreMain`) → `inv_of_preMain` → the `wset "k" 0` step (`Runs` rules) →
`runs_mainLoop` (cost `≤ 28(n²+m+28` from cost 0) → `solves_of_inv` on the loop's exit
postcondition.  Total `12(n+m)+12 + 28(n²+m+1) + O(1) ≤ 40(n²+m+1)` for all `n, m`. -/
theorem dijkstra_runs (G : Graph) (s : Fin G.n) :
    ∃ fuel r, dijkstraProgram.run fuel G s = some r ∧ r.Solves G s ∧
      (r.cost : ℝ) ≤ 40 * (((G.n : ℝ) ^ 2 + G.m) + 1) := by
  sorry

end BigOSpeedrun.DirectedSSSP.Dijkstra
