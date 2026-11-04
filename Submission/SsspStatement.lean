import Frontier.CostModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Trusted target for the Big O Speedrun directed shortest paths race,
https://bigospeedrun.com/directed-sssp.

The computation model (`Frontier.Graph`, `Frontier.RAM.Program`, `Program.run`,
`State.Solves`, `State.cost`: a deep-embedded word RAM with comparison-addition
reals) is not in this repository. The verifier stages it from
https://github.com/bigospeedrun/c-hd-proof (a fork of spicylemonade/c-hd-proof),
directory formal/lean, at the commit pinned in profiles/direct.json
(solution_dependencies). This file adds the race statement only and assumes no
estimate or proof of any bound.

A row says: "on graphs with at most D(n) edges, the time is O(T(n))", with
D(n) = n^a · ⌊⌊log₂ n⌋^b⌋ and T(n) = n^a' · (log n)^b' · (log log n)^c'. The
controller substitutes five exact rationals a, b, a', b', c'.
-/

namespace BigOSpeedrun.DirectedSSSP

open Frontier Frontier.RAM

/-- The edge cap `D(n) = n^a · ⌊⌊log₂ n⌋^b⌋`, with both floors exact
(`Nat.log 2 n` is `⌊log₂ n⌋`). At `a = 1`, `b = 3/4` this is the C-HD threshold. -/
noncomputable def Cap (a b : ℚ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (a : ℝ) * (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ : ℝ)

/-- A graph with `n` vertices and `m` edges is in the race's density range. -/
def Sparse (a b : ℚ) (n m : ℕ) : Prop := (m : ℝ) ≤ Cap a b n

/-- The time function `T(n) = n^a · (log n)^b · (log log n)^c` (natural logarithms). -/
noncomputable def Time (a b c : ℚ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (a : ℝ) * Real.log n ^ (b : ℝ) * Real.log (Real.log n) ^ (c : ℝ)

/-- One run of `P` on `(G, s)` terminates with the exact distances and costs at most `budget`. -/
def CorrectWithin (P : Program) (G : Graph) (s : Fin G.n) (budget : ℝ) : Prop :=
  ∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s ∧ (r.cost : ℝ) ≤ budget

/-- One uniform program, exact on every graph and source. On every graph with at
least `N` vertices and at most `D(n)` edges it runs within `C · T(n)`; on every
graph it runs within `C · (n+1) · (m+1)` (a polynomial fallback, as Bellman-Ford).
`P.Exact` follows from the fallback clause; it stays for readability. -/
def Bound (a b a' b' c' : ℚ) : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 16 ≤ N ∧
    (∀ (G : Graph) (s : Fin G.n), N ≤ G.n → Sparse a b G.n G.m →
      CorrectWithin P G s (C * Time a' b' c' G.n)) ∧
    (∀ (G : Graph) (s : Fin G.n),
      CorrectWithin P G s (C * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)))

end BigOSpeedrun.DirectedSSSP
