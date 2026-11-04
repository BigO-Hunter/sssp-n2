import Submission.Dijkstra

/-!
# Submission.DijkstraCSR — establishment of the CSR invariant by the counting-sort build

`buildCSR` (count / prefix / copy / place loops) establishes `CSRPart` and preserves the
input frame, ending with `PreMain`.  Proved here so the main loop in
`Submission.DijkstraProof` can assume a finished CSR.

The counting invariants (designed, proof open):
* countLoop (cursor `e`): `∀ v ≤ n, head v = |{e' : Fin m | src e' = v ∧ e' < e}|`.
* prefixLoop (cursor `i`, running total `k`): `k = cnt G i ∧ (∀ v ≤ i, head v = cnt G v) ∧
  (∀ v, i ≤ v → v ≤ n → head v = |{e' : Fin m | src e' = v}|)`, using
  `cnt G (v+1) = cnt G v + |{e' | src e' = v}|`; then `head[n] := k`.
* copyLoop: `∀ v < i, pos v = head v`.
* placeLoop (cursor `e`): `pos v = head v + |{e' < e | src e' = v}|`, placement
  `idx[head (src e') + rank G e'] = e'` for `e' < e`, and positional soundness
  `head v ≤ q < pos v → idx q < e ∧ src (idx q) = v ∧ q = head v + rank (idx q)`.

From these: `head_of_cnt`, `head_mono`, `head_range`, `csr_seg` (soundness), `csr_cover`
(placement position `q = head (src e) + rank G e`).
-/

namespace BigOSpeedrun.DirectedSSSP.Dijkstra

open scoped ENNReal NNReal
open Frontier Frontier.RAM
open WExpr Stmt

/-- The counting-sort build establishes `PreMain` at cost `≤ 12·(n+m) + 12`. -/
theorem runs_csr (G : Graph) (s : Fin G.n) :
    Runs realOps (seq allocAll (seq initReach buildCSR)) (initState dijkstraProgram G s)
      (fun st => PreMain G s st ∧ (st.cost : ℝ) ≤ 12 * ((G.n : ℝ) + G.m) + 12) := by
  sorry

end BigOSpeedrun.DirectedSSSP.Dijkstra
