import Submission.SsspStatement
import Submission.Bridge

/-!
The `n^2 ; n^2` row for the Big O Speedrun directed shortest paths race: one uniform program
(dispatching on `m`: the fork's verified Bellman–Ford for `m < n`, array-scan Dijkstra
otherwise) is exact on every graph, runs within `C·n²` at `m ≤ n²` for `n ≥ 16`, and within
`C·(n+1)(m+1)` on every graph.
-/

theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((2 : ℚ) / 1) ((0 : ℚ) / 1) ((2 : ℚ) / 1) ((0 : ℚ) / 1) ((0 : ℚ) / 1) :=
  BigOSpeedrun.DirectedSSSP.Bridge.dispatch_bound
