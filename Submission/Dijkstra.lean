import Frontier.RAMWitness
import Frontier.RAMLogic

/-!
# Submission.Dijkstra — array-scan Dijkstra with a counting-sort CSR build (the n^2 ; n^2 row)

Greenfield program for the Big O Speedrun directed-sssp `n^2 ; n^2` row: on the dense branch
(`n ≤ m`) this program computes exact SSSP in `O(n^2 + m)` on the Frontier comparison-addition
word RAM.  The sparse branch is the fork's verified Bellman–Ford (`Frontier.RAM.BF.bfProgram`),
spliced in `Submission.Bridge`.

Design (the proof-relevant points):

* `m` is dispatched by the caller; this program assumes nothing about `m` but is only *used*
  when `n ≤ m`.  It never gets stuck on any input.
* Phase 1 builds a CSR adjacency `idx` grouped by `src` with counting sort (`head`/`pos`/`idx`),
  `O(n + m)` statements.
* Phase 2 is array-scan Dijkstra: repeat — scan `0..n-1` for the minimum `dist` among
  `reach = 1` (reached, unsettled); if none, stop; else mark it `reach = 2` (settled, frozen)
  and relax its CSR out-edge segment.  At most `n` settlements; each scan `O(n)`, each edge
  relaxed exactly once across all settlements, total `O(n^2 + m)`.
* Output contract: `reach[v] = 0` iff `v` is unreachable; otherwise `dist[v]` is the exact
  distance.  Settled vertices carry `reach = 2` (nonzero, so their label reads `dist`).

Correctness shape: at every settlement the classic exchange argument gives
`dist[best] = G.dist s best` (first unsettled vertex `x` on a shortest path to `best` has
`dist[x] ≤ len (prefix to x) ≤ dist[best] ≤ dist[x]`; the min-scan gives `dist[best] ≤ dist[x]`),
skipped relaxations into settled vertices cannot break anything because settled labels are
frozen (the program never writes `reach = 2` vertices), and loop exhaustion leaves every
reached vertex settled.  Unreached vertices decode to `⊤ = G.dist`.

The counterexample that forbids arbitrary extraction order (recorded in the task riders):
with `s→a = 5, s→b = 1, b→a = 1`, settling `a` before `b` freezes `dist[a] = 5` and skips
`b→a`; min-extraction prevents this.
-/

namespace BigOSpeedrun.DirectedSSSP.Dijkstra

open Frontier Frontier.RAM
open WExpr Stmt

/-! ## Program text -/

/-- `dist[u] + w[e]`, the relax candidate. -/
def relaxVal : VExpr := .add (.load "dist" (.var "u")) (.load "w" (.var "e"))

/-- Phase 1a: count out-degrees into `head`. -/
def countBody : Stmt :=
  seq (wset "p" (.load "src" (.var "e")))
    (seq (wstore "head" (.var "p") (.add (.load "head" (.var "p")) (.lit 1)))
      (wset "e" (.add (.var "e") (.lit 1))))

def countLoop : Stmt := .while (.lt (.var "e") (.var "m")) countBody

/-- Phase 1b: exclusive prefix sums — `head[v]` becomes the segment start of `v`;
the running total lands in `k`, later stored to `head[n]`. -/
def prefixBody : Stmt :=
  seq (wset "p" (.load "head" (.var "i")))
    (seq (wstore "head" (.var "i") (.var "k"))
      (seq (wset "k" (.add (.var "k") (.var "p")))
        (wset "i" (.add (.var "i") (.lit 1)))))

def prefixLoop : Stmt := .while (.lt (.var "i") (.var "n")) prefixBody

/-- Phase 1c: copy segment starts into the working cursor `pos`. -/
def copyBody : Stmt :=
  seq (wstore "pos" (.var "i") (.load "head" (.var "i")))
    (wset "i" (.add (.var "i") (.lit 1)))

def copyLoop : Stmt := .while (.lt (.var "i") (.var "n")) copyBody

/-- Phase 1d: place every edge index into its `src` segment of `idx`. -/
def placeBody : Stmt :=
  seq (wset "p" (.load "src" (.var "e")))
    (seq (wset "q" (.load "pos" (.var "p")))
      (seq (wstore "idx" (.var "q") (.var "e"))
        (seq (wstore "pos" (.var "p") (.add (.var "q") (.lit 1)))
          (wset "e" (.add (.var "e") (.lit 1))))))

def placeLoop : Stmt := .while (.lt (.var "e") (.var "m")) placeBody

/-- Phase 2a: the update decision for one edge `(u, v)`: settled `v` is skipped, unreached
`v` is written, reached-unsettled `v` is written only when strictly improved. -/
def relaxInner : Stmt :=
  ite (.eq (.load "reach" (.var "v")) (.lit 2)) skip
    (ite (.eq (.load "reach" (.var "v")) (.lit 0))
      (seq (vstore "dist" (.var "v") relaxVal) (wstore "reach" (.var "v") (.lit 1)))
      (seq (vle "b" (.load "dist" (.var "v")) relaxVal)
        (ite (.var "b") skip (vstore "dist" (.var "v") relaxVal))))

/-- One edge of the relax sweep over `u`'s CSR segment. -/
def relaxBody : Stmt :=
  seq (wset "e" (.load "idx" (.var "j")))
    (seq (wset "v" (.load "dst" (.var "e")))
      (seq relaxInner (wset "j" (.add (.var "j") (.lit 1)))))

def relaxLoop : Stmt := .while (.lt (.var "j") (.var "jend")) relaxBody

/-- Phase 2b: settle the scan winner `best` and relax its out-edges. -/
def settleBody : Stmt :=
  seq (wset "u" (.var "best"))
    (seq (wstore "reach" (.var "u") (.lit 2))
      (seq (wset "j" (.load "head" (.var "u")))
        (seq (wset "jend" (.load "head" (.add (.var "u") (.lit 1)))) relaxLoop)))

/-- Phase 2c: one scan step — keep the minimum `dist` among `reach = 1` vertices;
`best = n` is the "none found" sentinel (`n` is never a valid vertex). -/
def minInner : Stmt :=
  ite (.eq (.load "reach" (.var "i")) (.lit 1))
    (ite (.eq (.var "best") (.var "n"))
      (wset "best" (.var "i"))
      (seq (vle "c" (.load "dist" (.var "i")) (.load "dist" (.var "best")))
        (ite (.var "c") (wset "best" (.var "i")) skip)))
    skip

def minBody : Stmt := seq minInner (wset "i" (.add (.var "i") (.lit 1)))

def minLoop : Stmt := .while (.lt (.var "i") (.var "n")) minBody

/-- One main iteration: find the min, settle it or stop (`k := n` forces the loop exit). -/
def mainInner : Stmt :=
  ite (.eq (.var "best") (.var "n"))
    (wset "k" (.var "n"))
    (seq settleBody (wset "k" (.add (.var "k") (.lit 1))))

def mainBody : Stmt :=
  seq (wset "best" (.var "n")) (seq (wset "i" (.lit 0)) (seq minLoop mainInner))

def mainLoop : Stmt := .while (.lt (.var "k") (.var "n")) mainBody

/-- Allocations: CSR arrays and the two output arrays (all zero-initialised). -/
def allocAll : Stmt :=
  seq (walloc "head" (.add (.var "n") (.lit 1)))
    (seq (walloc "pos" (.var "n"))
      (seq (walloc "idx" (.var "m"))
        (seq (valloc "dist" (.var "n"))
          (walloc "reach" (.var "n")))))

/-- Seed the source and the first edge cursor. -/
def initReach : Stmt :=
  seq (wstore "reach" (.var "s") (.lit 1)) (seq (wset "e" (.lit 0)) countLoop)

/-- CSR bookkeeping: prefix sums, `head[n] = k`, cursor copy, placement. -/
def buildCSR : Stmt :=
  seq (wset "i" (.lit 0))
    (seq (wset "k" (.lit 0))
      (seq prefixLoop
        (seq (wstore "head" (.var "n") (.var "k"))
          (seq (wset "i" (.lit 0))
            (seq copyLoop (seq (wset "e" (.lit 0)) placeLoop))))))

/-- The full array-scan Dijkstra program: CSR build, then settle-and-relax to exhaustion. -/
def prog : Stmt :=
  seq allocAll (seq initReach (seq buildCSR (seq (wset "k" (.lit 0)) mainLoop)))

/-- The dense-branch program (words below `n + m + 2`, like `bfProgram`). -/
def dijkstraProgram : Program := { body := prog, wordExp := 0 }

/-! ## Semantic statement (filled by the proof) -/

/-- On every graph and source the program terminates without getting stuck, outputs the exact
distances, and costs `K * (n^2 + m) + K * (n + m) + K` for a small constant `K`. -/
theorem dijkstra_runs (G : Graph) (s : Fin G.n) :
    ∃ fuel r, dijkstraProgram.run fuel G s = some r ∧ r.Solves G s ∧
      (r.cost : ℝ) ≤ 40 * (((G.n : ℝ) ^ 2 + G.m) + 1) := by
  sorry

end BigOSpeedrun.DirectedSSSP.Dijkstra
