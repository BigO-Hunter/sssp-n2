import Frontier.RAMWitness
import Frontier.RAMLogic

/-!
# Submission.Dijkstra — array-scan Dijkstra with a counting-sort CSR build (the n^2 ; n^2 row)

Greenfield program for the Big O Speedrun directed-sssp `n^2 ; n^2` row: on the dense branch
(`n ≤ m`) this program computes exact SSSP in `O(n^2 + m)` on the Frontier comparison-addition
word RAM.  The sparse branch is the fork's verified Bellman–Ford (`Frontier.RAM.BF.bfProgram`),
spliced in `Submission.Bridge`.

Design (the proof-relevant points):

* Phase 1 builds a CSR adjacency `idx` grouped by `src` with counting sort (`head`/`pos`/`idx`),
  `O(n + m)` statements.
* Phase 2 is array-scan Dijkstra: repeat — scan `0..n-1` for the minimum `dist` among
  `reach = 1` (reached, unsettled); if none, stop; else mark it `reach = 2` (settled, frozen)
  and relax its CSR out-edge segment.  At most `n` settlements; each scan `O(n)`, each edge
  relaxed at most once across all settlements, total `O(n^2 + m)`.
* Output contract: `reach[v] = 0` iff `v` is unreachable; otherwise `dist[v]` is the exact
  distance.  Settled vertices carry `reach = 2` (nonzero, so their label reads `dist`).
* Settled labels are frozen (relax skips `reach = 2` targets), so the classic exchange
  argument at settlement — `dist[best] = G.dist s best` via the first unsettled vertex on a
  shortest path — is all the correctness the output needs.  The counterexample that forbids
  arbitrary extraction order (settling `a` before `b` on `s→a = 5, s→b = 1, b→a = 1` freezes
  `5` and skips `b→a`) is excluded by the min-scan.
-/

namespace BigOSpeedrun.DirectedSSSP.Dijkstra

open scoped ENNReal NNReal
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

/-! ## Invariants

All invariants are history-free: `relaxed` (every edge out of a settled vertex bounds its
target) absorbs the skipped-relaxation case, because a settled target already carries its
true distance (`settledExact`) and the triangle inequality gives the bound.
-/

open Frontier.RAM.BF (Frame)

/-- Out-degree source-counts: `cnt v = |{e < m | src e = v}|`. -/
noncomputable def cnt (G : Graph) (v : ℕ) : ℕ :=
  ((Finset.univ.filter (fun e : Fin G.m => (G.src e : ℕ) < v)).card)

/-- Counting-sort placement rank of edge `e` among same-source edges. -/
noncomputable def rank (G : Graph) (e : Fin G.m) : ℕ :=
  (Finset.univ.filter (fun e' : Fin G.m => G.src e' = G.src e ∧ (e' : ℕ) < (e : ℕ))).card

/-- The CSR facts established by the counting-sort build. -/
structure CSRPart (G : Graph) (st : State ℝ≥0) : Prop where
  hheadL : st.wlen "head" = G.n + 1
  hposL : st.wlen "pos" = G.n
  hidxL : st.wlen "idx" = G.m
  head_range : ∀ v, v ≤ G.n → st.wa "head" v ≤ G.m
  head_mono : ∀ i j, i ≤ j → j ≤ G.n → st.wa "head" i ≤ st.wa "head" j
  head_of_cnt : ∀ v, v ≤ G.n → st.wa "head" v = cnt G v
  csr_seg : ∀ (v : Fin G.n) q, st.wa "head" v ≤ q → q < st.wa "head" ((v : ℕ) + 1) →
    q < G.m ∧ ∀ hq : q < G.m, G.src ⟨q, hq⟩ = v
  csr_cover : ∀ e : Fin G.m, ∃ q, st.wa "head" (G.src e) ≤ q ∧
    q < st.wa "head" ((G.src e : ℕ) + 1) ∧ st.wa "idx" q = e

/-- The state right before the main loop: the CSR is built, `reach ∈ {0, 1}` with only `s`
reached, `dist = 0` everywhere. -/
structure PreMain (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  frame : Frontier.RAM.BF.Frame G st
  csr : CSRPart G st
  reach_low : ∀ v : Fin G.n, st.wa "reach" v ≤ 1
  reach_s : st.wa "reach" s = 1
  reach_zero : ∀ v : Fin G.n, v ≠ s → st.wa "reach" v = 0
  dist_zero : ∀ v : Fin G.n, st.va "dist" v = 0

/-- The CSR and semantic invariant of the main loop.  History-free: `relaxed` absorbs
skipped relaxations into settled vertices via `settledExact` + the triangle inequality. -/
structure Inv (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  frame : Frontier.RAM.BF.Frame G st
  csr : CSRPart G st
  reach_val : ∀ v : Fin G.n, st.wa "reach" v ≤ 2
  reach_s : st.wa "reach" s ≠ 0
  walk_sound : ∀ v : Fin G.n, st.wa "reach" v ≠ 0 →
    ∃ p, G.IsWalk s v p ∧ G.len p = st.va "dist" v
  settled_exact : ∀ v : Fin G.n, st.wa "reach" v = 2 →
    ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) = G.dist s v
  relaxed : ∀ e : Fin G.m, st.wa "reach" (G.src e) = 2 →
    st.wa "reach" (G.dst e) ≠ 0 ∧
    (st.va "dist" (G.dst e) : ℝ≥0) ≤ st.va "dist" (G.src e) + G.w e
  dist_s_zero : st.va "dist" s = 0

/-- A freshly built state satisfies the main-loop invariant. -/
theorem inv_of_preMain {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : PreMain G s st) :
    Inv G s st := by
  refine ⟨h.frame, h.csr, fun v => Nat.le_trans (h.reach_low v) (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.reach_s]; simp
  · intro v hv
    by_cases hs : v = s
    · subst hs
      exact ⟨[], Graph.IsWalk.nil _, by simp [h.dist_zero]⟩
    · rw [h.reach_zero v hs] at hv
      exact absurd hv (by simp)
  · intro v hv
    have hle : st.wa "reach" v ≤ 1 := h.reach_low v
    omega
  · intro e he
    have hle : st.wa "reach" (G.src e) ≤ 1 := h.reach_low _
    omega
  · exact h.dist_zero s

end BigOSpeedrun.DirectedSSSP.Dijkstra
