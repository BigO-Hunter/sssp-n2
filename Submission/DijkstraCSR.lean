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
open Frontier Frontier.RAM Graph
open WExpr Stmt

/-! ## Counting-sort combinatorics -/

theorem card_filter_eq_sum {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ a ∈ s, if p a then (1 : ℕ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp

/-- Number of edges `e' < e` with source `v` (counting-sort occupancy of `v`'s segment). -/
noncomputable def srcCnt (G : Graph) (v : ℕ) (e : ℕ) : ℕ :=
  (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) = v ∧ (e' : ℕ) < e)).card

theorem srcCnt_sum (G : Graph) (v e : ℕ) :
    srcCnt G v e = ∑ e' : Fin G.m, if (G.src e' : ℕ) = v ∧ (e' : ℕ) < e then 1 else 0 := by
  rw [srcCnt, card_filter_eq_sum]

theorem srcCnt_zero (G : Graph) (v : ℕ) : srcCnt G v 0 = 0 := by
  rw [srcCnt]
  exact Finset.card_eq_zero.mpr (by ext e'; simp)

theorem srcCnt_succ {G : Graph} {v e : ℕ} (he : e < G.m) :
    srcCnt G v (e + 1) = srcCnt G v e + if (G.src ⟨e, he⟩ : ℕ) = v then 1 else 0 := by
  rw [srcCnt_sum, srcCnt_sum]
  have hsplit : ∀ e' : Fin G.m,
      (if (G.src e' : ℕ) = v ∧ (e' : ℕ) < e + 1 then 1 else 0) =
      (if (G.src e' : ℕ) = v ∧ (e' : ℕ) < e then 1 else 0) +
      (if (G.src e' : ℕ) = v ∧ (e' : ℕ) = e then 1 else 0) := by
    intro e'
    by_cases h1 : (G.src e' : ℕ) = v
    · by_cases h2 : (e' : ℕ) < e
      · have h3 : (e' : ℕ) ≠ e := by omega
        have h4 : (e' : ℕ) < e + 1 := by omega
        simp [h1, h2, h3, h4]
      · by_cases h3 : (e' : ℕ) = e
        · have h4 : (e' : ℕ) < e + 1 := by omega
          simp [h1, h2, h3, h4]
        · have h4 : ¬ ((e' : ℕ) < e + 1) := by omega
          simp [h1, h2, h3, h4]
    · simp [h1]
  have hsum1 : (∑ e' : Fin G.m,
      (if (G.src e' : ℕ) = v ∧ (e' : ℕ) < e + 1 then 1 else 0)) =
      (∑ e' : Fin G.m,
        (if (G.src e' : ℕ) = v ∧ (e' : ℕ) < e then 1 else 0)) +
      (∑ e' : Fin G.m, (if (G.src e' : ℕ) = v ∧ (e' : ℕ) = e then 1 else 0)) := by
    conv_lhs => simp only [hsplit]
    rw [Finset.sum_add_distrib]
  rw [hsum1]
  congr 1
  rw [Fintype.sum_eq_single (⟨e, he⟩ : Fin G.m)]
  · simp
  · intro x hx
    have hne : ¬ ((G.src x : ℕ) = v ∧ (x : ℕ) = e) := fun hh => hx (Fin.ext hh.2)
    simp [hne]

theorem srcCnt_full (G : Graph) (v : ℕ) : srcCnt G v G.m =
    (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) = v)).card := by
  apply congrArg Finset.card
  ext e'
  simp

theorem srcCnt_le (G : Graph) (v e : ℕ) : srcCnt G v e ≤ G.m := by
  rw [srcCnt_sum]
  calc (∑ e' : Fin G.m, if (G.src e' : ℕ) = v ∧ (e' : ℕ) < e then 1 else 0)
      ≤ ∑ e' : Fin G.m, (1 : ℕ) := Finset.sum_le_sum fun x _ => by split_ifs <;> omega
    _ = G.m := by simp

theorem srcCnt_mono (G : Graph) (v : ℕ) {e e' : ℕ} (h : e ≤ e') :
    srcCnt G v e ≤ srcCnt G v e' := by
  rw [srcCnt_sum, srcCnt_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hh : (G.src x : ℕ) = v
  · by_cases h2 : (x : ℕ) < e
    · have h2' : (x : ℕ) < e' := Nat.lt_of_lt_of_le h2 h
      simp [hh, h2, h2']
    · by_cases h3 : (x : ℕ) < e'
      · simp [hh, h2, h3]
      · simp [hh, h2, h3]
  · simp [hh]

/-- `rank` (placement order within a source class) is the prefix count at the edge. -/
theorem rank_eq (G : Graph) (e : Fin G.m) :
    rank G e = srcCnt G (G.src e) (e : ℕ) := by
  unfold rank srcCnt
  apply congrArg Finset.card
  ext e'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Fin.ext h1, h2⟩

/-- `cnt` increments by the source class size. -/
theorem cnt_succ (G : Graph) (v : ℕ) :
    cnt G (v + 1) = cnt G v + (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) = v)).card := by
  have hsplit : ∀ e' : Fin G.m,
      ((G.src e' : ℕ) < v + 1) ↔ ((G.src e' : ℕ) < v ∨ (G.src e' : ℕ) = v) := by
    intro e'
    constructor
    · intro h
      by_cases hh : (G.src e' : ℕ) < v
      · exact Or.inl hh
      · exact Or.inr (by omega)
    · rintro (h | h)
      · omega
      · omega
  have h1 : (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) < v + 1)) =
      (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) < v)) ∪
      (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) = v)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rw [hsplit]
  have hdisj : Disjoint
      (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) < v))
      (Finset.univ.filter (fun e' : Fin G.m => (G.src e' : ℕ) = v)) := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    omega
  rw [cnt, cnt, h1, Finset.card_union_of_disjoint hdisj, Nat.add_comm]

theorem cnt_mono (G : Graph) {v w : ℕ} (h : v ≤ w) : cnt G v ≤ cnt G w := by
  unfold cnt
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact Nat.lt_of_lt_of_le hx h

theorem cnt_le (G : Graph) (v : ℕ) : cnt G v ≤ G.m := by
  unfold cnt
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- The counting-sort build establishes `PreMain` at cost `≤ 12·(n+m) + 17`.

True per-phase counts against the cost model (`1` per statement and test, `alloc k = k+1`):
`allocAll = 4n+m+6` (five allocs of sizes `n+1, n, m, n, n`), `initReach = 4m+3`
(`wstore; wset; countLoop` = `2 + m·(1+3) + 1`), `buildCSR = 8n+6m+8`
(`wset;wset; prefixLoop; wstore; wset; copyLoop; wset; placeLoop` = `2 + (5n+1) + 1 + 1 +
(3n+1) + 1 + (6m+1)`).  Total `12n + 11m + 17`.  BOTH earlier claimed bounds are false at
`n = 1, m = 0` (true cost `29`): the original `12(n+m)+12` and the session-2 "correction"
`10(n+m)+17` (its claimed true count `10n+10m+17` dropped the `n+1` in `walloc "head"`,
one loop exit test, and one prologue `wset`). -/
theorem runs_allocAll (G : Graph) (s : Fin G.n) :
    Runs realOps allocAll (initState dijkstraProgram G s) (fun S1 =>
      Frontier.RAM.BF.Frame G S1 ∧ S1.wlen "head" = G.n + 1 ∧ S1.wlen "pos" = G.n ∧
        S1.wlen "idx" = G.m ∧ (∀ j, S1.wa "head" j = 0) ∧ (∀ j, S1.wa "pos" j = 0) ∧
        (∀ j, S1.wa "idx" j = 0) ∧ (∀ j, S1.va "dist" j = 0) ∧ S1.w "s" = (s : ℕ) ∧ (∀ j, S1.wa "reach" j = 0) ∧
        S1.cost = 4 * G.n + G.m + 6) := by
  have hn : 0 < G.n := by have := s.isLt; omega
  have h0 := Frontier.RAM.BF.inputFrame_initState dijkstraProgram s
  have h0n := h0.hn
  have h0m := h0.hm
  have h0cap := h0.hcap
  refine runs_seq (runs_walloc (k := G.n + 1)
    (by rw [evalW_add_of (by rw [evalW_var, h0n]) (evalW_lit_of (by omega))
      (by omega)]) ?_)
  refine runs_seq (runs_walloc (k := G.n)
    (by simp [evalW_var, State.allocW, State.charge, h0n]) ?_)
  refine runs_seq (runs_walloc (k := G.m)
    (by simp [evalW_var, State.allocW, State.charge, h0n, h0m]) ?_)
  refine runs_seq (runs_valloc (k := G.n)
    (by simp [evalW_var, State.allocW, State.charge, h0n, h0m]) ?_)
  refine runs_walloc (k := G.n)
    (by simp [evalW_var, State.allocW, State.allocV, State.charge, h0n, h0m]) ?_
  set S5 := ((((((initState dijkstraProgram G s).allocW "head" (G.n + 1)).charge (G.n + 1 +
      1)).allocW "pos" G.n).charge (G.n + 1)).allocW "idx" G.m).charge (G.m + 1) |>.allocV
      "dist" G.n realOps.zero |>.charge (G.n + 1) |>.allocW "reach" G.n |>.charge (G.n + 1)
    with hS5
  have h5cap : G.n + G.m + 2 ≤ S5.cap := by
    simp only [hS5, State.allocW, State.allocV, State.charge]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hS5, State.allocW, State.allocV, State.charge, h0.hn]
    · simp [hS5, State.allocW, State.allocV, State.charge, h0.hm]
    · simp only [hS5, State.allocW, State.allocV, State.charge]; omega
    · intro j h; simp [hS5, State.allocW, State.allocV, State.charge, h0.hsrc j h]
    · intro j h; simp [hS5, State.allocW, State.allocV, State.charge, h0.hdst j h]
    · intro j h; simp [hS5, State.allocW, State.allocV, State.charge, h0.hw j h]
    · simp [hS5, State.allocW, State.allocV, State.charge, h0.hsrcL]
    · simp [hS5, State.allocW, State.allocV, State.charge, h0.hdstL]
    · simp [hS5, State.allocW, State.allocV, State.charge, h0.hwL]
    · simp [hS5, State.allocW, State.allocV, State.charge]
    · simp [hS5, State.allocW, State.allocV, State.charge]
  · simp [hS5, State.allocW, State.allocV, State.charge]
  · simp [hS5, State.allocW, State.allocV, State.charge]
  · simp [hS5, State.allocW, State.allocV, State.charge]
  · intro j; simp [hS5, State.allocW, State.allocV, State.charge]
  · intro j; simp [hS5, State.allocW, State.allocV, State.charge]
  · intro j; simp [hS5, State.allocW, State.allocV, State.charge]
  · intro j; simp [hS5, State.allocW, State.allocV, State.charge, realOps]
  · simp [hS5, State.allocW, State.allocV, State.charge, initState]
  · intro j; simp [hS5, State.allocW, State.allocV, State.charge]
  · simp [hS5, State.allocW, State.allocV, State.charge, initState]
    omega

/-! ## Rank strictness (no cardinality argument needed: proper-subset cards) -/

/-- An edge's rank is strictly below its full source-class size. -/
theorem rank_lt (G : Graph) (e : Fin G.m) :
    rank G e < srcCnt G (G.src e) G.m := by
  rw [rank_eq]
  have hone : srcCnt G (G.src e) ((e : ℕ) + 1) = srcCnt G (G.src e) (e : ℕ) + 1 := by
    rw [srcCnt_succ e.isLt]
    simp
  have hmono : srcCnt G (G.src e) ((e : ℕ) + 1) ≤ srcCnt G (G.src e) G.m :=
    srcCnt_mono (G := G) (v := (G.src e : ℕ)) (e := (e : ℕ) + 1) (e' := G.m)
      (by have := e.isLt; omega)
  omega

/-- Same-source ranks strictly follow edge order (hence `rank` is injective on a class). -/
theorem rank_lt_of_lt {G : Graph} {e₁ e₂ : Fin G.m}
    (hs : G.src e₁ = G.src e₂) (h : (e₁ : ℕ) < (e₂ : ℕ)) : rank G e₁ < rank G e₂ := by
  have h1 : rank G e₁ = srcCnt G (G.src e₂) (e₁ : ℕ) := by rw [rank_eq, hs]
  have h2 : rank G e₂ = srcCnt G (G.src e₂) (e₂ : ℕ) := rank_eq G e₂
  rw [h2, h1]
  have hone : srcCnt G (G.src e₂) ((e₁ : ℕ) + 1) = srcCnt G (G.src e₂) (e₁ : ℕ) + 1 := by
    rw [srcCnt_succ e₁.isLt]
    simp [hs]
  have hmono : srcCnt G (G.src e₂) ((e₁ : ℕ) + 1) ≤ srcCnt G (G.src e₂) (e₂ : ℕ) :=
    srcCnt_mono (G := G) (v := (G.src e₂ : ℕ)) (e := (e₁ : ℕ) + 1) (e' := (e₂ : ℕ)) (by omega)
  omega

/-- Prefix-count step, in `srcCnt` form. -/
theorem cnt_step (G : Graph) (v : ℕ) : cnt G v + srcCnt G v G.m = cnt G (v + 1) := by
  rw [cnt_succ, ← srcCnt_full]

theorem cnt_top (G : Graph) : cnt G G.n = G.m := by
  have h : (Finset.univ.filter (fun e : Fin G.m => (G.src e : ℕ) < G.n)) = Finset.univ := by
    ext e
    simpa [Finset.mem_filter] using (G.src e).isLt
  unfold cnt
  rw [h]
  simp

theorem cnt_zero (G : Graph) : cnt G 0 = 0 := by
  unfold cnt
  simp

/-! ## Facts carried unchanged from `runs_allocAll` through the build -/

/-- The part of the `allocAll` postcondition that every later phase preserves: the frame,
the three CSR array lengths, zero-initialised `dist`, and `reach` seeded at `s` only. -/
structure AllocFacts (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  frame : Frontier.RAM.BF.Frame G st
  hheadL : st.wlen "head" = G.n + 1
  hposL : st.wlen "pos" = G.n
  hidxL : st.wlen "idx" = G.m
  hdist0 : ∀ j, st.va "dist" j = 0
  hreachS : st.wa "reach" (s : ℕ) = 1
  hreach0 : ∀ v : ℕ, v < G.n → v ≠ (s : ℕ) → st.wa "reach" v = 0
  hws : st.w "s" = (s : ℕ)

/-- `Frame` survives stores into any array other than the two input arrays. -/
theorem frame_storeW_arr {G : Graph} {st : State ℝ≥0} (h : Frontier.RAM.BF.Frame G st)
    {arr : String} (h1 : arr ≠ "src") (h2 : arr ≠ "dst") (j a : ℕ) :
    Frontier.RAM.BF.Frame G (st.storeW arr j a) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := h
  refine ⟨f1, f2, f3, ?_, ?_, f6, f7, f8, f9, f10, f11⟩
  · intro j' hj'; simp [State.storeW, Ne.symm h1, f4 j' hj']
  · intro j' hj'; simp [State.storeW, Ne.symm h2, f5 j' hj']

theorem AllocFacts.setW {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : AllocFacts G s st)
    (x : String) (hxn : x ≠ "n") (hxm : x ≠ "m") (hxs : x ≠ "s") (a : ℕ) :
    AllocFacts G s (st.setW x a) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h
  refine ⟨f1.setW hxn hxm a, f2, f3, f4, f5, f6, f7, ?_⟩
  simp [State.setW, Ne.symm hxs, f8]

theorem AllocFacts.charge {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : AllocFacts G s st)
    (k : ℕ) : AllocFacts G s (st.charge k) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h
  exact ⟨f1.charge k, f2, f3, f4, f5, f6, f7, f8⟩

theorem AllocFacts.storeW {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : AllocFacts G s st)
    (arr : String) (h1 : arr ≠ "src") (h2 : arr ≠ "dst") (h3 : arr ≠ "reach") (j a : ℕ) :
    AllocFacts G s (st.storeW arr j a) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h
  refine ⟨frame_storeW_arr f1 h1 h2 j a, f2, f3, f4, f5, ?_, ?_, f8⟩
  · simp [State.storeW, Ne.symm h3, f6]
  · intro v hv hvs
    simp [State.storeW, Ne.symm h3, f7 v hv hvs]


/-! ## Phase B — `initReach`

Exact cost `4m + 3`: `wstore reach s 1` (1), `wset e 0` (1), `countLoop` (`m` iterations of
`1` test + `3` statements, then `1` exit test). -/


/-- The facts `allocAll` establishes, in the form `initReach` needs them (before `reach` is
seeded, so the array is still all-zero). -/
structure AllocPre (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  frame : Frontier.RAM.BF.Frame G st
  hheadL : st.wlen "head" = G.n + 1
  hposL : st.wlen "pos" = G.n
  hidxL : st.wlen "idx" = G.m
  hdist0 : ∀ j, st.va "dist" j = 0
  hws : st.w "s" = (s : ℕ)
  hhead0 : ∀ j, st.wa "head" j = 0
  hreachZ : ∀ j, st.wa "reach" j = 0

/-- `initReach`'s first store seeds `reach[s]`, turning `AllocPre` into `AllocFacts`. -/
theorem AllocPre.toAllocAfterReach {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (h : AllocPre G s st) : AllocFacts G s (st.storeW "reach" (s : ℕ) 1) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h
  refine ⟨Frontier.RAM.BF.Frame.storeW_reach f1 (s : ℕ) 1, f2, f3, f4, f5, ?_, ?_, f6⟩
  · simp [State.storeW]
  · intro v _ hvs
    simp [State.storeW, hvs, f8 v]

/-- Count-loop invariant: `head v` holds the number of edges `< k` whose source is `v`. -/
structure CountInv (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (k : ℕ) (t : State ℝ≥0) : Prop where
  alloc : AllocFacts G s t
  head : ∀ v, v ≤ G.n → t.wa "head" v = srcCnt G v k
  we : t.w "e" = k
  cost : t.cost = S.cost + 2 + 4 * k

theorem AllocFacts.storeReachS {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (h : AllocFacts G s st) : AllocFacts G s (st.storeW "reach" (s : ℕ) 1) := by
  obtain ⟨f1, f2, f3, f4, f5, _, f7, f8⟩ := h
  refine ⟨Frontier.RAM.BF.Frame.storeW_reach f1 (s : ℕ) 1, f2, f3, f4, f5, ?_, ?_, f8⟩
  · simp [State.storeW]
  · intro v hv hvs
    simp [State.storeW, hvs, f7 v hv hvs]

/-- One count iteration: `p := src[e]`, `head[p] += 1`, `e += 1`. -/
theorem countBody_runs {G : Graph} {s : Fin G.n} {S : State ℝ≥0} {k : ℕ} (hkm : k < G.m)
    {t : State ℝ≥0} (It : CountInv G s S k t) :
    Runs realOps countBody (t.charge 1) (CountInv G s S (k + 1)) := by
  obtain ⟨A, hhead, hwe, hcost⟩ := It
  have hcap : G.n + G.m + 2 ≤ t.cap := A.frame.hcap
  set p : ℕ := (G.src ⟨k, hkm⟩ : ℕ) with hp
  have hsrc : t.wa "src" k = p := A.frame.hsrc k hkm
  have hpL : p ≤ G.n := by rw [hp]; have := (G.src ⟨k, hkm⟩).isLt; omega
  have hheadp : t.wa "head" p = srcCnt G p k := hhead p hpL
  have hsrcE : evalW (t.charge 1) (.load "src" (.var "e")) = some p := by
    rw [evalW_load_of (show evalW (t.charge 1) (.var "e") = some k by
          simp [evalW_var, State.charge, hwe])
        (show k < (t.charge 1).wlen "src" by
          show k < t.wlen "src"; rw [A.frame.hsrcL]; exact hkm)]
    exact congrArg some hsrc
  refine runs_seq (runs_wset (x := "p") (e := .load "src" (.var "e")) (a := p) hsrcE ?_)
  set T1 : State ℝ≥0 := ((t.charge 1).setW "p" p).charge 1 with hT1
  have hT1p : T1.w "p" = p := by simp [hT1, State.setW, State.charge]
  have hT1headP : T1.wa "head" p = srcCnt G p k := by
    rw [hT1]; simp only [State.setW, State.charge]; exact hheadp
  have hT1headL : T1.wlen "head" = G.n + 1 := by
    rw [hT1]; simp only [State.setW, State.charge]; exact A.hheadL
  have hT1cap : G.n + G.m + 2 ≤ T1.cap := hcap
  have hstoreE : evalW T1 (.add (.load "head" (.var "p")) (.lit 1))
      = some (srcCnt G p k + 1) := by
    have hload : evalW T1 (.load "head" (.var "p")) = some (srcCnt G p k) := by
      rw [evalW_load_of (show evalW T1 (.var "p") = some p by rw [evalW_var, hT1p])
        (show p < T1.wlen "head" by rw [hT1headL]; omega), hT1headP]
    rw [evalW_add_of hload (evalW_lit_of (by have := hT1cap; omega))
      (by have := srcCnt_le G p k; have := hT1cap; omega)]
  refine runs_seq (runs_wstore (arr := "head") (i := .var "p")
    (e := .add (.load "head" (.var "p")) (.lit 1)) (j := p) (a := srcCnt G p k + 1)
    (show evalW T1 (.var "p") = some p by rw [evalW_var, hT1p]) hstoreE
    (show p < T1.wlen "head" by rw [hT1headL]; omega) ?_)
  set T2 : State ℝ≥0 := (T1.storeW "head" p (srcCnt G p k + 1)).charge 1 with hT2
  have hT2e : T2.w "e" = k := by
    simp [hT2, hT1, State.storeW, State.setW, State.charge, hwe]
  have hT2cap : G.n + G.m + 2 ≤ T2.cap := hcap
  have haddE : evalW T2 (.add (.var "e") (.lit 1)) = some (k + 1) := by
    rw [evalW_add_of (show evalW T2 (.var "e") = some k by rw [evalW_var, hT2e])
      (evalW_lit_of (by have := hT2cap; omega)) (by omega)]
  refine runs_wset (x := "e") (e := .add (.var "e") (.lit 1)) (a := k + 1) haddE ?_
  set T3 : State ℝ≥0 := (T2.setW "e" (k + 1)).charge 1 with hT3
  have hT3head : ∀ v, T3.wa "head" v = T2.wa "head" v := by
    intro v; rw [hT3]; simp only [State.setW, State.charge]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : AllocFacts G s T1 :=
      ((A.charge 1).setW "p" (by decide) (by decide) (by decide) p).charge 1
    have h2 : AllocFacts G s T2 :=
      (h1.storeW "head" (by decide) (by decide) (by decide) p _).charge 1
    exact (h2.setW "e" (by decide) (by decide) (by decide) (k + 1)).charge 1
  · intro v hv
    have hsuc : srcCnt G v (k + 1) = srcCnt G v k + (if p = v then 1 else 0) := by
      have h := srcCnt_succ (G := G) (v := v) hkm
      rw [← hp] at h
      exact h
    by_cases hvp : p = v
    · subst hvp
      rw [hT3head, hsuc]
      simp [hT2, hT1, State.storeW, State.setW, State.charge]
    · rw [hT3head, hsuc, if_neg hvp, hT2, hT1]
      simp [State.storeW, State.setW, State.charge, Ne.symm hvp, hhead v hv]
  · simp [hT3, hT2, hT1, State.setW, State.charge, hwe]
  · have hc : T3.cost = t.cost + 4 := by
      simp [hT3, hT2, hT1, State.setW, State.storeW, State.charge]
    rw [hc, hcost]; omega

theorem runs_initReach (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (A : AllocPre G s S) :
    Runs realOps initReach S (fun S2 => AllocFacts G s S2 ∧
      (∀ v, v ≤ G.n → S2.wa "head" v = srcCnt G v G.m) ∧
      S2.w "e" = G.m ∧ S2.cost = S.cost + 4 * G.m + 3) := by
  have hcap : G.n + G.m + 2 ≤ S.cap := A.frame.hcap
  have hcap1 : G.n + G.m + 2 ≤ ((S.storeW "reach" (s : ℕ) 1).charge 1).cap := hcap
  refine runs_seq (runs_wstore (arr := "reach") (i := .var "s") (e := .lit 1)
    (j := (s : ℕ)) (a := 1)
    (show evalW S (.var "s") = some (s : ℕ) by rw [evalW_var, A.hws])
    (evalW_lit_of (by have := hcap; omega))
    (show (s : ℕ) < S.wlen "reach" by rw [A.frame.hreachL]; exact s.isLt) ?_)
  refine runs_seq (runs_wset (x := "e") (e := .lit 0) (a := 0)
    (evalW_lit_of (by have := hcap1; omega)) ?_)
  set T : State ℝ≥0 := ((S.storeW "reach" (s : ℕ) 1).charge 1).setW "e" 0 |>.charge 1 with hT
  have hTalloc : AllocFacts G s T :=
    ((A.toAllocAfterReach.charge 1).setW "e" (by decide) (by decide) (by decide) 0).charge 1
  have hThead : ∀ v, v ≤ G.n → T.wa "head" v = srcCnt G v 0 := by
    intro v hv
    rw [srcCnt_zero]
    simp [hT, State.setW, State.storeW, State.charge, A.hhead0 v]
  have hTe : T.w "e" = 0 := by simp [hT, State.setW, State.charge]
  have hTcost : T.cost = S.cost + 2 + 4 * 0 := by
    simp [hT, State.setW, State.charge] <;> rfl
  have hloop : Runs realOps countLoop T (fun S2 => AllocFacts G s S2 ∧
      (∀ v, v ≤ G.n → S2.wa "head" v = srcCnt G v G.m) ∧
      S2.w "e" = G.m ∧ S2.cost = S.cost + 2 + 4 * G.m + 1) := by
    refine runs_while (fun k t => CountInv G s S k t) G.m _ ?_ ?_ T ⟨hTalloc, hThead, hTe, hTcost⟩
    · intro k hkm t It
      have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
      refine ⟨1, ?_, one_ne_zero, countBody_runs (S := S) hkm It⟩
      rw [evalW_lt_of (evalW_var t "e") (evalW_var t "m") (by have := hcap'; omega),
        It.we, It.alloc.frame.hm, if_pos hkm]
    · intro t It
      refine ⟨?_, It.alloc.charge 1, It.head, It.we, ?_⟩
      · have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
        rw [evalW_lt_of (evalW_var t "e") (evalW_var t "m") (by have := hcap'; omega),
          It.we, It.alloc.frame.hm]
        simp
      · show (t.charge 1).cost = S.cost + 2 + 4 * G.m + 1
        simp [State.charge, It.cost]
  obtain ⟨fL, rL, hexL, hAl, hHl, hEl, hCl⟩ := hloop
  exact ⟨fL, rL, hexL, hAl, hHl, hEl, by rw [hCl]; omega⟩


/-! ## Phase C1 — the prefix-sum section and the cursor copy

Costs: `wset i 0; wset k 0; prefixLoop` = `2 + (5n+1)`; `wstore head n k` = `1`;
`wset i 0; copyLoop` = `1 + (3n+1)`. -/

/-- Prefix invariant: below the cursor `head` is the final prefix sum `cnt v`; at or above
it `head v` is still the raw source count. -/
structure PrefixInv (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (k : ℕ) (t : State ℝ≥0) : Prop where
  alloc : AllocFacts G s t
  wi : t.w "i" = k
  wk : t.w "k" = cnt G k
  done : ∀ v, v < k → t.wa "head" v = cnt G v
  todo : ∀ v, k ≤ v → v ≤ G.n → t.wa "head" v = srcCnt G v G.m
  cost : t.cost = S.cost + 5 * k

theorem prefixBody_runs {G : Graph} {s : Fin G.n} {S : State ℝ≥0} {k : ℕ} (hkn : k < G.n)
    {t : State ℝ≥0} (It : PrefixInv G s S k t) :
    Runs realOps prefixBody (t.charge 1) (PrefixInv G s S (k + 1)) := by
  obtain ⟨A, hwi, hwk, hdone, htodo, hcost⟩ := It
  have hcap : G.n + G.m + 2 ≤ t.cap := A.frame.hcap
  have hheadk : t.wa "head" k = srcCnt G k G.m := htodo k le_rfl (by omega)
  have hheadL : t.wlen "head" = G.n + 1 := A.hheadL
  -- 1: `p := head[i]`
  have hE1 : evalW (t.charge 1) (.load "head" (.var "i")) = some (srcCnt G k G.m) := by
    rw [evalW_load_of (show evalW (t.charge 1) (.var "i") = some k by
          simp [evalW_var, State.charge, hwi])
        (show k < (t.charge 1).wlen "head" by
          show k < t.wlen "head"; rw [hheadL]; omega)]
    exact congrArg some hheadk
  refine runs_seq (runs_wset (x := "p") (e := .load "head" (.var "i"))
    (a := srcCnt G k G.m) hE1 ?_)
  set T1 : State ℝ≥0 := ((t.charge 1).setW "p" (srcCnt G k G.m)).charge 1 with hT1
  have hT1k : T1.w "k" = cnt G k := by simp [hT1, State.setW, State.charge, hwk]
  have hT1cap : G.n + G.m + 2 ≤ T1.cap := hcap
  have hT1headL : T1.wlen "head" = G.n + 1 := by
    rw [hT1]; simp only [State.setW, State.charge]; exact hheadL
  -- 2: `head[i] := k`
  refine runs_seq (runs_wstore (arr := "head") (i := .var "i") (e := .var "k") (j := k)
    (a := cnt G k)
    (show evalW T1 (.var "i") = some k by
      simp [evalW_var, hT1, State.setW, State.charge, hwi])
    (show evalW T1 (.var "k") = some (cnt G k) by rw [evalW_var, hT1k])
    (show k < T1.wlen "head" by rw [hT1headL]; omega) ?_)
  set T2 : State ℝ≥0 := (T1.storeW "head" k (cnt G k)).charge 1 with hT2
  have hT2k : T2.w "k" = cnt G k := by simp [hT2, State.storeW, State.charge, hT1k]
  have hT2p : T2.w "p" = srcCnt G k G.m := by
    simp [hT2, hT1, State.storeW, State.setW, State.charge]
  have hT2cap : G.n + G.m + 2 ≤ T2.cap := hcap
  -- 3: `k := k + p`
  refine runs_seq (runs_wset (x := "k") (e := .add (.var "k") (.var "p"))
    (a := cnt G (k + 1))
    (show evalW T2 (.add (.var "k") (.var "p")) = some (cnt G (k + 1)) by
      rw [evalW_add_of (show evalW T2 (.var "k") = some (cnt G k) by rw [evalW_var, hT2k])
        (show evalW T2 (.var "p") = some (srcCnt G k G.m) by rw [evalW_var, hT2p])
        (by have h := cnt_step (G := G) k; have h2 := cnt_le G (k + 1)
            have hc := hT2cap; omega)]
      exact congrArg some (cnt_step (G := G) k)) ?_)
  set T3 : State ℝ≥0 := (T2.setW "k" (cnt G (k + 1))).charge 1 with hT3
  have hT3i : T3.w "i" = k := by
    simp [hT3, hT2, hT1, State.storeW, State.setW, State.charge, hwi]
  have hT3cap : G.n + G.m + 2 ≤ T3.cap := hcap
  -- 4: `i := i + 1`
  refine runs_wset (x := "i") (e := .add (.var "i") (.lit 1)) (a := k + 1)
    (show evalW T3 (.add (.var "i") (.lit 1)) = some (k + 1) by
      rw [evalW_add_of (show evalW T3 (.var "i") = some k by rw [evalW_var, hT3i])
        (evalW_lit_of (by have := hT3cap; omega)) (by omega)]) ?_
  set T4 : State ℝ≥0 := (T3.setW "i" (k + 1)).charge 1 with hT4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : AllocFacts G s T1 :=
      ((A.charge 1).setW "p" (by decide) (by decide) (by decide) _).charge 1
    have h2 : AllocFacts G s T2 :=
      (h1.storeW "head" (by decide) (by decide) (by decide) k _).charge 1
    have h3 : AllocFacts G s T3 :=
      (h2.setW "k" (by decide) (by decide) (by decide) _).charge 1
    exact (h3.setW "i" (by decide) (by decide) (by decide) (k + 1)).charge 1
  · simp [hT4, State.setW, State.charge]
  · simp [hT4, hT3, hT2, hT1, State.storeW, State.setW, State.charge]
  · intro v hv
    have hheadT2 : T2.wa "head" v = cnt G v := by
      rw [hT2]; simp only [State.storeW, State.charge]
      by_cases hvk : v = k
      · subst hvk; simp
      · rw [if_neg (by rintro ⟨-, hjk⟩; exact hvk hjk)]
        rw [hT1]; simp only [State.setW, State.charge]
        exact hdone v (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hv) hvk)
    rw [hT4, hT3]
    simp only [State.setW, State.charge]
    exact hheadT2
  · intro v hvk hvn
    have hvk' : v ≠ k := by omega
    have hheadT2 : T2.wa "head" v = srcCnt G v G.m := by
      rw [hT2]; simp only [State.storeW, State.charge]
      rw [if_neg (by rintro ⟨-, hjk⟩; omega)]
      rw [hT1]; simp only [State.setW, State.charge]
      exact htodo v (by omega) hvn
    rw [hT4, hT3]
    simp only [State.setW, State.charge]
    exact hheadT2
  · have hc : T4.cost = t.cost + 5 := by
      simp [hT4, hT3, hT2, hT1, State.setW, State.storeW, State.charge]
    rw [hc, hcost]; omega

/-- The prefix loop from an arbitrary start state with `i = 0`, `k = 0`. -/
theorem runs_prefixLoop (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (A : AllocFacts G s S)
    (htodo0 : ∀ v, v ≤ G.n → S.wa "head" v = srcCnt G v G.m)
    (hi0 : S.w "i" = 0) (hk0 : S.w "k" = 0) :
    Runs realOps prefixLoop S (fun S2 => AllocFacts G s S2 ∧
      (∀ v, v < G.n → S2.wa "head" v = cnt G v) ∧
      S2.wa "head" G.n = srcCnt G G.n G.m ∧ S2.w "k" = G.m ∧
      S2.cost = S.cost + 5 * G.n + 1) := by
  have hTk : S.w "k" = cnt G 0 := by rw [hk0, cnt_zero]
  have hTcost : S.cost = S.cost + 5 * 0 := by omega
  refine runs_while (fun k t => PrefixInv G s S k t) G.n _ ?_ ?_ S
    ⟨A, hi0, hTk, (by intro v hv; omega), (fun v _ hv => htodo0 v hv), hTcost⟩
  · intro k hkn t It
    have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
    refine ⟨1, ?_, one_ne_zero, prefixBody_runs hkn It⟩
    rw [evalW_lt_of (evalW_var t "i") (evalW_var t "n") (by have := hcap'; omega),
      It.wi, It.alloc.frame.hn]
    simp [hkn]
  · intro t It
    have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
    refine ⟨?_, It.alloc.charge 1, (fun v hv => It.done v hv), ?_, It.wk.trans (cnt_top G), ?_⟩
    · rw [evalW_lt_of (evalW_var t "i") (evalW_var t "n") (by have := hcap'; omega),
        It.wi, It.alloc.frame.hn]
      simp
    · exact It.todo G.n le_rfl le_rfl
    · have hc1 : (t.charge 1).cost = t.cost + 1 := by simp [State.charge]
      rw [hc1, It.cost]

/-- Copy invariant: `pos` agrees with `head` below the cursor. -/
structure CopyInv (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (k : ℕ) (t : State ℝ≥0) : Prop where
  alloc : AllocFacts G s t
  wi : t.w "i" = k
  pos : ∀ v, v < k → t.wa "pos" v = t.wa "head" v
  head : ∀ v, v ≤ G.n → t.wa "head" v = cnt G v
  cost : t.cost = S.cost + 3 * k

theorem copyBody_runs {G : Graph} {s : Fin G.n} {S : State ℝ≥0} {k : ℕ} (hkn : k < G.n)
    {t : State ℝ≥0} (It : CopyInv G s S k t) :
    Runs realOps copyBody (t.charge 1) (CopyInv G s S (k + 1)) := by
  obtain ⟨A, hwi, hpos, hhead, hcost⟩ := It
  have hcap : G.n + G.m + 2 ≤ t.cap := A.frame.hcap
  have hE : evalW (t.charge 1) (.load "head" (.var "i")) = some (cnt G k) := by
    rw [evalW_load_of (show evalW (t.charge 1) (.var "i") = some k by
          simp [evalW_var, State.charge, hwi])
        (show k < (t.charge 1).wlen "head" by
          show k < t.wlen "head"; rw [A.hheadL]; omega)]
    exact congrArg some (hhead k (by omega))
  refine runs_seq (runs_wstore (arr := "pos") (i := .var "i") (e := .load "head" (.var "i"))
    (j := k) (a := cnt G k)
    (show evalW (t.charge 1) (.var "i") = some k by
      simp [evalW_var, State.charge, hwi])
    hE
    (show k < (t.charge 1).wlen "pos" by
      show k < t.wlen "pos"; rw [A.hposL]; omega) ?_)
  set T1 : State ℝ≥0 := ((t.charge 1).storeW "pos" k (cnt G k)).charge 1 with hT1
  have hT1i : T1.w "i" = k := by
    simp [hT1, State.storeW, State.charge, hwi]
  have hT1cap : G.n + G.m + 2 ≤ T1.cap := hcap
  refine runs_wset (x := "i") (e := .add (.var "i") (.lit 1)) (a := k + 1)
    (show evalW T1 (.add (.var "i") (.lit 1)) = some (k + 1) by
      rw [evalW_add_of (show evalW T1 (.var "i") = some k by rw [evalW_var, hT1i])
        (evalW_lit_of (by have := hT1cap; omega)) (by omega)]) ?_
  set T2 : State ℝ≥0 := (T1.setW "i" (k + 1)).charge 1 with hT2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : AllocFacts G s T1 :=
      ((A.charge 1).storeW "pos" (by decide) (by decide) (by decide) k _).charge 1
    exact (h1.setW "i" (by decide) (by decide) (by decide) (k + 1)).charge 1
  · simp [hT2, State.setW, State.charge]
  · intro v hv
    have hT1pos : T1.wa "pos" v = cnt G v := by
      rw [hT1]; simp only [State.storeW, State.charge]
      by_cases hvk : v = k
      · subst hvk; simp
      · rw [if_neg (by rintro ⟨-, hjk⟩; exact hvk hjk)]
        exact (hpos v (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hv) hvk)).trans
          (hhead v (by omega))
    have hT1head : T1.wa "head" v = cnt G v := by
      rw [hT1]; simp only [State.storeW, State.charge]; exact hhead v (by omega)
    rw [hT2]; simp only [State.setW, State.charge]
    rw [hT1pos, hT1head]
  · intro v hvn
    rw [hT2]; simp only [State.setW, State.charge]
    rw [hT1]; simp only [State.storeW, State.charge]; exact hhead v hvn
  · have hc : T2.cost = t.cost + 3 := by
      simp [hT2, hT1, State.setW, State.storeW, State.charge]
    rw [hc, hcost]; omega

/-- The copy loop from an arbitrary start state with `i = 0`. -/
theorem runs_copyLoop (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (A : AllocFacts G s S)
    (hhead : ∀ v, v ≤ G.n → S.wa "head" v = cnt G v) (hi0 : S.w "i" = 0) :
    Runs realOps copyLoop S (fun S2 => AllocFacts G s S2 ∧
      (∀ v, v < G.n → S2.wa "pos" v = S2.wa "head" v) ∧
      (∀ v, v ≤ G.n → S2.wa "head" v = cnt G v) ∧
      S2.cost = S.cost + 3 * G.n + 1) := by
  have hTcost : S.cost = S.cost + 3 * 0 := by omega
  refine runs_while (fun k t => CopyInv G s S k t) G.n _ ?_ ?_ S
    ⟨A, hi0, (by intro v hv; omega), hhead, hTcost⟩
  · intro k hkn t It
    have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
    refine ⟨1, ?_, one_ne_zero, copyBody_runs hkn It⟩
    rw [evalW_lt_of (evalW_var t "i") (evalW_var t "n") (by have := hcap'; omega),
      It.wi, It.alloc.frame.hn]
    simp [hkn]
  · intro t It
    have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
    refine ⟨?_, It.alloc.charge 1, (fun v hv => It.pos v hv), It.head, ?_⟩
    · rw [evalW_lt_of (evalW_var t "i") (evalW_var t "n") (by have := hcap'; omega),
        It.wi, It.alloc.frame.hn]
      simp
    · have hc1 : (t.charge 1).cost = t.cost + 1 := by simp [State.charge]
      rw [hc1, It.cost]

theorem rank_lt_cursor {G : Graph} {e : Fin G.m} {k : ℕ} (hek : (e : ℕ) < k) :
    rank G e < srcCnt G (G.src e : ℕ) k := by
  rw [rank_eq]
  have hone : srcCnt G (G.src e : ℕ) ((e : ℕ) + 1) = srcCnt G (G.src e : ℕ) (e : ℕ) + 1 := by
    rw [srcCnt_succ e.isLt]
    simp
  have hmono : srcCnt G (G.src e : ℕ) ((e : ℕ) + 1) ≤ srcCnt G (G.src e : ℕ) k :=
    srcCnt_mono (G := G) (v := (G.src e : ℕ)) (e := (e : ℕ) + 1) (e' := k) (by omega)
  omega

/-- The cursor cell of the current source is not yet exhausted: placing edge `k` lands
strictly inside `p`'s tiling cell `[cnt p, cnt (p+1))`. -/
theorem place_cell_lt (G : Graph) {k : ℕ} (hkm : k < G.m) :
    cnt G (G.src ⟨k, hkm⟩ : ℕ) + srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k <
      cnt G ((G.src ⟨k, hkm⟩ : ℕ) + 1) := by
  have hs : srcCnt G (G.src ⟨k, hkm⟩ : ℕ) (k + 1) =
      srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k + 1 := by
    rw [srcCnt_succ hkm]
    simp
  have hle : srcCnt G (G.src ⟨k, hkm⟩ : ℕ) (k + 1) ≤ srcCnt G (G.src ⟨k, hkm⟩ : ℕ) G.m :=
    srcCnt_mono (G := G) (v := (G.src ⟨k, hkm⟩ : ℕ)) (e := k + 1) (e' := G.m) (by omega)
  have h := cnt_step (G := G) (G.src ⟨k, hkm⟩ : ℕ)
  omega

/-- A previously placed edge occupies a slot different from the one edge `k` takes. -/
theorem place_slot_ne {G : Graph} {k : ℕ} (hkm : k < G.m) {e : Fin G.m}
    (hek : (e : ℕ) < k) :
    cnt G (G.src e : ℕ) + rank G e ≠
      cnt G (G.src ⟨k, hkm⟩ : ℕ) + srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k := by
  have hpcell : cnt G (G.src ⟨k, hkm⟩ : ℕ) + srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k <
      cnt G ((G.src ⟨k, hkm⟩ : ℕ) + 1) := place_cell_lt (G := G) hkm
  have hecell : cnt G (G.src e : ℕ) + rank G e < cnt G ((G.src e : ℕ) + 1) := by
    have herank : rank G e < srcCnt G (G.src e : ℕ) k := rank_lt_cursor hek
    have hle : srcCnt G (G.src e : ℕ) k ≤ srcCnt G (G.src e : ℕ) G.m :=
      srcCnt_mono (G := G) (v := (G.src e : ℕ)) (e := k) (e' := G.m) (by omega)
    have h := cnt_step (G := G) (G.src e : ℕ)
    omega
  rcases lt_trichotomy (G.src e : ℕ) (G.src ⟨k, hkm⟩ : ℕ) with hlt | heq | hgt
  · have hmono : cnt G ((G.src e : ℕ) + 1) ≤ cnt G (G.src ⟨k, hkm⟩ : ℕ) :=
      cnt_mono (G := G) (by omega)
    have h1 : cnt G (G.src e : ℕ) + rank G e < cnt G (G.src ⟨k, hkm⟩ : ℕ) :=
      lt_of_lt_of_le hecell hmono
    have h2 : cnt G (G.src ⟨k, hkm⟩ : ℕ) ≤
        cnt G (G.src ⟨k, hkm⟩ : ℕ) + srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k :=
      Nat.le_add_right _ _
    exact Nat.ne_of_lt (lt_of_lt_of_le h1 h2)
  · have herank : rank G e < srcCnt G (G.src e : ℕ) k := rank_lt_cursor hek
    have herank' : rank G e < srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k := by rw [← heq]; exact herank
    have hceq : cnt G (G.src e : ℕ) = cnt G (G.src ⟨k, hkm⟩ : ℕ) := by rw [heq]
    rw [hceq]
    exact Nat.ne_of_lt (Nat.add_lt_add_left herank' _)
  · have hmono : cnt G ((G.src ⟨k, hkm⟩ : ℕ) + 1) ≤ cnt G (G.src e : ℕ) :=
      cnt_mono (G := G) (by omega)
    have h4 : cnt G (G.src ⟨k, hkm⟩ : ℕ) + srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k <
        cnt G (G.src e : ℕ) := lt_of_lt_of_le hpcell hmono
    have h5 : cnt G (G.src e : ℕ) ≤ cnt G (G.src e : ℕ) + rank G e :=
      Nat.le_add_right _ _
    exact Ne.symm (Nat.ne_of_lt (lt_of_lt_of_le h4 h5))

/-- Placement invariant. -/
structure PlaceInv (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (k : ℕ) (t : State ℝ≥0) : Prop where
  alloc : AllocFacts G s t
  we : t.w "e" = k
  headcnt : ∀ v, v ≤ G.n → t.wa "head" v = cnt G v
  posform : ∀ v, v < G.n → t.wa "pos" v = t.wa "head" v + srcCnt G v k
  place : ∀ e : Fin G.m, (e : ℕ) < k →
    t.wa "idx" (t.wa "head" (G.src e) + rank G e) = (e : ℕ)
  cost : t.cost = S.cost + 6 * k

theorem placeBody_runs {G : Graph} {s : Fin G.n} {S : State ℝ≥0} {k : ℕ} (hkm : k < G.m)
    {t : State ℝ≥0} (It : PlaceInv G s S k t) :
    Runs realOps placeBody (t.charge 1) (PlaceInv G s S (k + 1)) := by
  obtain ⟨A, hwe, hheadcnt, hposform, hplace, hcost⟩ := It
  have hcap : G.n + G.m + 2 ≤ t.cap := A.frame.hcap
  set p : ℕ := (G.src ⟨k, hkm⟩ : ℕ) with hp
  have hpL : p < G.n := by rw [hp]; exact (G.src ⟨k, hkm⟩).isLt
  have hsrc : t.wa "src" k = p := A.frame.hsrc k hkm
  have hheadp : t.wa "head" p = cnt G p := hheadcnt p (by omega)
  -- 1: `p := src[e]`
  have hE1 : evalW (t.charge 1) (.load "src" (.var "e")) = some p := by
    rw [evalW_load_of (show evalW (t.charge 1) (.var "e") = some k by
          simp [evalW_var, State.charge, hwe])
        (show k < (t.charge 1).wlen "src" by
          show k < t.wlen "src"; rw [A.frame.hsrcL]; exact hkm)]
    exact congrArg some hsrc
  refine runs_seq (runs_wset (x := "p") (e := .load "src" (.var "e")) (a := p) hE1 ?_)
  set T1 : State ℝ≥0 := ((t.charge 1).setW "p" p).charge 1 with hT1
  have hT1p : T1.w "p" = p := by simp [hT1, State.setW, State.charge]
  have hT1posL : T1.wlen "pos" = G.n := by
    rw [hT1]; simp only [State.setW, State.charge]; exact A.hposL
  have hT1cap : G.n + G.m + 2 ≤ T1.cap := hcap
  have hposp : T1.wa "pos" p = t.wa "head" p + srcCnt G p k := by
    rw [hT1]; simp only [State.setW, State.charge]; exact hposform p hpL
  -- 2: `q := pos[p]`
  have hE2 : evalW T1 (.load "pos" (.var "p")) = some (t.wa "head" p + srcCnt G p k) := by
    rw [evalW_load_of (show evalW T1 (.var "p") = some p by rw [evalW_var, hT1p])
      (show p < T1.wlen "pos" by rw [hT1posL]; omega)]
    exact congrArg some hposp
  refine runs_seq (runs_wset (x := "q") (e := .load "pos" (.var "p"))
    (a := t.wa "head" p + srcCnt G p k) hE2 ?_)
  set q : ℕ := t.wa "head" p + srcCnt G p k with hq
  set T2 : State ℝ≥0 := ((T1.setW "q" q).charge 1) with hT2
  have hT2q : T2.w "q" = q := by simp [hT2, State.setW, State.charge]
  have hT2e : T2.w "e" = k := by
    simp [hT2, hT1, State.setW, State.charge, hwe]
  have hT2idxL : T2.wlen "idx" = G.m := by
    rw [hT2, hT1]; simp only [State.setW, State.charge]; exact A.hidxL
  have hT2cap : G.n + G.m + 2 ≤ T2.cap := hcap
  have hqm : q < G.m := by
    rw [hq, hheadp]
    have := place_cell_lt (G := G) hkm
    have := cnt_le G ((G.src ⟨k, hkm⟩ : ℕ) + 1)
    rw [hp] at *
    omega
  -- 3: `idx[q] := e`
  refine runs_seq (runs_wstore (arr := "idx") (i := .var "q") (e := .var "e") (j := q) (a := k)
    (show evalW T2 (.var "q") = some q by rw [evalW_var, hT2q])
    (show evalW T2 (.var "e") = some k by rw [evalW_var, hT2e])
    (show q < T2.wlen "idx" by rw [hT2idxL]; exact hqm) ?_)
  set T3 : State ℝ≥0 := (T2.storeW "idx" q k).charge 1 with hT3
  have hT3posL : T3.wlen "pos" = G.n := by
    rw [hT3, hT2, hT1]; simp only [State.storeW, State.setW, State.charge]; exact A.hposL
  have hT3p : T3.w "p" = p := by
    simp [hT3, hT2, hT1, State.storeW, State.setW, State.charge, hT1p]
  have hT3q : T3.w "q" = q := by
    simp [hT3, hT2, State.storeW, State.setW, State.charge, hT2q]
  have hT3cap : G.n + G.m + 2 ≤ T3.cap := hcap
  -- 4: `pos[p] := q + 1`
  refine runs_seq (runs_wstore (arr := "pos") (i := .var "p") (e := .add (.var "q") (.lit 1))
    (j := p) (a := q + 1)
    (show evalW T3 (.var "p") = some p by rw [evalW_var, hT3p])
    (show evalW T3 (.add (.var "q") (.lit 1)) = some (q + 1) by
      rw [evalW_add_of (show evalW T3 (.var "q") = some q by rw [evalW_var, hT3q])
        (evalW_lit_of (by have := hT3cap; omega)) (by have := hT3cap; omega)])
    (show p < T3.wlen "pos" by rw [hT3posL]; exact hpL) ?_)
  set T4 : State ℝ≥0 := (T3.storeW "pos" p (q + 1)).charge 1 with hT4
  have hT4e : T4.w "e" = k := by
    simp [hT4, hT3, hT2, hT1, State.storeW, State.setW, State.charge, hwe]
  have hT4cap : G.n + G.m + 2 ≤ T4.cap := hcap
  -- 5: `e := e + 1`
  refine runs_wset (x := "e") (e := .add (.var "e") (.lit 1)) (a := k + 1)
    (show evalW T4 (.add (.var "e") (.lit 1)) = some (k + 1) by
      rw [evalW_add_of (show evalW T4 (.var "e") = some k by rw [evalW_var, hT4e])
        (evalW_lit_of (by have := hT4cap; omega)) (by omega)]) ?_
  set T5 : State ℝ≥0 := (T4.setW "e" (k + 1)).charge 1 with hT5
  -- `head` is untouched by every store of this body
  have hheadT1 : ∀ v, T1.wa "head" v = t.wa "head" v := by
    intro v; rw [hT1]; simp only [State.setW, State.charge]
  have hheadT2 : ∀ v, T2.wa "head" v = T1.wa "head" v := by
    intro v; rw [hT2]; simp only [State.setW, State.charge]
  have hheadT3 : ∀ v, T3.wa "head" v = T2.wa "head" v := by
    intro v; rw [hT3]; simp only [State.storeW, State.charge]
    rw [if_neg (by rintro ⟨h1, -⟩; exact absurd h1 (by decide))]
  have hheadT4 : ∀ v, T4.wa "head" v = T3.wa "head" v := by
    intro v; rw [hT4]; simp only [State.storeW, State.charge]
    rw [if_neg (by rintro ⟨h1, -⟩; exact absurd h1 (by decide))]
  have hheadT5 : ∀ v, T5.wa "head" v = T4.wa "head" v := by
    intro v; rw [hT5]; simp only [State.setW, State.charge]
  have hheadT5' : ∀ v, T5.wa "head" v = t.wa "head" v := fun v =>
    (hheadT5 v).trans ((hheadT4 v).trans ((hheadT3 v).trans ((hheadT2 v).trans (hheadT1 v))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : AllocFacts G s T1 :=
      ((A.charge 1).setW "p" (by decide) (by decide) (by decide) p).charge 1
    have h2 : AllocFacts G s T2 :=
      (h1.setW "q" (by decide) (by decide) (by decide) q).charge 1
    have h3 : AllocFacts G s T3 :=
      (h2.storeW "idx" (by decide) (by decide) (by decide) q k).charge 1
    have h4 : AllocFacts G s T4 :=
      (h3.storeW "pos" (by decide) (by decide) (by decide) p (q + 1)).charge 1
    exact (h4.setW "e" (by decide) (by decide) (by decide) (k + 1)).charge 1
  · simp [hT5, hT4, hT3, hT2, hT1, State.storeW, State.setW, State.charge]
  · intro v hv
    rw [hheadT5' v]
    exact hheadcnt v hv
  · intro v hvn
    have hsuc : srcCnt G v (k + 1) = srcCnt G v k + (if p = v then 1 else 0) := by
      have h := srcCnt_succ (G := G) (v := v) hkm
      rw [← hp] at h
      exact h
    by_cases hvp : v = p
    · subst hvp
      have hT5pos : T5.wa "pos" p = q + 1 := by
        rw [hT5, hT4]; simp [State.setW, State.storeW, State.charge]
      have htgt : T5.wa "head" p + srcCnt G p (k + 1) = q + 1 := by
        rw [hheadT5' p, hsuc, if_pos rfl, hq]
        omega
      rw [hT5pos, htgt]
    · have hpv : p ≠ v := Ne.symm hvp
      have hT5pos : T5.wa "pos" v = T4.wa "pos" v := by
        rw [hT5]; simp only [State.setW, State.charge]
      have hT4pos : T4.wa "pos" v = T3.wa "pos" v := by
        rw [hT4]; simp only [State.storeW, State.charge]
        rw [if_neg (by rintro ⟨-, hv⟩; exact hvp hv)]
      have hT3pos : T3.wa "pos" v = T2.wa "pos" v := by
        rw [hT3]; simp only [State.storeW, State.charge]
        rw [if_neg (by rintro ⟨h1, -⟩; exact absurd h1 (by decide))]
      have hT2pos : T2.wa "pos" v = T1.wa "pos" v := by
        rw [hT2]; simp only [State.setW, State.charge]
      have hT1pos : T1.wa "pos" v = t.wa "pos" v := by
        rw [hT1]; simp only [State.setW, State.charge]
      rw [hT5pos, hT4pos, hT3pos, hT2pos, hT1pos, hsuc, if_neg hpv, hheadT5' v,
        hposform v hvn]
      omega
  · intro e hek
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hek) with hlt | heq
    · -- a previously placed edge: its slot differs from `q`
      have hne : t.wa "head" (G.src e) + rank G e ≠ q := by
        intro hcon
        have hA : t.wa "head" (G.src e) = cnt G (G.src e : ℕ) :=
          hheadcnt (G.src e) (by have := (G.src e).isLt; omega)
        have hB : q = cnt G (G.src ⟨k, hkm⟩ : ℕ) + srcCnt G (G.src ⟨k, hkm⟩ : ℕ) k := by
          rw [hq, hp,
            hheadcnt (G.src ⟨k, hkm⟩) (by have := (G.src ⟨k, hkm⟩).isLt; omega)]
        rw [hA, hB] at hcon
        exact place_slot_ne (G := G) hkm (e := e) hlt hcon
      have hstart : T5.wa "idx" (T5.wa "head" (G.src e) + rank G e) =
          T5.wa "idx" (t.wa "head" (G.src e) + rank G e) := by
        rw [hheadT5' (G.src e)]
      have hidxT5 : T5.wa "idx" (t.wa "head" (G.src e) + rank G e) =
          T4.wa "idx" (t.wa "head" (G.src e) + rank G e) := by
        rw [hT5]; simp only [State.setW, State.charge]
      have hidxT4 : T4.wa "idx" (t.wa "head" (G.src e) + rank G e) =
          T3.wa "idx" (t.wa "head" (G.src e) + rank G e) := by
        rw [hT4]; simp only [State.storeW, State.charge]
        rw [if_neg (by rintro ⟨h1, -⟩; exact absurd h1 (by decide))]
      have hidxT3 : T3.wa "idx" (t.wa "head" (G.src e) + rank G e) =
          T2.wa "idx" (t.wa "head" (G.src e) + rank G e) := by
        rw [hT3]; simp only [State.storeW, State.charge]
        rw [if_neg (by rintro ⟨-, hjk⟩; exact hne hjk)]
      have hidxT2 : T2.wa "idx" (t.wa "head" (G.src e) + rank G e) =
          T1.wa "idx" (t.wa "head" (G.src e) + rank G e) := by
        rw [hT2]; simp only [State.setW, State.charge]
      have hidxT1 : T1.wa "idx" (t.wa "head" (G.src e) + rank G e) =
          t.wa "idx" (t.wa "head" (G.src e) + rank G e) := by
        rw [hT1]; simp only [State.setW, State.charge]
      rw [hstart, hidxT5, hidxT4, hidxT3, hidxT2, hidxT1]
      exact hplace e hlt
    · -- the new edge `k` sits at `q`
      have hee : e = (⟨k, hkm⟩ : Fin G.m) := Fin.ext heq
      rw [hee]
      have hrank : rank G (⟨k, hkm⟩ : Fin G.m) = srcCnt G p k := by
        rw [rank_eq, hp]
      have hheadp2 : t.wa "head" p = cnt G (G.src ⟨k, hkm⟩ : ℕ) := by
        rw [hp, hheadcnt (G.src ⟨k, hkm⟩) (by have := (G.src ⟨k, hkm⟩).isLt; omega)]
      have hstart : T5.wa "idx" (T5.wa "head" (G.src ⟨k, hkm⟩) + rank G ⟨k, hkm⟩) =
          T5.wa "idx" q := by
        rw [hheadT5' (G.src ⟨k, hkm⟩), hrank,
          hheadcnt (G.src ⟨k, hkm⟩) (by have := (G.src ⟨k, hkm⟩).isLt; omega), hq, hheadp2]
      have hidxT5 : T5.wa "idx" q = T4.wa "idx" q := by
        rw [hT5]; simp only [State.setW, State.charge]
      have hidxT4 : T4.wa "idx" q = T3.wa "idx" q := by
        rw [hT4]; simp only [State.storeW, State.charge]
        rw [if_neg (by rintro ⟨h1, -⟩; exact absurd h1 (by decide))]
      have hidxT3 : T3.wa "idx" q = k := by
        rw [hT3]; simp only [State.storeW, State.charge]; simp
      rw [hstart, hidxT5, hidxT4, hidxT3]
  · have hc : T5.cost = t.cost + 6 := by
      simp [hT5, hT4, hT3, hT2, hT1, State.storeW, State.setW, State.charge]
    rw [hc, hcost]; omega

/-- The placement loop from an arbitrary start state with `e = 0`. -/
theorem runs_placeLoop (G : Graph) (s : Fin G.n) (S : State ℝ≥0) (A : AllocFacts G s S)
    (hheadcnt : ∀ v, v ≤ G.n → S.wa "head" v = cnt G v)
    (hpos0 : ∀ v, v < G.n → S.wa "pos" v = S.wa "head" v) (he0 : S.w "e" = 0) :
    Runs realOps placeLoop S (fun S2 => AllocFacts G s S2 ∧
      (∀ v, v ≤ G.n → S2.wa "head" v = cnt G v) ∧
      (∀ e : Fin G.m, S2.wa "idx" (S2.wa "head" (G.src e) + rank G e) = (e : ℕ)) ∧
      S2.cost = S.cost + 6 * G.m + 1) := by
  have hTpos : ∀ v, v < G.n → S.wa "pos" v = S.wa "head" v + srcCnt G v 0 := by
    intro v hv
    rw [srcCnt_zero, hpos0 v hv]
    omega
  have hTcost : S.cost = S.cost + 6 * 0 := by omega
  refine runs_while (fun k t => PlaceInv G s S k t) G.m _ ?_ ?_ S
    ⟨A, he0, hheadcnt, hTpos, (by intro e he; omega), hTcost⟩
  · intro k hkm t It
    have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
    refine ⟨1, ?_, one_ne_zero, placeBody_runs hkm It⟩
    rw [evalW_lt_of (evalW_var t "e") (evalW_var t "m") (by have := hcap'; omega),
      It.we, It.alloc.frame.hm]
    simp [hkm]
  · intro t It
    have hcap' : G.n + G.m + 2 ≤ t.cap := It.alloc.frame.hcap
    refine ⟨?_, It.alloc.charge 1, It.headcnt, (fun e => It.place e (by have := It.we; omega)),
      ?_⟩
    · rw [evalW_lt_of (evalW_var t "e") (evalW_var t "m") (by have := hcap'; omega),
        It.we, It.alloc.frame.hm]
      simp
    · have hc1 : (t.charge 1).cost = t.cost + 1 := by simp [State.charge]
      rw [hc1, It.cost]


/-! ## Phase D — the rank bijection and `CSRPart`

`rank` maps the edges of one source class bijectively onto `[0, srcCnt v m)`.  Injectivity is
`rank_lt_of_lt`; surjectivity is a cardinality argument.  This is what turns the placement
invariant into `csr_seg`/`csr_cover`. -/

theorem rank_bij {G : Graph} {v r : ℕ} (hr : r < srcCnt G v G.m) :
    ∃ e : Fin G.m, (G.src e : ℕ) = v ∧ rank G e = r := by
  classical
  set A : Finset (Fin G.m) := Finset.univ.filter (fun e' => (G.src e' : ℕ) = v) with hA
  have hAcard : A.card = srcCnt G v G.m := by
    rw [hA, srcCnt_full]
  have hinj : ∀ a ∈ A, ∀ b ∈ A, rank G a = rank G b → a = b := by
    intro a ha b hb hab
    by_contra hne
    have hsa : (G.src a : ℕ) = v := (Finset.mem_filter.mp ha).2
    have hsb : (G.src b : ℕ) = v := (Finset.mem_filter.mp hb).2
    have hsrc : G.src a = G.src b := Fin.ext (by omega)
    rcases lt_trichotomy (a : ℕ) (b : ℕ) with hlt | heq | hgt
    · have := rank_lt_of_lt hsrc hlt
      omega
    · exact hne (Fin.ext heq)
    · have := rank_lt_of_lt hsrc.symm hgt
      omega
  have himg : (A.image (rank G)).card = srcCnt G v G.m := by
    rw [Finset.card_image_of_injOn hinj, hAcard]
  have hsub : A.image (rank G) ⊆ Finset.range (srcCnt G v G.m) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have hse : (G.src e : ℕ) = v := (Finset.mem_filter.mp he).2
    refine Finset.mem_range.mpr ?_
    have h := rank_lt G e
    rw [hse] at h
    exact h
  have himgEq : A.image (rank G) = Finset.range (srcCnt G v G.m) := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [himg, Finset.card_range]
  have hmem : r ∈ A.image (rank G) := by
    rw [himgEq]
    exact Finset.mem_range.mpr hr
  obtain ⟨e, he, her⟩ := Finset.mem_image.mp hmem
  exact ⟨e, (Finset.mem_filter.mp he).2, her⟩

/-- `CSRPart` from the phase-C facts. -/
theorem csrPart_of {G : Graph} {st : State ℝ≥0}
    (hheadL : st.wlen "head" = G.n + 1) (hposL : st.wlen "pos" = G.n)
    (hidxL : st.wlen "idx" = G.m)
    (hheadcnt : ∀ v, v ≤ G.n → st.wa "head" v = cnt G v)
    (hplace : ∀ e : Fin G.m, st.wa "idx" (st.wa "head" (G.src e) + rank G e) = (e : ℕ)) :
    CSRPart G st := by
  refine ⟨hheadL, hposL, hidxL, ?_, ?_, hheadcnt, ?_, ?_⟩
  · intro v hv
    rw [hheadcnt v hv]
    exact cnt_le G v
  · intro i j hij hjn
    rw [hheadcnt i (by omega), hheadcnt j hjn]
    exact cnt_mono (G := G) hij
  · intro v q hl hq
    have hnext : st.wa "head" ((v : ℕ) + 1) = cnt G (v : ℕ) + srcCnt G (v : ℕ) G.m := by
      rw [hheadcnt ((v : ℕ) + 1) (by have := v.isLt; omega), cnt_step (G := G) (v : ℕ)]
    have hcntv : st.wa "head" (v : ℕ) = cnt G (v : ℕ) := hheadcnt (v : ℕ) (by omega)
    have hr : q - st.wa "head" (v : ℕ) < srcCnt G (v : ℕ) G.m := by
      rw [hnext] at hq
      omega
    obtain ⟨e, hse, hre⟩ := rank_bij (G := G) hr
    have hqv : q = st.wa "head" (G.src e) + rank G e := by
      have h1 : st.wa "head" (G.src e) = st.wa "head" (v : ℕ) := by rw [hse]
      rw [h1, hre]
      exact (Nat.add_sub_of_le hl).symm
    have hidxe : st.wa "idx" q = (e : ℕ) := by
      rw [hqv]
      exact hplace e
    have hqm : q < G.m := by
      have hsum : cnt G (v : ℕ) + srcCnt G (v : ℕ) G.m ≤ G.m := by
        have hstep := cnt_step (G := G) (v : ℕ)
        have hle := cnt_le G ((v : ℕ) + 1)
        omega
      rw [hnext] at hq
      omega
    exact ⟨hqm,
      by have := e.isLt; rw [hidxe]; exact e.isLt,
      by
        intro hq'
        have hfin : (⟨st.wa "idx" q, hq'⟩ : Fin G.m) = e := Fin.ext hidxe
        rw [hfin]
        exact Fin.ext hse⟩
  · intro e
    have hcnt : st.wa "head" (G.src e) = cnt G (G.src e : ℕ) :=
      hheadcnt (G.src e) (by have := (G.src e).isLt; omega)
    have hnext : st.wa "head" ((G.src e : ℕ) + 1) =
        cnt G (G.src e : ℕ) + srcCnt G (G.src e : ℕ) G.m := by
      rw [hheadcnt ((G.src e : ℕ) + 1) (by have := (G.src e).isLt; omega),
        cnt_step (G := G) (G.src e : ℕ)]
    refine ⟨st.wa "head" (G.src e) + rank G e, Nat.le_add_right _ _, ?_, hplace e⟩
    rw [hnext, hcnt]
    have hlt := rank_lt G e
    omega

theorem runs_csr (G : Graph) (s : Fin G.n) :
    Runs realOps (seq allocAll (seq initReach buildCSR)) (initState dijkstraProgram G s)
      (fun st => PreMain G s st ∧ (st.cost : ℝ) ≤ 12 * ((G.n : ℝ) + G.m) + 17) := by
  refine runs_seq (a := allocAll) (b := seq initReach buildCSR) (Runs.mono (runs_allocAll G s) ?_)
  rintro S1 ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩, hnl, hpl, hil, hz1, hz2, hz3,
    hz4, hwsA, hzr, hcA⟩
  have hPre : AllocPre G s S1 :=
    ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩, hnl, hpl, hil, hz4, hwsA, hz1, hzr⟩
  -- Phase B: `initReach`
  refine runs_seq (a := initReach) (b := buildCSR) (Runs.mono (runs_initReach G s S1 hPre) ?_)
  rintro S2 ⟨A2, hsrc2, hwe2, hc2⟩
  have hcap2 : G.n + G.m + 2 ≤ S2.cap := A2.frame.hcap
  -- `i := 0`
  refine runs_seq (a := wset "i" (.lit 0)) (b := seq (wset "k" (.lit 0))
    (seq prefixLoop (seq (wstore "head" (.var "n") (.var "k"))
      (seq (wset "i" (.lit 0)) (seq copyLoop (seq (wset "e" (.lit 0)) placeLoop))))))
    (Runs.mono (runs_wset (x := "i") (e := .lit 0) (a := 0) (s := S2)
      (Q := fun t => AllocFacts G s t ∧ (∀ v, v ≤ G.n → t.wa "head" v = srcCnt G v G.m) ∧
        t.w "i" = 0 ∧ t.cost = S2.cost + 1)
      (evalW_lit_of (by have := hcap2; omega)) ?_) ?_)
  · refine ⟨A2.setW "i" (by decide) (by decide) (by decide) 0 |>.charge 1, ?_, ?_, ?_⟩
    · intro v hv; simp [State.setW, State.charge, hsrc2 v hv]
    · simp [State.setW, State.charge]
    · simp [State.setW, State.charge]
  rintro T1 ⟨A1, hsrc1, hi1, hc1⟩
  -- `k := 0`
  refine runs_seq (a := wset "k" (.lit 0)) (b := seq prefixLoop (seq (wstore "head" (.var "n")
    (.var "k")) (seq (wset "i" (.lit 0)) (seq copyLoop (seq (wset "e" (.lit 0)) placeLoop)))))
    (Runs.mono (runs_wset (x := "k") (e := .lit 0) (a := 0) (s := T1)
      (Q := fun t => AllocFacts G s t ∧ (∀ v, v ≤ G.n → t.wa "head" v = srcCnt G v G.m) ∧
        t.w "i" = 0 ∧ t.w "k" = 0 ∧ t.cost = T1.cost + 1)
      (evalW_lit_of (by have := A1.frame.hcap; omega)) ?_) ?_)
  · refine ⟨A1.setW "k" (by decide) (by decide) (by decide) 0 |>.charge 1, ?_, ?_, ?_, ?_⟩
    · intro v hv; simp [State.setW, State.charge, hsrc1 v hv]
    · simp [State.setW, State.charge, hi1]
    · simp [State.setW, State.charge]
    · simp [State.setW, State.charge]
  rintro T2 ⟨A3, hsrc3, hi3, hk3, hc3⟩
  -- the prefix loop
  refine runs_seq (a := prefixLoop) (b := seq (wstore "head" (.var "n") (.var "k"))
    (seq (wset "i" (.lit 0)) (seq copyLoop (seq (wset "e" (.lit 0)) placeLoop))))
    (Runs.mono (runs_prefixLoop G s T2 A3 hsrc3 hi3 hk3) ?_)
  rintro T3 ⟨A4, hdone4, htop4, hk4, hc4⟩
  -- `head[n] := k`
  refine runs_seq (a := wstore "head" (.var "n") (.var "k")) (b := seq (wset "i" (.lit 0))
    (seq copyLoop (seq (wset "e" (.lit 0)) placeLoop)))
    (Runs.mono (runs_wstore (arr := "head") (i := .var "n") (e := .var "k") (j := G.n) (a := G.m)
      (s := T3) (Q := fun t => AllocFacts G s t ∧ (∀ v, v ≤ G.n → t.wa "head" v = cnt G v) ∧
        t.cost = T3.cost + 1)
      (show evalW T3 (.var "n") = some G.n by rw [evalW_var, A4.frame.hn])
      (show evalW T3 (.var "k") = some G.m by rw [evalW_var, hk4])
      (show G.n < T3.wlen "head" by rw [A4.hheadL]; omega) ?_) ?_)
  · refine ⟨(A4.storeW "head" (by decide) (by decide) (by decide) G.n G.m).charge 1, ?_, ?_⟩
    · intro v hv
      by_cases hvN : v = G.n
      · subst hvN
        simp [State.storeW, State.charge, cnt_top]
      · have hlt : v < G.n := by omega
        simp [State.storeW, State.charge, hvN, hdone4 v hlt]
    · simp [State.storeW, State.charge]
  rintro T4 ⟨A5, hhead5, hc5⟩
  have hcap5 : G.n + G.m + 2 ≤ T4.cap := A5.frame.hcap
  -- `i := 0`
  refine runs_seq (a := wset "i" (.lit 0)) (b := seq copyLoop (seq (wset "e" (.lit 0)) placeLoop))
    (Runs.mono (runs_wset (x := "i") (e := .lit 0) (a := 0) (s := T4)
      (Q := fun t => AllocFacts G s t ∧ (∀ v, v ≤ G.n → t.wa "head" v = cnt G v) ∧
        t.w "i" = 0 ∧ t.cost = T4.cost + 1)
      (evalW_lit_of (by have := hcap5; omega)) ?_) ?_)
  · refine ⟨A5.setW "i" (by decide) (by decide) (by decide) 0 |>.charge 1, ?_, ?_, ?_⟩
    · intro v hv; simp [State.setW, State.charge, hhead5 v hv]
    · simp [State.setW, State.charge]
    · simp [State.setW, State.charge]
  rintro T5 ⟨A6, hhead6, hi6, hc6⟩
  -- the copy loop
  refine runs_seq (a := copyLoop) (b := seq (wset "e" (.lit 0)) placeLoop)
    (Runs.mono (runs_copyLoop G s T5 A6 hhead6 hi6) ?_)
  rintro T6 ⟨A7, hpos7, hhead7, hc7⟩
  have hcap7 : G.n + G.m + 2 ≤ T6.cap := A7.frame.hcap
  -- `e := 0`
  refine runs_seq (a := wset "e" (.lit 0)) (b := placeLoop)
    (Runs.mono (runs_wset (x := "e") (e := .lit 0) (a := 0) (s := T6)
      (Q := fun t => AllocFacts G s t ∧ (∀ v, v ≤ G.n → t.wa "head" v = cnt G v) ∧
        (∀ v, v < G.n → t.wa "pos" v = t.wa "head" v) ∧ t.w "e" = 0 ∧
        t.cost = T6.cost + 1)
      (evalW_lit_of (by have := hcap7; omega)) ?_) ?_)
  · refine ⟨A7.setW "e" (by decide) (by decide) (by decide) 0 |>.charge 1, ?_, ?_, ?_, ?_⟩
    · intro v hv; simp [State.setW, State.charge, hhead7 v hv]
    · intro v hv; simp [State.setW, State.charge, hpos7 v hv]
    · simp [State.setW, State.charge]
    · simp [State.setW, State.charge]
  rintro T7 ⟨A8, hhead8, hpos8, he8, hc8⟩
  -- the placement loop
  refine Runs.mono (runs_placeLoop G s T7 A8 hhead8 hpos8 he8) ?_
  rintro T8 ⟨A9, hhead9, hplace9, hc9⟩
  -- `PreMain` and the cost bound
  refine ⟨⟨A9.frame, csrPart_of A9.hheadL A9.hposL A9.hidxL hhead9 hplace9, ?_, A9.hreachS, ?_,
    (fun v => A9.hdist0 v)⟩, ?_⟩
  · intro v
    by_cases hvs : v = s
    · subst hvs; rw [A9.hreachS]
    · rw [A9.hreach0 v v.isLt (by intro h; exact hvs (Fin.ext h))]; omega
  · intro v hvs
    exact A9.hreach0 v v.isLt (by intro h; exact hvs (Fin.ext h))
  · have hcost : T8.cost = 12 * G.n + 11 * G.m + 17 := by omega
    have hcast : (T8.cost : ℝ) = 12 * (G.n : ℝ) + 11 * (G.m : ℝ) + 17 := by
      exact_mod_cast hcost
    have hm0 : (0 : ℝ) ≤ (G.m : ℝ) := Nat.cast_nonneg _
    linarith

end BigOSpeedrun.DirectedSSSP.Dijkstra
