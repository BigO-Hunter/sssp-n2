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
        (∀ j, S1.wa "idx" j = 0) ∧ (∀ j, S1.va "dist" j = 0) ∧
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- `Frame` survives stores into any array other than the two input arrays. -/
theorem frame_storeW_arr {G : Graph} {st : State ℝ≥0} (h : Frontier.RAM.BF.Frame G st)
    {arr : String} (h1 : arr ≠ "src") (h2 : arr ≠ "dst") (j a : ℕ) :
    Frontier.RAM.BF.Frame G (st.storeW arr j a) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := h
  refine ⟨f1, f2, f3, ?_, ?_, f6, f7, f8, f9, f10, f11⟩
  · intro j' hj'; simp [State.storeW, Ne.symm h1, f4 j' hj']
  · intro j' hj'; simp [State.storeW, Ne.symm h2, f5 j' hj']

theorem AllocFacts.setW {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : AllocFacts G s st)
    (x : String) (hxn : x ≠ "n") (hxm : x ≠ "m") (a : ℕ) : AllocFacts G s (st.setW x a) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  exact ⟨f1.setW hxn hxm a, f2, f3, f4, f5, f6, f7⟩

theorem AllocFacts.charge {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : AllocFacts G s st)
    (k : ℕ) : AllocFacts G s (st.charge k) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  exact ⟨f1.charge k, f2, f3, f4, f5, f6, f7⟩

theorem AllocFacts.storeW {G : Graph} {s : Fin G.n} {st : State ℝ≥0} (h : AllocFacts G s st)
    (arr : String) (h1 : arr ≠ "src") (h2 : arr ≠ "dst") (h3 : arr ≠ "reach") (j a : ℕ) :
    AllocFacts G s (st.storeW arr j a) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h
  refine ⟨frame_storeW_arr f1 h1 h2 j a, f2, f3, f4, f5, ?_, ?_⟩
  · simp [State.storeW, Ne.symm h3, f6]
  · intro v hv hvs
    simp [State.storeW, Ne.symm h3, f7 v hv hvs]

theorem runs_csr (G : Graph) (s : Fin G.n) :
    Runs realOps (seq allocAll (seq initReach buildCSR)) (initState dijkstraProgram G s)
      (fun st => PreMain G s st ∧ (st.cost : ℝ) ≤ 12 * ((G.n : ℝ) + G.m) + 17) := by
  sorry

end BigOSpeedrun.DirectedSSSP.Dijkstra
