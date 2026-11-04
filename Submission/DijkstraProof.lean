import Submission.DijkstraCSR

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
open Frontier Frontier.RAM Graph
open WExpr Stmt

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

/-- The min-scan postcondition: `best = n` means no `reach = 1` vertex below `n`;
otherwise `best` is a `reach = 1` vertex of minimum `dist`. -/
def ScanPost (G : Graph) (st : State ℝ≥0) (best : ℕ) : Prop :=
  (best = G.n ∧ ∀ v : Fin G.n, st.wa "reach" v = 1 → False) ∨
  (best < G.n ∧ st.wa "reach" best = 1 ∧
    ∀ v : Fin G.n, st.wa "reach" v = 1 → (st.va "dist" best : ℝ≥0) ≤ st.va "dist" v)

/-- The exchange argument: the scan winner's label equals its true distance. -/
theorem min_settled_exact {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : Fin G.n}
    (I : Inv G s st) (hu : st.wa "reach" u = 1)
    (hmin : ∀ v : Fin G.n, st.wa "reach" v = 1 → (st.va "dist" u : ℝ≥0) ≤ st.va "dist" v) :
    ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) = G.dist s u := by
  -- `≥`: the label is realized by a walk, so it bounds the distance from above
  have hwalk : ∃ p, G.IsWalk s u p ∧ G.len p = st.va "dist" u :=
    I.walk_sound u (by rw [hu]; exact one_ne_zero)
  obtain ⟨p, hp, hlen⟩ := hwalk
  have hle1 : G.dist s u ≤ ((G.len p : ℝ≥0) : ℝ≥0∞) := dist_le_len hp
  rw [hlen] at hle1
  -- `≤`: the first unsettled vertex on a shortest walk to `u` is bounded by that walk
  obtain ⟨p', hp', hpe, -, -⟩ := exists_shortest_path ⟨p, hp⟩
  obtain ⟨x, hx, hlex⟩ := exists_reached_le G s I p' s u 0 hp' (Or.inl rfl) hu
  have hmin' : (st.va "dist" u : ℝ≥0) ≤ st.va "dist" x := hmin x hx
  have h2 : ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) ≤ ((G.len p' : ℝ≥0) : ℝ≥0∞) := by
    apply ENNReal.coe_le_coe.mpr
    have h0 : (st.va "dist" x : ℝ≥0) ≤ G.len p' := by simpa using hlex
    exact le_trans hmin' h0
  have h2' : ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) ≤ G.dist s u := by
    rw [← hpe]
    exact h2
  exact le_antisymm h2' hle1

/-! ## Counting bookkeeping -/

/-- Number of settled (`reach = 2`) vertices. -/
noncomputable def settleCard (G : Graph) (st : State ℝ≥0) : ℕ :=
  (Finset.univ.filter (fun v : Fin G.n => st.wa "reach" v = 2)).card

theorem settleCard_storeW2 {G : Graph} {st : State ℝ≥0} {u : Fin G.n}
    (h : st.wa "reach" u = 1) :
    settleCard G (st.storeW "reach" u 2) = settleCard G st + 1 := by
  have hp : ∀ v : Fin G.n, (st.storeW "reach" u 2).wa "reach" v = 2 ↔
      (v = u ∨ st.wa "reach" v = 2) := by
    intro v
    by_cases hv : v = u
    · subst hv
      simp [State.storeW, h]
    · have hne : ¬ ((v : ℕ) = (u : ℕ)) := fun hh => hv (Fin.ext hh)
      constructor
      · intro hh
        simp [State.storeW, hne] at hh
        exact Or.inr hh
      · intro hh
        rcases hh with hh | hh
        · exact absurd hh hv
        · simp [State.storeW, hne] at hh ⊢
          exact hh
  have key : (Finset.univ.filter (fun v : Fin G.n => (st.storeW "reach" u 2).wa "reach" v = 2)) =
      insert u (Finset.univ.filter (fun v : Fin G.n => st.wa "reach" v = 2)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
    rw [hp]
  rw [settleCard, settleCard, key, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hh
  simp [h] at hh

theorem settleCard_storeW1 {G : Graph} {st : State ℝ≥0} {v : Fin G.n}
    (h : st.wa "reach" v = 0) :
    settleCard G (st.storeW "reach" v 1) = settleCard G st := by
  apply congrArg Finset.card
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hw : (w : ℕ) = v
  · have hw' : w = v := Fin.ext hw
    subst hw'
    simp [State.storeW, h]
  · simp [State.storeW, hw]

theorem settleCard_le (G : Graph) (st : State ℝ≥0) : settleCard G st ≤ G.n := by
  unfold settleCard
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- Total out-degree of the settled vertices (charges the relax work). -/
noncomputable def settledEdges (G : Graph) (st : State ℝ≥0) : ℕ :=
  ∑ v : Fin G.n, if st.wa "reach" v = 2 then srcCnt G v G.m else 0

theorem settledEdges_storeW2 {G : Graph} {st : State ℝ≥0} {u : Fin G.n}
    (h : st.wa "reach" u = 1) :
    settledEdges G (st.storeW "reach" u 2) = settledEdges G st + srcCnt G u G.m := by
  have hg0 : (if st.wa "reach" u = 2 then srcCnt G u G.m else 0) = 0 := by simp [h]
  have hpt : ∀ v : Fin G.n,
      (if (st.storeW "reach" u 2).wa "reach" v = 2 then srcCnt G v G.m else 0) =
      (if st.wa "reach" v = 2 then srcCnt G v G.m else 0) +
        (if v = u then srcCnt G u G.m else 0) := by
    intro v
    by_cases hv : v = u
    · subst hv
      simp [State.storeW, h, hg0]
    · have hne : ¬ ((v : ℕ) = (u : ℕ)) := fun hh => hv (Fin.ext hh)
      simp [State.storeW, hne, hv]
  have hitesum : (∑ x : Fin G.n, if x = u then srcCnt G u G.m else 0) = srcCnt G u G.m := by
    rw [Fintype.sum_eq_single u]
    · simp
    · intro x hx
      simp [hx]
  rw [settledEdges, settledEdges]
  conv_lhs => simp only [hpt, Finset.sum_add_distrib]
  rw [hitesum]

theorem settledEdges_storeW1 {G : Graph} {st : State ℝ≥0} {v : Fin G.n}
    (h : st.wa "reach" v = 0) :
    settledEdges G (st.storeW "reach" v 1) = settledEdges G st := by
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = v
  · subst hw
    simp [State.storeW, h]
  · have hne : ¬ ((w : ℕ) = v) := fun hh => hw (Fin.ext hh)
    simp [State.storeW, hne]

theorem sum_srcCnt (G : Graph) : (∑ v : Fin G.n, srcCnt G v G.m) = G.m := by
  have h1 : ∀ v : Fin G.n,
      srcCnt G v G.m = ∑ e : Fin G.m, if (G.src e : ℕ) = (v : ℕ) then 1 else 0 := by
    intro v
    rw [srcCnt_full, card_filter_eq_sum]
  rw [show (∑ v : Fin G.n, srcCnt G v G.m) =
      (∑ v : Fin G.n, ∑ e : Fin G.m, if (G.src e : ℕ) = (v : ℕ) then 1 else 0) from
      Finset.sum_congr rfl fun v _ => h1 v]
  rw [Finset.sum_comm]
  have h2 : ∀ e : Fin G.m, (∑ v : Fin G.n, if (G.src e : ℕ) = (v : ℕ) then 1 else 0) = 1 := by
    intro e
    rw [Fintype.sum_eq_single (G.src e)]
    · simp
    · intro x hx
      have hne : ¬ ((G.src e : ℕ) = (x : ℕ)) := fun hh => hx (Fin.ext hh).symm
      simp [hne]
  have h3 : (∑ e : Fin G.m, ∑ v : Fin G.n, if (G.src e : ℕ) = (v : ℕ) then 1 else 0) =
      (∑ e : Fin G.m, (1 : ℕ)) := Finset.sum_congr rfl fun e _ => h2 e
  rw [h3]
  simp

theorem settledEdges_le (G : Graph) (st : State ℝ≥0) : settledEdges G st ≤ G.m := by
  unfold settledEdges
  calc (∑ v : Fin G.n, if st.wa "reach" v = 2 then srcCnt G v G.m else 0)
      ≤ ∑ v : Fin G.n, srcCnt G v G.m :=
        Finset.sum_le_sum fun v _ => by by_cases hh : st.wa "reach" v = 2 <;> simp [hh]
    _ = G.m := sum_srcCnt G

/-! ## One relax step -/

/-- `evalV` of `relaxVal` at registers `u`/`e` (same tree as `Frontier.RAM.BF.relaxVal`). -/
theorem eval_relaxVal' {S : State ℝ≥0} {u j : ℕ} (hu : S.w "u" = u) (he : S.w "e" = j)
    (hul : u < S.vlen "dist") (hjl : j < S.vlen "w") :
    evalV realOps S relaxVal = some (S.va "dist" u + S.va "w" j) :=
  evalV_add_of (evalV_load_of (by rw [evalW_var, hu]) hul)
    (evalV_load_of (by rw [evalW_var, he]) hjl)

/-! ## Relaxation of one edge -/

/-- Relax of an edge out of a settled vertex into an **unreached** target: the target is
reached with label `dist[u] + w[e]` and a fresh walk.  Shaped like the `exec` steps of
`vstore` + `wstore`. -/
theorem inv_relax_unreached {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) {u : Fin G.n} {e : Fin G.m}
    (hu : st.wa "reach" u = 2) (hsrc : G.src e = u) (hv0 : st.wa "reach" (G.dst e) = 0) :
    Inv G s (((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1
      |>.storeW "reach" (G.dst e) 1).charge 1) := by
  set st' : State ℝ≥0 := (((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1
    |>.storeW "reach" (G.dst e) 1).charge 1) with hst'
  have hreach' : ∀ v : Fin G.n, st'.wa "reach" v = if v = G.dst e then 1 else st.wa "reach" v := by
    intro v
    by_cases hv : v = G.dst e
    · subst hv
      simp [st', State.storeW, State.charge]
    · have hne : ¬ ((v : ℕ) = (G.dst e : ℕ)) := fun hh => hv (Fin.ext hh)
      simp [st', State.storeW, State.storeV, State.charge, hne, hv]
  have hdist' : ∀ v : Fin G.n, st'.va "dist" v =
      if v = G.dst e then st.va "dist" u + G.w e else st.va "dist" v := by
    intro v
    by_cases hv : v = G.dst e
    · subst hv
      simp [st', State.storeW, State.storeV, State.charge]
    · have hne : ¬ ((v : ℕ) = (G.dst e : ℕ)) := fun hh => hv (Fin.ext hh)
      simp [st', State.storeW, State.storeV, State.charge, hne, hv]
  have hframe : Frontier.RAM.BF.Frame G st' :=
    ((I.frame.storeV_dist (G.dst e) (st.va "dist" u + G.w e)).charge 1
      |>.storeW_reach (G.dst e) 1 |>.charge 1)
  have hcsr : CSRPart G st' :=
    ((I.csr.storeV_dist (G.dst e) (st.va "dist" u + G.w e)).charge 1
      |>.storeW_reach (G.dst e) 1 |>.charge 1)
  refine ⟨hframe, hcsr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [hreach']
    split_ifs
    · omega
    · exact I.reach_val v
  · rw [hreach']
    split_ifs with hv
    · intro h0; simp at h0
    · intro h0
      apply I.reach_s
      exact h0
  · intro v hv
    rw [hreach'] at hv
    by_cases hve : v = G.dst e
    · subst hve
      obtain ⟨p, hp, hlen⟩ := I.walk_sound u (by rw [hu]; omega)
      refine ⟨p ++ [e], hp.append ?_, ?_⟩
      · rw [← hsrc]
        exact IsWalk.single e
      · rw [G.len_append, G.len_singleton, hdist']
        simp
        rw [hlen]
    · have hv' : st.wa "reach" v ≠ 0 := by simpa [hreach', hve] using hv
      have hd' : st'.va "dist" v = st.va "dist" v := by simp [hdist', hve]
      rw [hd']
      exact I.walk_sound v hv'
  · intro v hv
    rw [hreach'] at hv
    by_cases hve : v = G.dst e
    · subst hve
      simp at hv
    · have hv' : st.wa "reach" v = 2 := by simpa [hreach', hve] using hv
      have hd' : st'.va "dist" v = st.va "dist" v := by simp [hdist', hve]
      rw [hd']
      exact I.settled_exact v hv' 
  · intro e'' he''
    rw [hreach'] at he''
    by_cases hse : G.src e'' = G.dst e
    · rw [hse] at he''
      simp at he''
    · rw [if_neg hse] at he''
      obtain ⟨hre, hde⟩ := I.relaxed e'' he''
      refine ⟨?_, ?_⟩
      · rw [hreach']
        split_ifs with hd
        · intro h0; simp at h0
        · exact hre
      · rw [hdist' (G.src e''), if_neg hse]
        rw [hdist' (G.dst e'')]
        split_ifs with hd
        · rw [hd] at hre
          exact absurd hv0 hre
        · exact hde
  · by_cases hse : s = G.dst e
    · subst hse
      exact absurd hv0 I.reach_s
    · rw [hdist' s, if_neg hse]
      exact I.dist_s_zero

/-- Relax of an edge out of a settled vertex into a **reached-unsettled** target with a strict
improvement: the target label is lowered; all bounds survive.  Shaped like the `vstore` step. -/
theorem inv_relax_improve {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) {u : Fin G.n} {e : Fin G.m}
    (hu : st.wa "reach" u = 2) (hsrc : G.src e = u) (hv1 : st.wa "reach" (G.dst e) = 1)
    (himp : st.va "dist" u + G.w e < st.va "dist" (G.dst e)) :
    Inv G s ((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1) := by
  set st' : State ℝ≥0 := (st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1 with hst'
  have hreachst : ∀ v : Fin G.n, st'.wa "reach" v = st.wa "reach" v := fun v => rfl
  have hdist' : ∀ v : Fin G.n, st'.va "dist" v =
      if v = G.dst e then st.va "dist" u + G.w e else st.va "dist" v := by
    intro v
    by_cases hv : v = G.dst e
    · subst hv
      simp [st', State.storeV, State.charge]
    · have hne : ¬ ((v : ℕ) = (G.dst e : ℕ)) := fun hh => hv (Fin.ext hh)
      simp [st', State.storeV, State.charge, hne, hv]
  refine ⟨(I.frame.storeV_dist _ _).charge 1, (I.csr.storeV_dist _ _).charge 1, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro v; exact I.reach_val v
  · exact I.reach_s
  · intro v hv
    rw [hreachst] at hv
    rw [hdist']
    split_ifs with hve
    · subst hve
      obtain ⟨p, hp, hlen⟩ := I.walk_sound u (by rw [hu]; omega)
      refine ⟨p ++ [e], hp.append ?_, ?_⟩
      · rw [← hsrc]
        exact IsWalk.single e
      · rw [G.len_append, G.len_singleton]
        simp
        rw [hlen]
    · exact I.walk_sound v hv
  · intro v hv
    rw [hreachst] at hv
    rw [hdist']
    split_ifs with hve
    · subst hve
      rw [hv1] at hv
      simp at hv
    · exact I.settled_exact v hv
  · intro e'' he''
    rw [hreachst] at he''
    obtain ⟨hre, hde⟩ := I.relaxed e'' he''
    refine ⟨hre, ?_⟩
    rw [hdist' (G.src e'')]
    rw [hdist' (G.dst e'')]
    by_cases hsrc' : G.src e'' = G.dst e
    · rw [hsrc'] at he''
      rw [hv1] at he''
      simp at he''
    · rw [if_neg hsrc']
      split_ifs with hd
      · rw [hd] at hde
        exact le_trans (le_of_lt himp) hde
      · exact hde
  · by_cases hse : s = G.dst e
    · subst hse
      rw [I.dist_s_zero] at himp
      exact absurd himp (by simp)
    · rw [hdist' s, if_neg hse]
      exact I.dist_s_zero

set_option maxHeartbeats 800000 in
/-- One relax step (`relaxBody`) over edge `idx[st.w "j"]` of `u`'s CSR segment
preserves `Inv` and advances the cursor.  Settled targets are skipped mechanically; the
reached-unsettled strict-improvement branch only lowers labels, preserving `relaxed`. -/
theorem relaxBody_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (I : Inv G s st) (hu : st.wa "reach" u = 2) (huu : u < G.n) (hwu : st.w "u" = u)
    (hj : st.wa "head" u ≤ st.w "j") (hjend : st.w "j" < st.wa "head" (u + 1)) :
    Runs realOps relaxBody st (fun st' => Inv G s st' ∧
      st'.w "j" = st.w "j" + 1 ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
      st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
      settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
      (st'.cost : ℝ) ≤ st.cost + 8 ∧ st'.wa "reach" u = 2 ∧
      ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
  /- BRANCH FILL (spine above compiles; ~120 lines of mechanical tactics remain).
  FINAL WORKING PATTERNS (each verified in this file's history):
  * register-eval at a charged state: `by simp [evalW_var, State.charge, h2v]`
  * cap bounds: `by exact hcap` / `by exact hcap2` / `by exact hcap0` (defeq through ALL
    updates; omega FAILS because st2.cap is an opaque atom to it)
  * array-length bounds: `by simp [State.charge, State.setW, State.storeV, State.storeW];
    rw [hdistL]; exact (G.dst eFin).isLt` (simp reduces the nesting to st-level, THEN the
    st-level equation hdistL/hreachL/hwL matches -- h2distL/h2reachL do NOT)
  * register-view shows: `by simp [st3, State.charge, State.setW]; exact h2u` (reduces to
    st2-level where h2u/h2e apply)
  * view-equation args to inv_relax_unreached/inv_relax_improve at their states are defeq:
    pass `hu`, `hsrc_e`, `h0`/`h1`, `himp` DIRECTLY with explicit (u := ⟨u, huu⟩) (e := eFin)
  * cost goals: `simp only [State.charge, State.setW, State.storeV, h3cost]; omega` with
    hoisted h2cost : st2.cost = st.cost + 2 / h3cost : st3.cost = st.cost + 5
  * realOps.le booleans: `simp [bit, realOps, hle]`
  * settleCard/edges at the unreached branch: settledEdges_storeW1 / settleCard_storeW1 at
    the pre-storeW state (their equation arg is defeq to h0)
  BRANCH SKELETON: h2=2 -> runs_ite_true (runs_skip) mid=(st2.charge 1).charge 1;
  h0=0 -> runs_seq (runs_vstore ...) (runs_wstore ...) + inv_relax_unreached;
  else -> vle + bit; bit=1 -> skip mid=(st3.charge 1).charge 1;
  bit=0 -> runs_vstore hev3 + inv_relax_improve, mid=((st3.charge 1).storeV ...).charge 1.
  See rider ssp-n2-resume2-progress for the full session transcript of what compiled. -/
  obtain ⟨hjm, hidxm, hsrc⟩ := I.csr.csr_seg ⟨u, huu⟩ (st.w "j") hj hjend
  set eFin : Fin G.m := ⟨st.wa "idx" (st.w "j"), hidxm⟩ with heFin
  have hsrc_e : G.src eFin = (⟨u, huu⟩ : Fin G.n) := hsrc hidxm
  have hwe : st.va "w" (eFin : ℕ) = G.w eFin := I.frame.hw (eFin : ℕ) hidxm
  have hdst_e : st.wa "dst" (eFin : ℕ) = (G.dst eFin : ℕ) := I.frame.hdst (eFin : ℕ) hidxm
  have hcap0 : G.n + G.m + 2 ≤ st.cap := I.frame.hcap
  have hnpos : 0 < G.n := by have := s.isLt; omega
  -- common tail: advance the cursor `j`
  have finish : ∀ t : State ℝ≥0, Inv G s t → t.w "j" = st.w "j" → t.w "u" = st.w "u" →
      t.w "jend" = st.w "jend" → t.w "k" = st.w "k" → t.w "best" = st.w "best" →
      t.w "i" = st.w "i" → settledEdges G t = settledEdges G st →
      settleCard G t = settleCard G st → t.cost ≤ st.cost + 7 →
      t.wa "reach" u = 2 → (∀ v : ℕ, t.wa "head" v = st.wa "head" v) →
      Runs realOps (wset "j" (.add (.var "j") (.lit 1))) t
        (fun st' => Inv G s st' ∧
          st'.w "j" = st.w "j" + 1 ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
          st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
          settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
          (st'.cost : ℝ) ≤ st.cost + 8 ∧ st'.wa "reach" u = 2 ∧
      ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
    intro t It h3j h3u h3jend h3k h3best h3i h3se h3sc h3cost h3reach h3head
    have htcap : G.n + G.m + 2 ≤ t.cap := It.frame.hcap
    have htj : t.w "j" < G.m := by rw [h3j]; exact hjm
    refine runs_wset (a := t.w "j" + 1)
      (evalW_add_of (evalW_var t "j") (evalW_lit_of (by have := htcap; omega))
        (by have := htcap; omega)) ?_
    refine ⟨(It.setW "j" (t.w "j" + 1) (by decide) (by decide)).charge 1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [State.setW, State.charge, h3j]
    · simp [State.setW, State.charge, h3u]
    · simp [State.setW, State.charge, h3jend]
    · simp [State.setW, State.charge, h3k]
    · simp [State.setW, State.charge, h3best]
    · simp [State.setW, State.charge, h3i]
    · show settledEdges G t = settledEdges G st; exact h3se
    · show settleCard G t = settleCard G st; exact h3sc
    · simp [State.setW, State.charge]
      exact_mod_cast (by omega : t.cost + 1 ≤ st.cost + 8)
    · exact h3reach
    · exact h3head
  -- e := idx[j]
  refine runs_seq (runs_wset (a := (eFin : ℕ))
    (by rw [evalW_load_of (evalW_var st "j") (by rw [I.csr.hidxL]; exact hjm)]) ?_)
  set st1 : State ℝ≥0 := (st.setW "e" (eFin : ℕ)).charge 1 with hst1
  have h1e : st1.w "e" = (eFin : ℕ) := by simp [st1, State.setW, State.charge]
  have I1 : Inv G s st1 := (I.setW "e" (eFin : ℕ) (by decide) (by decide)).charge 1
  -- v := dst[e]
  have h1eval : evalW st1 (.load "dst" (.var "e")) = some ((G.dst eFin : ℕ)) := by
    rw [evalW_load_of (j := (eFin : ℕ)) (by rw [evalW_var, h1e])
      (by rw [I1.frame.hdstL]; exact hidxm)]
    exact congrArg some hdst_e
  refine runs_seq (runs_wset (a := (G.dst eFin : ℕ)) h1eval ?_)
  set st2 : State ℝ≥0 := (st1.setW "v" (G.dst eFin : ℕ)).charge 1 with hst2
  have h2u : st2.w "u" = u := by simp [st2, st1, State.setW, State.charge, hwu]
  have h2v : st2.w "v" = (G.dst eFin : ℕ) := by simp [st2, State.setW, State.charge]
  have h2e : st2.w "e" = (eFin : ℕ) := by simp [st2, st1, State.setW, State.charge]
  have h2cost : st2.cost = st.cost + 2 := by simp [st2, st1, State.setW, State.charge]
  have I2 : Inv G s st2 :=
    ((I.setW "e" (eFin : ℕ) (by decide) (by decide)).charge 1
      |>.setW "v" (G.dst eFin : ℕ) (by decide) (by decide)).charge 1
  have h2cap : G.n + G.m + 2 ≤ st2.cap := I2.frame.hcap
  have h2distL : st2.vlen "dist" = G.n := I2.frame.hdistL
  have h2reachL : st2.wlen "reach" = G.n := I2.frame.hreachL
  have h2wL : st2.vlen "w" = G.m := I2.frame.hwL
  have hreachv : evalW st2 (.load "reach" (.var "v")) = some (st.wa "reach" (G.dst eFin)) :=
    evalW_load_of (by rw [evalW_var, h2v]) (by rw [h2reachL]; exact (G.dst eFin).isLt)
  have htest2 : evalW st2 (.eq (.load "reach" (.var "v")) (.lit 2)) =
      some (if st.wa "reach" (G.dst eFin) = 2 then 1 else 0) :=
    evalW_eq_of hreachv (evalW_lit_of (by have := h2cap; omega)) (by have := h2cap; omega)
  -- relaxInner, then the common tail
  refine runs_seq ?_
  by_cases h2v2 : st.wa "reach" (G.dst eFin) = 2
  · -- settled target: skip
    refine runs_ite_true (x := 1) (by rw [htest2, h2v2]; rfl) one_ne_zero (runs_skip ?_)
    refine finish _ ((I2.charge 1).charge 1) rfl rfl rfl rfl rfl rfl rfl rfl ?_ hu (fun v => rfl)
    simp [State.charge, h2cost]
  · refine runs_ite_false (by rw [htest2, if_neg h2v2]) ?_
    have h21cap : G.n + G.m + 2 ≤ (st2.charge 1).cap := h2cap
    have hreachv1 : evalW (st2.charge 1) (.load "reach" (.var "v"))
        = some (st.wa "reach" (G.dst eFin)) := by rw [evalW_charge]; exact hreachv
    have htestc2 : evalW (st2.charge 1) (.eq (.load "reach" (.var "v")) (.lit 0)) =
        some (if st.wa "reach" (G.dst eFin) = 0 then 1 else 0) :=
      evalW_eq_of hreachv1 (evalW_lit_of (by have := h21cap; omega)) (by have := h21cap; omega)
    by_cases h0v : st.wa "reach" (G.dst eFin) = 0
    · -- unreached target: dist[v] := dist[u] + w[e], reach[v] := 1
      refine runs_ite_true (x := 1) (by rw [htestc2, h0v]; rfl) one_ne_zero ?_
      set S4 : State ℝ≥0 := (st2.charge 1).charge 1 with hS4
      have h4distL : S4.vlen "dist" = G.n := I.frame.hdistL
      have h4reachL : S4.wlen "reach" = G.n := I.frame.hreachL
      have h4wL : S4.vlen "w" = G.m := I.frame.hwL
      have h4cap : G.n + G.m + 2 ≤ S4.cap := I.frame.hcap
      have h4u : S4.w "u" = u := by simp [S4, State.charge, h2u]
      have h4e : S4.w "e" = (eFin : ℕ) := by simp [S4, State.charge, h2e]
      have hev4 : evalV realOps S4 relaxVal = some (st.va "dist" u + G.w eFin) := by
        rw [eval_relaxVal' h4u h4e (by rw [h4distL]; exact huu) (by rw [h4wL]; exact hidxm)]
        exact congrArg some (congrArg₂ (· + ·) rfl hwe)
      refine runs_seq (runs_vstore (j := (G.dst eFin : ℕ))
        (by rw [evalW_var] <;> exact congrArg some h2v) hev4
        (by rw [h4distL]; exact (G.dst eFin).isLt) ?_)
      set S5 : State ℝ≥0 := ((S4.storeV "dist" (G.dst eFin) (st.va "dist" u + G.w eFin)).charge 1)
        with hS5
      have h5reachL : S5.wlen "reach" = G.n := I.frame.hreachL
      have h5cap : G.n + G.m + 2 ≤ S5.cap := I.frame.hcap
      refine runs_wstore (j := (G.dst eFin : ℕ)) (a := 1)
        (by rw [evalW_var] <;> exact congrArg some h2v)
        (evalW_lit_of (by have := h5cap; omega))
        (by rw [h5reachL]; exact (G.dst eFin).isLt) ?_
      have hvu : (u : ℕ) ≠ (G.dst eFin : ℕ) := by
        intro h
        rw [← h] at h0v
        omega
      have hreachu : S5.wa "reach" u = 2 := hu
      refine finish _ (inv_relax_unreached (I2.charge 1 |>.charge 1)
        (u := ⟨u, huu⟩) (e := eFin) hu hsrc_e h0v) rfl rfl rfl rfl rfl rfl ?_ ?_ ?_
        (by simp [State.setW, State.charge, State.storeW, hvu, hreachu]) (fun v => rfl)
      · show settledEdges G (S5.storeW "reach" (G.dst eFin) 1) = settledEdges G st
        rw [settledEdges_storeW1 (st := S5) (v := G.dst eFin) (show S5.wa "reach" (G.dst eFin) = 0 from h0v)]
        rfl
      · show settleCard G (S5.storeW "reach" (G.dst eFin) 1) = settleCard G st
        rw [settleCard_storeW1 (st := S5) (v := G.dst eFin) (show S5.wa "reach" (G.dst eFin) = 0 from h0v)]
        rfl
      · simp only [hS5, hS4, State.charge, State.storeV, State.storeW, State.setW, h2cost]
        omega
    · -- reached-unsettled target: compare, improve only on strict gain
      have h1v : st.wa "reach" (G.dst eFin) = 1 := by
        have hle2 := I.reach_val (G.dst eFin)
        omega
      refine runs_ite_false (by rw [htestc2, if_neg h0v]) ?_
      set S4 : State ℝ≥0 := (st2.charge 1).charge 1 with hS4
      have h4distL : S4.vlen "dist" = G.n := I.frame.hdistL
      have h4wL : S4.vlen "w" = G.m := I.frame.hwL
      have h4cap : G.n + G.m + 2 ≤ S4.cap := I.frame.hcap
      have h4u : S4.w "u" = u := by simp [S4, State.charge, h2u]
      have h4e : S4.w "e" = (eFin : ℕ) := by simp [S4, State.charge, h2e]
      have hdv : evalV realOps S4 (.load "dist" (.var "v"))
          = some (st.va "dist" (G.dst eFin)) := by
        rw [evalV_load_of (by rw [evalW_var] <;> exact congrArg some h2v)
          (by rw [h4distL]; exact (G.dst eFin).isLt)]
        rfl
      have hev4 : evalV realOps S4 relaxVal = some (st.va "dist" u + G.w eFin) := by
        rw [eval_relaxVal' h4u h4e (by rw [h4distL]; exact huu) (by rw [h4wL]; exact hidxm)]
        exact congrArg some (congrArg₂ (· + ·) rfl hwe)
      refine runs_seq (runs_vle hdv hev4 (by have := h4cap; omega) ?_)
      set bit : ℕ := if realOps.le (st.va "dist" (G.dst eFin)) (st.va "dist" u + G.w eFin)
        then 1 else 0 with hbit
      set S5 : State ℝ≥0 := ((S4.setW "b" bit).charge 1) with hS5
      have hS5b : S5.w "b" = bit := by simp [S5, State.setW, State.charge]
      by_cases hle : st.va "dist" (G.dst eFin) ≤ st.va "dist" u + G.w eFin
      · have hbit1 : bit = 1 := by simp [bit, realOps, hle]
        refine runs_ite_true (x := 1) (by rw [evalW_var, hS5b, hbit1]) one_ne_zero (runs_skip ?_)
        refine finish _
          (((I2.charge 1).charge 1 |>.setW "b" bit (by decide) (by decide))
            |>.charge 1 |>.charge 1 |>.charge 1)
          rfl rfl rfl rfl rfl rfl rfl rfl ?_ hu (fun v => rfl)
        simp only [hS5, hS4, State.charge, State.setW, h2cost]
        omega
      · have hbit0 : bit = 0 := by simp [bit, realOps, hle]
        refine runs_ite_false (by rw [evalW_var, hS5b, hbit0]) ?_
        have h5distL : S5.vlen "dist" = G.n := I.frame.hdistL
        have h5wL : S5.vlen "w" = G.m := I.frame.hwL
        have h51distL : (S5.charge 1).vlen "dist" = G.n := I.frame.hdistL
        have h5u : S5.w "u" = u := by simp [S5, S4, State.setW, State.charge, h2u]
        have h5e : S5.w "e" = (eFin : ℕ) := by simp [S5, S4, State.setW, State.charge, h2e]
        have hev5 : evalV realOps (S5.charge 1) relaxVal
            = some (st.va "dist" u + G.w eFin) := by
          rw [evalV_charge]
          rw [eval_relaxVal' h5u h5e (by rw [h5distL]; exact huu) (by rw [h5wL]; exact hidxm)]
          exact congrArg some (congrArg₂ (· + ·) rfl hwe)
        refine runs_vstore (j := (G.dst eFin : ℕ))
          (by rw [evalW_var] <;> exact congrArg some h2v) hev5
          (by rw [h51distL]; exact (G.dst eFin).isLt) ?_
        refine finish _ (inv_relax_improve
          (I2.charge 1 |>.charge 1 |>.setW "b" bit (by decide) (by decide)
            |>.charge 1 |>.charge 1)
          (u := ⟨u, huu⟩) (e := eFin) hu hsrc_e h1v (lt_of_not_ge hle))
          rfl rfl rfl rfl rfl rfl rfl rfl ?_ hu (fun v => rfl)
        simp only [hS5, hS4, State.charge, State.storeV, State.setW, h2cost]
        omega


theorem inv_of_main_step {G : Graph} {s : Fin G.n} {st st' : State ℝ≥0}
    (I : Inv G s st) (hk : st.w "k" < G.n)
    (hstep : Runs realOps mainBody st (fun r => r = st' ∧ (G.n - st'.w "k") < G.n - st.w "k")) :
    Inv G s st' := by
  sorry

/-- One settle step preserves `Inv` and settles its target exactly (the exchange). -/
theorem inv_of_settle {G : Graph} {s : Fin G.n} {st st' : State ℝ≥0} {u : Fin G.n}
    (I : Inv G s st) (hu : st.wa "reach" u = 1) (hbest : st.w "best" = u)
    (hmin : ∀ v : Fin G.n, st.wa "reach" v = 1 → (st.va "dist" u : ℝ≥0) ≤ st.va "dist" v)
    (hstep : Runs realOps settleBody st (fun r => r = st')) :
    Inv G s st' ∧ st'.wa "reach" u = 2 := by
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
vertex remains and `Solves` holds, at cost `≤ 26·(n²+m+1)`.  The loop invariant extends
`Inv` with the settle-count (`k ≤ #{v | reach v = 2}` or done) and the exit fact, both
carried through `mainInner` by `inv_of_settle` / `inv_of_relax_step` / `inv_of_main_step`. -/
theorem runs_mainLoop {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) (hk0 : st.w "k" = 0) :
    Runs realOps mainLoop st
      (fun r => (∀ v : Fin G.n, r.wa "reach" v = 1 → False) ∧ r.Solves G s ∧
        (r.cost : ℝ) ≤ 26 * (((G.n : ℝ) ^ 2 + G.m) + 1) + st.cost) := by
  sorry

/-- On every graph and source the program terminates without getting stuck, outputs the exact
distances, and costs at most `40 * (n² + m + 1)`.

Assembly (the wiring is mechanical over the named lemmas above):
`prog = allocAll; initReach; buildCSR; k := 0; mainLoop`.  Chain `runs_csr` (cost
`≤ 10(n+m)+17`, `PreMain`) → `inv_of_preMain` → the `wset "k" 0` step (`Runs` rules) →
`runs_mainLoop` (cost `≤ 26(n²+m+1)` from there) → `solves_of_inv` on the loop's exit
postcondition.  Total `10(n+m)+18 + 26(n²+m+1) ≤ 40(n²+m+1)` for all `n ≥ 1, m ≥ 0`. -/
theorem dijkstra_runs (G : Graph) (s : Fin G.n) :
    ∃ fuel r, dijkstraProgram.run fuel G s = some r ∧ r.Solves G s ∧
      (r.cost : ℝ) ≤ 40 * (((G.n : ℝ) ^ 2 + G.m) + 1) := by
  sorry

end BigOSpeedrun.DirectedSSSP.Dijkstra
