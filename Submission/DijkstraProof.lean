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

/-! ## The sweep invariant (R2125608238 redesign)

`settleBody` stores `reach u = 2` BEFORE relaxing `u`'s out-edges one at a time, so the
global `Inv.relaxed` does not hold at the pre-sweep state (`walk_sound` bounds reach-1
labels only from above) and the Inv→Inv sims `relaxBody_runs`/`relaxLoop_runs` cannot be
applied to the settle sweep.  `SweepInv` weakens `relaxed` to (a) edges out of reach-2
sources other than `u`, and (b) `u`'s already-swept out-edges — CSR segment positions
`q ∈ [head u, cursor)`.  `SweepInv.toInv` collapses it back to `Inv` once the cursor
reaches `head (u + 1)`.
-/

/-- The relaxation obligation for one edge out of `u`. -/
def EdgeRelaxed (G : Graph) (st : State ℝ≥0) (u : ℕ) (e : Fin G.m) : Prop :=
  st.wa "reach" (G.dst e) ≠ 0 ∧
    (st.va "dist" (G.dst e) : ℝ≥0) ≤ st.va "dist" u + G.w e

/-- Sweep invariant of the settle sweep, at the relax cursor `st.w "j"`.  Identical to
`Inv` except for `relaxed`, which is required only for reach-2 sources `≠ u` and for `u`'s
out-edges at already-swept segment positions `q < st.w "j"`. -/
structure SweepInv (G : Graph) (s : Fin G.n) (u : ℕ) (st : State ℝ≥0) : Prop where
  frame : Frontier.RAM.BF.Frame G st
  csr : CSRPart G st
  reach_val : ∀ v : Fin G.n, st.wa "reach" v ≤ 2
  reach_s : st.wa "reach" s ≠ 0
  reach_u : st.wa "reach" u = 2
  cursor_ge : st.wa "head" u ≤ st.w "j"
  cursor_le : st.w "j" ≤ st.wa "head" (u + 1)
  walk_sound : ∀ v : Fin G.n, st.wa "reach" v ≠ 0 →
    ∃ p, G.IsWalk s v p ∧ G.len p = st.va "dist" v
  settled_exact : ∀ v : Fin G.n, st.wa "reach" v = 2 →
    ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) = G.dist s v
  relaxed_other : ∀ e : Fin G.m, (G.src e : ℕ) ≠ u → st.wa "reach" (G.src e) = 2 →
    st.wa "reach" (G.dst e) ≠ 0 ∧
    (st.va "dist" (G.dst e) : ℝ≥0) ≤ st.va "dist" (G.src e) + G.w e
  relaxed_swept : ∀ q : ℕ, st.wa "head" u ≤ q → q < st.w "j" →
    ∀ hq : q < G.m, ∀ hidx : st.wa "idx" q < G.m,
      EdgeRelaxed G st u ⟨st.wa "idx" q, hidx⟩
  dist_s_zero : st.va "dist" s = 0

theorem SweepInv.setW {G : Graph} {s : Fin G.n} {u : ℕ} {st : State ℝ≥0}
    (S : SweepInv G s u st) (x : String) (a : ℕ)
    (hxn : x ≠ "n") (hxm : x ≠ "m") (hxj : x ≠ "j") : SweepInv G s u (st.setW x a) := by
  obtain ⟨hfr, hcsr, hrv, hrs, hru, hcg, hcl, hws, hse, hro, hrs2, hds⟩ := S
  refine ⟨hfr.setW hxn hxm a, hcsr.setW x a, hrv, hrs, hru, ?_, ?_, hws, hse, hro, ?_, hds⟩
  · simpa [State.setW, Ne.symm hxj] using hcg
  · simpa [State.setW, Ne.symm hxj] using hcl
  · intro q h1 h2 hq hidx
    have h2' : q < st.w "j" := by rwa [show (st.setW x a).w "j" = st.w "j" by
      simp [State.setW, Ne.symm hxj]] at h2
    exact hrs2 q h1 h2' hq hidx

theorem SweepInv.charge {G : Graph} {s : Fin G.n} {u : ℕ} {st : State ℝ≥0}
    (S : SweepInv G s u st) (k : ℕ) : SweepInv G s u (st.charge k) := by
  obtain ⟨hfr, hcsr, hrv, hrs, hru, hcg, hcl, hws, hse, hro, hrs2, hds⟩ := S
  exact ⟨hfr.charge k, hcsr.charge k, hrv, hrs, hru, hcg, hcl, hws, hse, hro, hrs2, hds⟩

/-- The cursor advance of `relaxBody`'s tail: once the edge at position `j` is relaxed,
`wset "j" (j+1)` extends the swept segment by one position. -/
theorem SweepInv.advance {G : Graph} {s : Fin G.n} {u : ℕ} {st : State ℝ≥0}
    (S : SweepInv G s u st) (huu : u < G.n)
    (hcur : st.w "j" < st.wa "head" (u + 1))
    (hedge : ∀ hidx : st.wa "idx" (st.w "j") < G.m,
      EdgeRelaxed G st u ⟨st.wa "idx" (st.w "j"), hidx⟩) :
    SweepInv G s u (st.setW "j" (st.w "j" + 1)) := by
  obtain ⟨hfr, hcsr, hrv, hrs, hru, hcg, hcl, hws, hse, hro, hrs2, hds⟩ := S
  refine ⟨hfr.setW (by decide) (by decide) (st.w "j" + 1), hcsr.setW "j" (st.w "j" + 1),
    hrv, hrs, hru, ?_, ?_, hws, hse, hro, ?_, hds⟩
  · simp [State.setW]
    omega
  · simp [State.setW]
    omega
  · intro q h1 h2 hq hidx
    have hqj : q < st.w "j" ∨ q = st.w "j" := by
      have h2' : q < st.w "j" + 1 := by
        rwa [show (st.setW "j" (st.w "j" + 1)).w "j" = st.w "j" + 1 by simp [State.setW]] at h2
      omega
    rcases hqj with hqj | hqj
    · exact hrs2 q h1 hqj hq hidx
    · subst hqj
      exact hedge hidx

/-- Sweep-end collapse: once the cursor reaches `head (u+1)` every out-edge of `u` is
swept (`csr_cover`), so `SweepInv` upgrades to the full `Inv`. -/
theorem SweepInv.toInv {G : Graph} {s : Fin G.n} {u : ℕ} {st : State ℝ≥0}
    (S : SweepInv G s u st) (huu : u < G.n) (hjend : st.w "j" = st.wa "head" (u + 1)) :
    Inv G s st := by
  obtain ⟨hfr, hcsr, hrv, hrs, hru, hcg, hcl, hws, hse, hro, hrs2, hds⟩ := S
  refine ⟨hfr, hcsr, hrv, hrs, hws, hse, ?_, hds⟩
  intro e he
  by_cases hne : (G.src e : ℕ) = u
  · -- `e` is one of `u`'s out-edges: `csr_cover` places it at some swept position `q`
    obtain ⟨q, hq1, hq2, hq3⟩ := hcsr.csr_cover e
    have hq1' : st.wa "head" u ≤ q := by rwa [hne] at hq1
    have hq2' : q < st.w "j" := by
      rw [hjend]
      rwa [hne] at hq2
    obtain ⟨hlt, hidx, -⟩ := hcsr.csr_seg ⟨u, huu⟩ q hq1'
      (by show q < st.wa "head" (u + 1); rw [← hjend]; exact hq2')
    have heq : (⟨st.wa "idx" q, hidx⟩ : Fin G.m) = e :=
      Fin.ext (show (st.wa "idx" q : ℕ) = ↑e from hq3)
    have hE := hrs2 q hq1' hq2' hlt hidx
    rw [heq] at hE
    have hE' : st.wa "reach" (G.dst e) ≠ 0 ∧
        (st.va "dist" (G.dst e) : ℝ≥0) ≤ st.va "dist" u + G.w e := hE
    exact ⟨hE'.1, by rw [hne]; exact hE'.2⟩
  · exact hro e hne he

/-! ## Sweep-invariant relax sims (statement + design; fills follow)

Each mirrors its `Inv` counterpart (`inv_relax_unreached` / `inv_relax_improve` /
`relaxBody_runs` / `relaxLoop_runs`) with `SweepInv` in place of `Inv`.  REUSE MAP:
the branch structure, state-chains and finish-helper of `relaxBody_runs` below transfer
verbatim (its three branches already carry the exact simp/rw spines); the only new
obligations are `relaxed_swept`'s one-position extension, discharged through
`SweepInv.advance` + `EdgeRelaxed`, and `relaxed_other`, whose preservation argument is
byte-identical to the `relaxed` field proof in `inv_relax_unreached`/`inv_relax_improve`
(the written vertex `v` has `reach v ∈ {0, 1}` post-step, so no reach-2 source other than
`u` can point at it vacuously — exactly the `hse` case-split there). -/

set_option maxHeartbeats 800000 in
/-- Sweep variant of `inv_relax_unreached` (cursor unchanged): the written vertex `v`
was unreached, so no already-swept `u`-edge and no reach-2 source `≠ u` targets it —
both kinds of obligation already assert their target's `reach ≠ 0`.  The two `relaxed`
fields are therefore unchanged apart from the fresh `EdgeRelaxed e`, which
`SweepInv.advance` consumes at the tail of `relaxBody`. -/
theorem sweep_inv_relax_unreached {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (SW : SweepInv G s u st) {e : Fin G.m} (hsrc : (G.src e : ℕ) = u)
    (hv0 : st.wa "reach" (G.dst e) = 0) :
    SweepInv G s u ((((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1)
      |>.storeW "reach" (G.dst e) 1).charge 1) := by
  set st' : State ℝ≥0 := ((((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1)
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
  have hune : u ≠ (G.dst e : ℕ) := by
    intro hh
    rw [← hh] at hv0
    have h2 := SW.reach_u
    omega
  have hru : st'.wa "reach" u = st.wa "reach" u := by
    simp [st', State.storeW, State.storeV, State.charge, hune]
  have hdu : st'.va "dist" u = st.va "dist" u := by
    simp [st', State.storeW, State.storeV, State.charge, hune]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((SW.frame.storeV_dist (G.dst e) (st.va "dist" u + G.w e)).charge 1
      |>.storeW_reach (G.dst e) 1 |>.charge 1)
  · exact ((SW.csr.storeV_dist (G.dst e) (st.va "dist" u + G.w e)).charge 1
      |>.storeW_reach (G.dst e) 1 |>.charge 1)
  · intro v
    rw [hreach']
    split_ifs
    · omega
    · exact SW.reach_val v
  · rw [hreach']
    split_ifs with hv
    · intro h0; simp at h0
    · exact SW.reach_s
  · rw [hru]
    exact SW.reach_u
  · exact SW.cursor_ge
  · exact SW.cursor_le
  · intro v hv
    rw [hreach'] at hv
    by_cases hve : v = G.dst e
    · subst hve
      obtain ⟨p, hp, hlen⟩ := SW.walk_sound (G.src e) (by
        rw [hsrc] at ⊢
        have := SW.reach_u
        omega)
      refine ⟨p ++ [e], hp.append (IsWalk.single e), ?_⟩
      have hlen' : G.len p = st.va "dist" u := by
        rw [hlen]
        exact congrArg (st.va "dist") hsrc
      rw [G.len_append, G.len_singleton, hlen']
      simp [st', State.storeW, State.storeV, State.charge]
    · have hv' : st.wa "reach" v ≠ 0 := by simpa [hreach', hve] using hv
      have hd' : st'.va "dist" v = st.va "dist" v := by simp [hdist', hve]
      rw [hd']
      exact SW.walk_sound v hv'
  · intro v hv
    rw [hreach'] at hv
    by_cases hve : v = G.dst e
    · subst hve
      simp at hv
    · have hv' : st.wa "reach" v = 2 := by simpa [hreach', hve] using hv
      have hd' : st'.va "dist" v = st.va "dist" v := by simp [hdist', hve]
      rw [hd']
      exact SW.settled_exact v hv'
  · -- relaxed_other: the written vertex cannot be targeted by a reach-2 source ≠ u,
    -- since that obligation already forced its target's reach away from 0
    intro e'' hne_u he''
    rw [hreach'] at he''
    by_cases hse : G.src e'' = G.dst e
    · rw [hse] at he''
      simp at he''
    · rw [if_neg hse] at he''
      obtain ⟨hre, hde⟩ := SW.relaxed_other e'' hne_u he''
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
  · -- relaxed_swept: old swept targets were never the unreached vertex
    intro q h1 h2 hq hidx
    obtain ⟨hre, hde⟩ := SW.relaxed_swept q h1 h2 hq hidx
    refine ⟨?_, ?_⟩
    · show st'.wa "reach" (G.dst ⟨st.wa "idx" q, hidx⟩) ≠ 0
      rw [hreach']
      by_cases hd : G.dst ⟨st.wa "idx" q, hidx⟩ = G.dst e
      · rw [hd] at hre
        exact absurd hv0 hre
      · rw [if_neg hd]
        exact hre
    · show (st'.va "dist" (G.dst ⟨st.wa "idx" q, hidx⟩) : ℝ≥0) ≤
        st'.va "dist" u + G.w ⟨st.wa "idx" q, hidx⟩
      rw [hdist' (G.dst ⟨st.wa "idx" q, hidx⟩)]
      by_cases hd : G.dst ⟨st.wa "idx" q, hidx⟩ = G.dst e
      · rw [hd] at hre
        exact absurd hv0 hre
      · rw [if_neg hd, hdu]
        exact hde
  · rw [hdist' s]
    by_cases hse : (s : Fin G.n) = G.dst e
    · rw [if_pos hse]
      rw [← hse] at hv0
      exact absurd hv0 SW.reach_s
    · rw [if_neg hse]
      exact SW.dist_s_zero

/-- Sweep variant of `inv_relax_improve` (cursor unchanged): the strict-improvement
write only lowers the reached-unsettled target's label, so both `relaxed` fields
survive (every bound is monotone in the lowered label) and the fresh `EdgeRelaxed e`
holds with equality. -/
theorem sweep_inv_relax_improve {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (SW : SweepInv G s u st) {e : Fin G.m} (hsrc : (G.src e : ℕ) = u)
    (hv1 : st.wa "reach" (G.dst e) = 1)
    (himp : st.va "dist" u + G.w e < st.va "dist" (G.dst e)) :
    SweepInv G s u ((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1) := by
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
  have hune : u ≠ (G.dst e : ℕ) := by
    intro hh
    rw [← hh] at hv1
    have h2 := SW.reach_u
    omega
  have hdu : st'.va "dist" u = st.va "dist" u := by
    simp [st', State.storeV, State.charge, hune]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (SW.frame.storeV_dist (G.dst e) (st.va "dist" u + G.w e)).charge 1
  · exact (SW.csr.storeV_dist (G.dst e) (st.va "dist" u + G.w e)).charge 1
  · intro v
    rw [hreachst]
    exact SW.reach_val v
  · rw [hreachst]
    exact SW.reach_s
  · show st.wa "reach" u = 2
    exact SW.reach_u
  · exact SW.cursor_ge
  · exact SW.cursor_le
  · intro v hv
    rw [hreachst] at hv
    rw [hdist']
    split_ifs with hve
    · subst hve
      obtain ⟨p, hp, hlen⟩ := SW.walk_sound (G.src e) (by
        rw [hsrc] at ⊢
        have := SW.reach_u
        omega)
      refine ⟨p ++ [e], hp.append (IsWalk.single e), ?_⟩
      have hlen' : G.len p = st.va "dist" u := by
        rw [hlen]
        exact congrArg (st.va "dist") hsrc
      rw [G.len_append, G.len_singleton, hlen']
    · exact SW.walk_sound v hv
  · intro v hv
    rw [hreachst] at hv
    rw [hdist']
    split_ifs with hve
    · subst hve
      rw [hv1] at hv
      simp at hv
    · exact SW.settled_exact v hv
  · -- relaxed_other: labels only lower, reach unchanged
    intro e'' hne_u he''
    rw [hreachst] at he''
    obtain ⟨hre, hde⟩ := SW.relaxed_other e'' hne_u he''
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
  · -- relaxed_swept: the lowered label keeps every old swept bound
    intro q h1 h2 hq hidx
    obtain ⟨hre, hde⟩ := SW.relaxed_swept q h1 h2 hq hidx
    refine ⟨hre, ?_⟩
    show (st'.va "dist" (G.dst ⟨st.wa "idx" q, hidx⟩) : ℝ≥0) ≤
      st'.va "dist" u + G.w ⟨st.wa "idx" q, hidx⟩
    rw [hdist' (G.dst ⟨st.wa "idx" q, hidx⟩)]
    by_cases hd : G.dst ⟨st.wa "idx" q, hidx⟩ = G.dst e
    · rw [hd] at hde
      rw [if_pos hd, hdu]
      exact le_trans (le_of_lt himp) hde
    · rw [if_neg hd, hdu]
      exact hde
  · rw [hdist' s]
    by_cases hse : (s : Fin G.n) = G.dst e
    · subst hse
      rw [SW.dist_s_zero] at himp
      exact absurd himp (by simp)
    · rw [if_neg hse]
      exact SW.dist_s_zero

/-- The fresh `EdgeRelaxed` of the unreached-target write -- the `SweepInv.advance` input. -/
theorem edgeRelaxed_unreached {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ} {e : Fin G.m}
    (SW : SweepInv G s u st) (huu : u < G.n) (hsrc : (G.src e : ℕ) = u)
    (hv0 : st.wa "reach" (G.dst e) = 0) :
    EdgeRelaxed G ((((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1)
      |>.storeW "reach" (G.dst e) 1).charge 1) u e := by
  have hune : u ≠ (G.dst e : ℕ) := by
    intro hh
    rw [← hh] at hv0
    have h2 := SW.reach_u
    omega
  refine ⟨?_, ?_⟩
  · show ((((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1)
      |>.storeW "reach" (G.dst e) 1).charge 1).wa "reach" (G.dst e) ≠ 0
    simp [State.storeW, State.charge, State.storeV]
  · show (((((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1)
      |>.storeW "reach" (G.dst e) 1).charge 1).va "dist" (G.dst e) : ℝ≥0) ≤
      ((((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1)
        |>.storeW "reach" (G.dst e) 1).charge 1).va "dist" u + G.w e
    simp [State.storeW, State.charge, State.storeV, hune]

/-- The fresh `EdgeRelaxed` of the strict-improvement write -- the `SweepInv.advance` input. -/
theorem edgeRelaxed_improve {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ} {e : Fin G.m}
    (SW : SweepInv G s u st) (huu : u < G.n) (hsrc : (G.src e : ℕ) = u)
    (hv1 : st.wa "reach" (G.dst e) = 1) :
    EdgeRelaxed G ((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1) u e := by
  have hune : u ≠ (G.dst e : ℕ) := by
    intro hh
    rw [← hh] at hv1
    have h2 := SW.reach_u
    omega
  refine ⟨?_, ?_⟩
  · show st.wa "reach" (G.dst e) ≠ 0
    rw [hv1]
    decide
  · show (((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1).va "dist" (G.dst e)
      : ℝ≥0) ≤ ((st.storeV "dist" (G.dst e) (st.va "dist" u + G.w e)).charge 1).va "dist" u + G.w e
    simp [State.storeV, State.charge, hune]

/-- A settled target's skip obligation: both labels are exact (`settled_exact`) and the
triangle inequality for the edge (`dist_edge`) supplies the bound. -/
theorem relaxed_of_settled {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ} {e : Fin G.m}
    (SW : SweepInv G s u st) (huu : u < G.n) (hsrc : (G.src e : ℕ) = u)
    (hv2 : st.wa "reach" (G.dst e) = 2) : EdgeRelaxed G st u e := by
  refine ⟨by rw [hv2]; decide, ?_⟩
  have hu2 : st.wa "reach" u = 2 := SW.reach_u
  have hde : ((st.va "dist" (G.dst e) : ℝ≥0) : ℝ≥0∞) = G.dist s (G.dst e) :=
    SW.settled_exact (G.dst e) hv2
  have hdu : ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) = G.dist s (⟨u, huu⟩ : Fin G.n) :=
    SW.settled_exact (⟨u, huu⟩ : Fin G.n)
      (show st.wa "reach" (⟨u, huu⟩ : Fin G.n) = 2 from hu2)
  have hsrc' : (G.src e) = (⟨u, huu⟩ : Fin G.n) := Fin.ext hsrc
  have htri : G.dist s (G.dst e) ≤ G.dist s (⟨u, huu⟩ : Fin G.n) + G.w e := by
    rw [← hsrc']
    exact dist_edge s e
  have hcoe : ((st.va "dist" u + G.w e : ℝ≥0) : ℝ≥0∞)
      = ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) + ((G.w e : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_add _ _
  have hfin : ((st.va "dist" (G.dst e) : ℝ≥0) : ℝ≥0∞)
      ≤ ((st.va "dist" u + G.w e : ℝ≥0) : ℝ≥0∞) := by
    rw [hcoe, hde, hdu]
    exact htri
  exact ENNReal.coe_le_coe.mp hfin

set_option maxHeartbeats 800000 in
/-- Sweep variant of one relax step (`relaxBody`) over edge `idx[st.w "j"]`: preserves
`SweepInv` and advances the cursor.  DESIGN: identical spine to `relaxBody_runs` below
(h2v2 settled-target skip / h0v unreached write / else compare-branch), with
`inv_relax_unreached` / `inv_relax_improve` swapped for the SweepInv versions
(`sweep_relax_unreached` / `sweep_relax_improve`, whose internals are the same case
analyses over `relaxed_other` + `relaxed_swept`) and the tail `wset "j"` discharged by
`SweepInv.advance` with `hedge` = the branch's own `EdgeRelaxed` fact for `eFin`. -/
theorem sweep_relaxBody_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (S : SweepInv G s u st) (huu : u < G.n) (hwu : st.w "u" = u)
    (hj : st.wa "head" u ≤ st.w "j") (hjend : st.w "j" < st.wa "head" (u + 1)) :
    Runs realOps relaxBody st (fun st' => SweepInv G s u st' ∧
      st'.w "j" = st.w "j" + 1 ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
      st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
      settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
      (st'.cost : ℝ) ≤ st.cost + 8 ∧ st'.wa "reach" u = 2 ∧
      ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
  obtain ⟨hjm, hidxm, hsrc⟩ := S.csr.csr_seg ⟨u, huu⟩ (st.w "j") hj hjend
  set eFin : Fin G.m := ⟨st.wa "idx" (st.w "j"), hidxm⟩ with heFin
  have hsrc_e : G.src eFin = (⟨u, huu⟩ : Fin G.n) := hsrc hidxm
  have hsrc_n : (G.src eFin : ℕ) = u := congrArg Fin.val hsrc_e
  have hwe : st.va "w" (eFin : ℕ) = G.w eFin := S.frame.hw (eFin : ℕ) hidxm
  have hdst_e : st.wa "dst" (eFin : ℕ) = (G.dst eFin : ℕ) := S.frame.hdst (eFin : ℕ) hidxm
  have hcap0 : G.n + G.m + 2 ≤ st.cap := S.frame.hcap
  -- common tail: `wset "j" (j+1)` -- SweepInv gains position j via the branch's EdgeRelaxed
  have finish : ∀ t : State ℝ≥0, SweepInv G s u t → t.w "j" = st.w "j" → t.w "u" = st.w "u" →
      t.w "jend" = st.w "jend" → t.w "k" = st.w "k" → t.w "best" = st.w "best" →
      t.w "i" = st.w "i" → settledEdges G t = settledEdges G st →
      settleCard G t = settleCard G st → t.cost ≤ st.cost + 7 →
      t.wa "reach" u = 2 → (∀ v : ℕ, t.wa "head" v = st.wa "head" v) →
      t.wa "idx" (t.w "j") = st.wa "idx" (st.w "j") →
      EdgeRelaxed G t u eFin →
      Runs realOps (wset "j" (.add (.var "j") (.lit 1))) t
        (fun st' => SweepInv G s u st' ∧
          st'.w "j" = st.w "j" + 1 ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
          st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
          settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
          (st'.cost : ℝ) ≤ st.cost + 8 ∧ st'.wa "reach" u = 2 ∧
      ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
    intro t It h3j h3u h3jend h3k h3best h3i h3se h3sc h3cost h3reach h3head hidxeq hedge
    have htcap : G.n + G.m + 2 ≤ t.cap := It.frame.hcap
    have hedgeAll : ∀ hidx : t.wa "idx" (t.w "j") < G.m,
        EdgeRelaxed G t u ⟨t.wa "idx" (t.w "j"), hidx⟩ := by
      intro hidx
      have : (⟨t.wa "idx" (t.w "j"), hidx⟩ : Fin G.m) = eFin := Fin.ext hidxeq
      rw [this]
      exact hedge
    refine runs_wset (a := t.w "j" + 1)
      (evalW_add_of (evalW_var t "j") (evalW_lit_of (by have := htcap; omega))
        (by have := htcap; omega)) ?_
    refine ⟨(It.advance huu (by rw [h3j, h3head (u + 1)]; exact hjend) hedgeAll).charge 1,
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
    · intro v; exact h3head v
  -- e := idx[j]
  refine runs_seq (runs_wset (a := (eFin : ℕ))
    (by rw [evalW_load_of (evalW_var st "j") (by rw [S.csr.hidxL]; exact hjm)]) ?_)
  set st1 : State ℝ≥0 := (st.setW "e" (eFin : ℕ)).charge 1 with hst1
  have h1e : st1.w "e" = (eFin : ℕ) := by simp [st1, State.setW, State.charge]
  have S1 : SweepInv G s u st1 :=
    (S.setW "e" (eFin : ℕ) (by decide) (by decide) (by decide)).charge 1
  -- v := dst[e]
  have h1eval : evalW st1 (.load "dst" (.var "e")) = some ((G.dst eFin : ℕ)) := by
    rw [evalW_load_of (j := (eFin : ℕ)) (by rw [evalW_var, h1e])
      (by rw [S1.frame.hdstL]; exact hidxm)]
    exact congrArg some hdst_e
  refine runs_seq (runs_wset (a := (G.dst eFin : ℕ)) h1eval ?_)
  set st2 : State ℝ≥0 := (st1.setW "v" (G.dst eFin : ℕ)).charge 1 with hst2
  have h2u : st2.w "u" = u := by simp [st2, st1, State.setW, State.charge, hwu]
  have h2v : st2.w "v" = (G.dst eFin : ℕ) := by simp [st2, State.setW, State.charge]
  have h2e : st2.w "e" = (eFin : ℕ) := by simp [st2, st1, State.setW, State.charge]
  have h2cost : st2.cost = st.cost + 2 := by simp [st2, st1, State.setW, State.charge]
  have S2 : SweepInv G s u st2 :=
    ((S.setW "e" (eFin : ℕ) (by decide) (by decide) (by decide)).charge 1
      |>.setW "v" (G.dst eFin : ℕ) (by decide) (by decide) (by decide)).charge 1
  have h2cap : G.n + G.m + 2 ≤ st2.cap := S2.frame.hcap
  have h2distL : st2.vlen "dist" = G.n := S2.frame.hdistL
  have h2reachL : st2.wlen "reach" = G.n := S2.frame.hreachL
  have h2wL : st2.vlen "w" = G.m := S2.frame.hwL
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
    refine finish _ ((S2.charge 1).charge 1) rfl rfl rfl rfl rfl rfl rfl rfl ?_
      S.reach_u (fun v => rfl) rfl ?_
    · simp [State.charge, h2cost]
    · exact relaxed_of_settled ((S2.charge 1).charge 1) huu hsrc_n
        (by show ((st2.charge 1).charge 1).wa "reach" (G.dst eFin) = 2; exact h2v2)
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
      have h4distL : S4.vlen "dist" = G.n := S.frame.hdistL
      have h4reachL : S4.wlen "reach" = G.n := S.frame.hreachL
      have h4wL : S4.vlen "w" = G.m := S.frame.hwL
      have h4cap : G.n + G.m + 2 ≤ S4.cap := S.frame.hcap
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
      have h5reachL : S5.wlen "reach" = G.n := S.frame.hreachL
      have h5cap : G.n + G.m + 2 ≤ S5.cap := S.frame.hcap
      refine runs_wstore (j := (G.dst eFin : ℕ)) (a := 1)
        (by rw [evalW_var] <;> exact congrArg some h2v)
        (evalW_lit_of (by have := h5cap; omega))
        (by rw [h5reachL]; exact (G.dst eFin).isLt) ?_
      have hvu : (u : ℕ) ≠ (G.dst eFin : ℕ) := by
        intro h
        rw [← h] at h0v
        have h2 := S.reach_u
        omega
      have hreachu : S5.wa "reach" u = 2 := S.reach_u
      refine finish _ (sweep_inv_relax_unreached (S2.charge 1 |>.charge 1) hsrc_n h0v)
        rfl rfl rfl rfl rfl rfl ?_ ?_ ?_
        (by simp [State.setW, State.charge, State.storeW, hvu, hreachu]) (fun v => rfl) rfl ?_
      · show settledEdges G (S5.storeW "reach" (G.dst eFin) 1) = settledEdges G st
        rw [settledEdges_storeW1 (st := S5) (v := G.dst eFin) (show S5.wa "reach" (G.dst eFin) = 0 from h0v)]
        rfl
      · show settleCard G (S5.storeW "reach" (G.dst eFin) 1) = settleCard G st
        rw [settleCard_storeW1 (st := S5) (v := G.dst eFin) (show S5.wa "reach" (G.dst eFin) = 0 from h0v)]
        rfl
      · simp only [hS5, hS4, State.charge, State.storeV, State.storeW, State.setW, h2cost]
        omega
      · exact edgeRelaxed_unreached (S2.charge 1 |>.charge 1) huu hsrc_n h0v
    · -- reached-unsettled target: compare, improve only on strict gain
      have h1v : st.wa "reach" (G.dst eFin) = 1 := by
        have hle2 := S.reach_val (G.dst eFin)
        omega
      refine runs_ite_false (by rw [htestc2, if_neg h0v]) ?_
      set S4 : State ℝ≥0 := (st2.charge 1).charge 1 with hS4
      have h4distL : S4.vlen "dist" = G.n := S.frame.hdistL
      have h4wL : S4.vlen "w" = G.m := S.frame.hwL
      have h4cap : G.n + G.m + 2 ≤ S4.cap := S.frame.hcap
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
        have hedge : EdgeRelaxed G ((S5.charge 1).charge 1) u eFin := by
          refine ⟨?_, ?_⟩
          · show st.wa "reach" (G.dst eFin) ≠ 0
            rw [h1v]
            exact one_ne_zero
          · show (st.va "dist" (G.dst eFin) : ℝ≥0) ≤ st.va "dist" u + G.w eFin
            exact hle
        refine finish _
          (((S2.charge 1).charge 1 |>.setW "b" bit (by decide) (by decide) (by decide))
            |>.charge 1 |>.charge 1 |>.charge 1)
          rfl rfl rfl rfl rfl rfl rfl rfl ?_ S.reach_u (fun v => rfl) rfl hedge
        simp only [hS5, hS4, State.charge, State.setW, h2cost]
        omega
      · have hbit0 : bit = 0 := by simp [bit, realOps, hle]
        refine runs_ite_false (by rw [evalW_var, hS5b, hbit0]) ?_
        have h5distL : S5.vlen "dist" = G.n := S.frame.hdistL
        have h5wL : S5.vlen "w" = G.m := S.frame.hwL
        have h51distL : (S5.charge 1).vlen "dist" = G.n := S.frame.hdistL
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
        refine finish _ (sweep_inv_relax_improve
          ((S2.charge 1).charge 1 |>.setW "b" bit (by decide) (by decide) (by decide)
            |>.charge 1 |>.charge 1)
          hsrc_n h1v (lt_of_not_ge hle))
          rfl rfl rfl rfl rfl rfl rfl rfl ?_ S.reach_u (fun v => rfl) rfl ?_
        · simp only [hS5, hS4, State.charge, State.storeV, State.setW, h2cost]
          omega
        · exact edgeRelaxed_improve
            ((S2.charge 1).charge 1 |>.setW "b" bit (by decide) (by decide) (by decide)
              |>.charge 1 |>.charge 1)
            huu hsrc_n h1v

/-- Sweep variant of one relax loop over `u`'s CSR segment: `K = head[u+1] - head[u]`
iterations of `sweep_relaxBody_runs`, cursor from `head u` to `head (u+1)`.  DESIGN:
counted `runs_while` exactly like `relaxLoop_runs` below, invariant `J k t = SweepInv ∧
t.w "j" = head u + k ∧ <same view/settled/card conjuncts> ∧ t.cost ≤ st.cost + 9*k`; the
step calls `sweep_relaxBody_runs` at `(t.charge 1)`; the exit yields `SweepInv` at cursor
`head (u+1)`, ready for `SweepInv.toInv`. -/
theorem sweep_relaxLoop_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (S : SweepInv G s u st) (huu : u < G.n) (hwu : st.w "u" = u)
    (hj0 : st.w "j" = st.wa "head" u) (hjend : st.w "jend" = st.wa "head" (u + 1)) :
    Runs realOps relaxLoop st (fun st' => SweepInv G s u st' ∧
      st'.w "j" = st.wa "head" (u + 1) ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
      st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
      settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
      (st'.cost : ℝ) ≤ st.cost + 9 * (st.wa "head" (u + 1) - st.wa "head" u) + 1 ∧
      st'.wa "reach" u = 2 ∧ ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
  sorry

/-- One settle step in full: `settleBody` from an `Inv` state settles its scan winner `u`
exactly (exchange = `min_settled_exact`) and sweeps its out-edges (`sweep_relaxLoop_runs`),
ending at `Inv ∧ reach u = 2`.  DESIGN: state chain `wset "u" best` → `wstore "reach" u 2`
→ `wset "j" head[u]` → `wset "jend" head[u+1]` → `relaxLoop`; establish `SweepInv` at the
pre-sweep state (cursor = `head u` makes `relaxed_swept` vacuous; `settled_exact u` =
`min_settled_exact I hu hmin`; `relaxed_other` = the pre-store `Inv.relaxed` since the
store changes only `reach u : 1 → 2`), run `sweep_relaxLoop_runs`, conclude with
`SweepInv.toInv` + `reach_u`. -/
theorem settleBody_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : Fin G.n}
    (I : Inv G s st) (hu : st.wa "reach" u = 1) (hbest : st.w "best" = u) (huu : u < G.n)
    (hmin : ∀ v : Fin G.n, st.wa "reach" v = 1 → (st.va "dist" u : ℝ≥0) ≤ st.va "dist" v) :
    Runs realOps settleBody st (fun st' => Inv G s st' ∧ st'.wa "reach" u = 2 ∧
      st'.w "u" = u ∧ st'.w "j" = st.wa "head" (u + 1) ∧ st'.w "jend" = st.wa "head" (u + 1) ∧
      st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
      settleCard G st' = settleCard G st + 1 ∧
      settledEdges G st' = settledEdges G st + srcCnt G u G.m ∧
      (st'.cost : ℝ) ≤ st.cost + 9 * (st.wa "head" (u + 1) - st.wa "head" u) + 8 ∧
      ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
  sorry

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


/-- One relax sweep over `u`'s CSR segment: `K = head[u+1] - head[u]` iterations of
`relaxBody`, ending with the cursor at the segment end.  Cost `≤ 9·K + 1`. -/
theorem relaxLoop_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (I : Inv G s st) (hu : st.wa "reach" u = 2) (huu : u < G.n) (hwu : st.w "u" = u)
    (hj0 : st.w "j" = st.wa "head" u) (hjend : st.w "jend" = st.wa "head" (u + 1)) :
    Runs realOps relaxLoop st (fun st' => Inv G s st' ∧
      st'.w "j" = st.wa "head" (u + 1) ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
      st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
      settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
      (st'.cost : ℝ) ≤ st.cost + 9 * (st.wa "head" (u + 1) - st.wa "head" u) + 1) := by
  have hmono : st.wa "head" u ≤ st.wa "head" (u + 1) :=
    I.csr.head_mono u (u + 1) (by omega) (by omega)
  set J : ℕ → State ℝ≥0 → Prop := fun k t => Inv G s t ∧
      t.w "j" = st.wa "head" u + k ∧ t.w "u" = st.w "u" ∧ t.w "jend" = st.w "jend" ∧
      t.w "k" = st.w "k" ∧ t.w "best" = st.w "best" ∧ t.w "i" = st.w "i" ∧
      settledEdges G t = settledEdges G st ∧ settleCard G t = settleCard G st ∧
      t.cost ≤ st.cost + 9 * k ∧ t.wa "reach" u = 2 ∧
      (∀ v : ℕ, t.wa "head" v = st.wa "head" v) with hJ
  have step : ∀ k < (st.wa "head" (u + 1) - st.wa "head" u), ∀ t, J k t →
      ∃ x, evalW t (.lt (.var "j") (.var "jend")) = some x ∧ x ≠ 0 ∧
        Runs realOps relaxBody (t.charge 1) (J (k + 1)) := by
    intro k hk t Jt
    obtain ⟨It, hjt, hut, hjet, hkt, hbt, hit, hset, hsct, hct, hrt, hhead⟩ := Jt
    have hjlt : t.w "j" < t.w "jend" := by
      rw [hjt, hjet, hjend]
      omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (evalW_var t "j") (evalW_var t "jend")
        (by have := It.frame.hcap; omega), if_pos hjlt]
    · refine Runs.mono (relaxBody_runs (I := It.charge 1) (u := u) hrt huu
        (hut.trans hwu)
        (by show t.wa "head" u ≤ t.w "j"; rw [hhead u, hjt]; omega)
        (by show t.w "j" < t.wa "head" (u + 1); rw [hjt, hhead (u + 1)]; omega)) ?_
      rintro t' ⟨Iv, hju, hu2, hje2, hkb2, hbst2, hin2, hse2, hsc2, hc2, hru2, hhh2⟩
      refine ⟨Iv, ?_, hu2.trans hut, hje2.trans hjet, hkb2.trans hkt, hbst2.trans hbt,
        hin2.trans hit, hse2.trans hset, hsc2.trans hsct, ?_, hru2, ?_⟩
      · have h1 := hju
        simp only [State.charge] at h1
        omega
      · have h1 : t'.cost ≤ t.cost + 9 := by
          have h := hc2
          simp [State.charge] at h
          exact_mod_cast h
        omega
      · intro v
        exact (hhh2 v).trans (hhead v)
  have exit : ∀ t, J (st.wa "head" (u + 1) - st.wa "head" u) t →
      evalW t (.lt (.var "j") (.var "jend")) = some 0 ∧
      (fun st' => Inv G s st' ∧
        st'.w "j" = st.wa "head" (u + 1) ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
        st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
        settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
        (st'.cost : ℝ) ≤ st.cost + 9 * (st.wa "head" (u + 1) - st.wa "head" u) + 1) (t.charge 1) := by
    intro t Jt
    obtain ⟨It, hjt, hut, hjet, hkt, hbt, hit, hset, hsct, hct, hrt, hhead⟩ := Jt
    have hje : t.w "j" = t.w "jend" := by
      rw [hjt, hjet, hjend]
      omega
    constructor
    · rw [evalW_lt_of (evalW_var t "j") (evalW_var t "jend")
        (by have := It.frame.hcap; omega), if_neg (by omega)]
    · refine ⟨It.charge 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show t.w "j" = st.wa "head" (u + 1)
        rw [hjt]
        omega
      · simp [State.charge, hut]
      · simp [State.charge, hjet]
      · simp [State.charge, hkt]
      · simp [State.charge, hbt]
      · simp [State.charge, hit]
      · show settledEdges G t = settledEdges G st
        exact hset
      · show settleCard G t = settleCard G st
        exact hsct
      · simp [State.charge]
        exact_mod_cast hct
  refine runs_while J (st.wa "head" (u + 1) - st.wa "head" u) _ step exit st ?_
  refine ⟨I, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hu, fun v => rfl⟩
  · rw [hj0]
    omega
  · omega

/-! ## The min-scan (independent of the relax sweep — `minBody` never relaxes edges) -/

/-- Prefix form of `ScanPost`: `b` is the argmin over `reach = 1` vertices in the scanned
prefix `[0, k)`, or the `n` sentinel if the prefix holds none. -/
def ScanPrefix (G : Graph) (st : State ℝ≥0) (b k : ℕ) : Prop :=
  (b = G.n ∧ ∀ v : Fin G.n, (v : ℕ) < k → st.wa "reach" v = 1 → False) ∨
  (b < G.n ∧ (b : ℕ) < k ∧ st.wa "reach" b = 1 ∧
    ∀ v : Fin G.n, (v : ℕ) < k → st.wa "reach" v = 1 → (st.va "dist" b : ℝ≥0) ≤ st.va "dist" v)

theorem scanPrefix_full {G : Graph} {st : State ℝ≥0} {b : ℕ}
    (h : ScanPrefix G st b G.n) : ScanPost G st b := by
  rcases h with ⟨hb, hall⟩ | ⟨hbl, hbk, hbr, hle⟩
  · exact Or.inl ⟨hb, fun v hv => hall v v.isLt hv⟩
  · exact Or.inr ⟨hbl, hbr, fun v hv => hle v v.isLt hv⟩

/-- The min-scan: from `best = n`, `i = 0`, `minLoop` runs `n` counted steps; at exit `best`
is the argmin over `reach = 1` (or the `n` sentinel) — `ScanPost`.  Cost `≤ 9·n + 1`.
`minBody` writes only `i`/`best`/`c`, so `Inv` survives by `Inv.setW`.  FILL (per the
`relaxLoop_runs` counted-while pattern): invariant `J k t` = `Inv` ∧ `t.w "i" = k` ∧
`ScanPrefix G t (t.w "best") k` ∧ `u/j/jend/k`/`settled/card`/`head` unchanged ∧ `cost ≤
st.cost + 9*k`; step evaluates `i < n` (`evalW_lt_of` + `frame.hn`) and runs `minBody`, the
`ScanPrefix` argmin maintenance being the `reach k = 1` / `best = n` / `dist k ≤ dist best`
case split; exit uses `scanPrefix_full`; init is the sentinel disjunct. -/
theorem minLoop_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0}
    (I : Inv G s st) (hbest : st.w "best" = G.n) (hi0 : st.w "i" = 0) :
    Runs realOps minLoop st (fun st' => Inv G s st' ∧ ScanPost G st' (st'.w "best") ∧
      st'.w "u" = st.w "u" ∧ st'.w "j" = st.w "j" ∧ st'.w "jend" = st.w "jend" ∧
      st'.w "k" = st.w "k" ∧ settledEdges G st' = settledEdges G st ∧
      settleCard G st' = settleCard G st ∧ (st'.cost : ℝ) ≤ st.cost + 9 * G.n + 1 ∧
      ∀ v : ℕ, st'.wa "head" v = st.wa "head" v) := by
  sorry

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
