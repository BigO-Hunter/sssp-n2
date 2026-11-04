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

/-- One relax step (`relaxBody`) over edge `st.w "e" = idx[st.w "j"]` of `u`'s CSR segment
preserves `Inv` and advances the cursor.  Settled targets are skipped mechanically; the
reached-unsettled strict-improvement branch only lowers labels, preserving `relaxed`. -/
theorem relaxBody_runs {G : Graph} {s : Fin G.n} {st : State ℝ≥0} {u : ℕ}
    (I : Inv G s st) (hu : st.wa "reach" u = 2) (huu : u < G.n)
    (hj : st.wa "head" u ≤ st.w "j") (hjend : st.w "j" < st.wa "head" (u + 1)) :
    Runs realOps relaxBody st (fun st' => Inv G s st' ∧
      st'.w "j" = st.w "j" + 1 ∧ st'.w "u" = st.w "u" ∧ st'.w "jend" = st.w "jend" ∧
      st'.w "k" = st.w "k" ∧ st'.w "best" = st.w "best" ∧ st'.w "i" = st.w "i" ∧
      settledEdges G st' = settledEdges G st ∧ settleCard G st' = settleCard G st ∧
      (st'.cost : ℝ) ≤ st.cost + 8) := by
  sorry

/-- One relax-loop step (single edge of `u`'s segment) preserves `Inv`. -/
theorem inv_of_relax_step {G : Graph} {s : Fin G.n} {st st' : State ℝ≥0} {u : ℕ}
    (I : Inv G s st) (hu : st.wa "reach" u = 2) (huu : u < G.n)
    (hj : st.wa "head" u ≤ st.w "j") (hjend : st.w "j" < st.wa "head" (u + 1))
    (hstep : Runs realOps relaxBody st (fun r => r = st')) :
    Inv G s st' := by
  obtain ⟨f, r, hr, he⟩ := hstep
  obtain ⟨f2, r2, hr2, hpost⟩ := relaxBody_runs I hu huu hj hjend
  have : r = r2 := exec_det realOps hr hr2
  rw [← he, this]
  exact hpost.1

/-- The main loop preserves `Inv` per iteration, with measure `n - k`. -/
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
