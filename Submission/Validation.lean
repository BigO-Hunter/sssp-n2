import Submission.SsspStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Checks of the race statement (not trusted; the verifier does not use this file).

* `weaker_time`: a row also proves every slower time at the same density. Times are
  compared by the lexicographic order of `(a', b', c')`.
* `cover_sparser`: a row also proves its time at every sparser density. Densities are
  compared by the lexicographic order of `(a, b)`, with `b ≥ 0`.
* `cap_ge_self`, `time_pos`: the sparse clause is not empty (it holds every graph with at
  most `n` edges) and the time budget is positive.
-/

namespace BigOSpeedrun.DirectedSSSP.Validation

open Frontier Frontier.RAM Filter Asymptotics

lemma CorrectWithin.mono {P : Program} {G : Graph} {s : Fin G.n} {x y : ℝ}
    (h : CorrectWithin P G s x) (hxy : x ≤ y) : CorrectWithin P G s y := by
  obtain ⟨f, r, h1, h2, h3⟩ := h
  exact ⟨f, r, h1, h2, h3.trans hxy⟩

/-! ### Logarithms at `n ≥ 16` -/

lemma one_le_log {n : ℕ} (hn : 16 ≤ n) : 1 ≤ Real.log n := by
  have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

lemma one_le_loglog {n : ℕ} (hn : 16 ≤ n) : 1 ≤ Real.log (Real.log n) := by
  have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hl16 : Real.log 16 ≤ Real.log n := Real.log_le_log (by norm_num) h16
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have he : Real.exp 1 ≤ Real.log n := by
    have := Real.exp_one_lt_d9
    have := Real.log_two_gt_d9
    linarith
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

lemma loglog_le_log {n : ℕ} (hn : 16 ≤ n) : Real.log (Real.log n) ≤ Real.log n := by
  have h := one_le_log hn
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log n)
  linarith

lemma time_pos (a b c : ℚ) {n : ℕ} (hn : 16 ≤ n) : 0 < Time a b c n := by
  have hx : (0 : ℝ) < n := by
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hL := one_le_log hn
  have hLL := one_le_loglog hn
  unfold Time
  have := Real.rpow_pos_of_pos hx (a : ℝ)
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log n) (b : ℝ)
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log n)) (c : ℝ)
  positivity

/-! ### Polylogarithms against powers -/

/-- For every `s` and every `r > 0`, eventually `c · (log y)^s ≤ y^r`. -/
lemma ev_log_rpow_le (s : ℝ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ y : ℝ in atTop, c * Real.log y ^ s ≤ y ^ r := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop s hr).bound (inv_pos.2 hc),
    eventually_ge_atTop 1] with y hy h1
  have hlog : 0 ≤ Real.log y := Real.log_nonneg h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hy
  calc c * Real.log y ^ s ≤ c * (c⁻¹ * y ^ r) := mul_le_mul_of_nonneg_left hy hc.le
    _ = y ^ r := by field_simp

/-- The same along `n → ∞` in `ℕ`. -/
lemma ev_nat_log_rpow_le (s : ℝ) {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ^ s ≤ (n : ℝ) ^ r :=
  tendsto_natCast_atTop_atTop.eventually (ev_log_rpow_le s hr hc)

/-- `(log log n)^s ≤ (log n)^r` eventually, for `r > 0`. -/
lemma ev_nat_loglog_rpow_le (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (Real.log n) ^ s ≤ Real.log n ^ r := by
  have := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (ev_log_rpow_le s hr one_pos)
  filter_upwards [this] with n hn
  simpa using hn

/-- For `1 ≤ u ≤ v`, `u^e ≤ v^|e|`. -/
lemma rpow_le_rpow_abs {u v e : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) : u ^ e ≤ v ^ |e| :=
  (Real.rpow_le_rpow_of_exponent_le hu (le_abs_self e)).trans
    (Real.rpow_le_rpow (by linarith) huv (abs_nonneg e))

/-! ### `weaker_time` -/

/-- The ratio form of `Time`. -/
lemma time_eq_mul {a b c a' b' c' : ℚ} {n : ℕ} (hn : 16 ≤ n) :
    Time a b c n = Time a' b' c' n *
      ((n : ℝ) ^ ((a : ℝ) - a') * Real.log n ^ ((b : ℝ) - b') *
        Real.log (Real.log n) ^ ((c : ℝ) - c')) := by
  have hx : (0 : ℝ) < n := by
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hL : (0 : ℝ) < Real.log n := by linarith [one_le_log hn]
  have hLL : (0 : ℝ) < Real.log (Real.log n) := by linarith [one_le_loglog hn]
  unfold Time
  rw [Real.rpow_sub hx, Real.rpow_sub hL, Real.rpow_sub hLL]
  have := Real.rpow_pos_of_pos hx (a' : ℝ)
  have := Real.rpow_pos_of_pos hL (b' : ℝ)
  have := Real.rpow_pos_of_pos hLL (c' : ℝ)
  field_simp

/-- If `(a', b', c') ≤ (a'', b'', c'')` in lexicographic order, eventually
`Time a' b' c' n ≤ Time a'' b'' c'' n`. -/
lemma time_eventually_le {a' b' c' a'' b'' c'' : ℚ}
    (h : a' < a'' ∨ (a' = a'' ∧ (b' < b'' ∨ (b' = b'' ∧ c' ≤ c'')))) :
    ∀ᶠ n : ℕ in atTop, Time a' b' c' n ≤ Time a'' b'' c'' n := by
  -- It is enough to show that the ratio `R` is at most 1.
  suffices hR : ∀ᶠ n : ℕ in atTop, 16 ≤ n ∧
      (n : ℝ) ^ ((a' : ℝ) - a'') * Real.log n ^ ((b' : ℝ) - b'') *
        Real.log (Real.log n) ^ ((c' : ℝ) - c'') ≤ 1 by
    filter_upwards [hR] with n ⟨hn, hR⟩
    rw [time_eq_mul (a' := a'') (b' := b'') (c' := c'') hn]
    exact mul_le_of_le_one_right (time_pos _ _ _ hn).le hR
  rcases h with ha | ⟨ha, hb | ⟨hb, hc⟩⟩
  · -- `a' < a''`: the polylog factors are at most `(log n)^p ≤ n^(a'' - a')`.
    have hd : (0 : ℝ) < (a'' : ℝ) - a' := sub_pos.2 (by exact_mod_cast ha)
    filter_upwards [eventually_ge_atTop 16,
      ev_nat_log_rpow_le (((b' : ℝ) - b'') + |(c' : ℝ) - c''|) hd one_pos] with n hn hp
    refine ⟨hn, ?_⟩
    have hx : (0 : ℝ) < n := by
      have : (16 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hL1 := one_le_log hn
    have hL : (0 : ℝ) < Real.log n := by linarith
    have hLL1 := one_le_loglog hn
    have hLL : Real.log (Real.log n) ^ ((c' : ℝ) - c'') ≤ Real.log n ^ |(c' : ℝ) - c''| :=
      rpow_le_rpow_abs hLL1 (loglog_le_log hn)
    have hpoly : Real.log n ^ ((b' : ℝ) - b'') * Real.log (Real.log n) ^ ((c' : ℝ) - c'') ≤
        (n : ℝ) ^ ((a'' : ℝ) - a') := by
      calc _ ≤ Real.log n ^ ((b' : ℝ) - b'') * Real.log n ^ |(c' : ℝ) - c''| :=
            mul_le_mul_of_nonneg_left hLL (Real.rpow_nonneg hL.le _)
        _ = Real.log n ^ (((b' : ℝ) - b'') + |(c' : ℝ) - c''|) := (Real.rpow_add hL _ _).symm
        _ ≤ _ := by simpa using hp
    have hxa : (n : ℝ) ^ ((a' : ℝ) - a'') * (n : ℝ) ^ ((a'' : ℝ) - a') = 1 := by
      rw [← Real.rpow_add hx]
      simp
    calc (n : ℝ) ^ ((a' : ℝ) - a'') * Real.log n ^ ((b' : ℝ) - b'') *
          Real.log (Real.log n) ^ ((c' : ℝ) - c'')
        = (n : ℝ) ^ ((a' : ℝ) - a'') * (Real.log n ^ ((b' : ℝ) - b'') *
          Real.log (Real.log n) ^ ((c' : ℝ) - c'')) := by ring
      _ ≤ (n : ℝ) ^ ((a' : ℝ) - a'') * (n : ℝ) ^ ((a'' : ℝ) - a') :=
          mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hx.le _)
      _ = 1 := hxa
  · -- `a' = a''`, `b' < b''`: `(log log n)^(c' - c'') ≤ (log n)^(b'' - b')`.
    have hd : (0 : ℝ) < (b'' : ℝ) - b' := sub_pos.2 (by exact_mod_cast hb)
    filter_upwards [eventually_ge_atTop 16,
      ev_nat_loglog_rpow_le ((c' : ℝ) - c'') hd] with n hn hp
    refine ⟨hn, ?_⟩
    have hL : (0 : ℝ) < Real.log n := by linarith [one_le_log hn]
    have hLb : Real.log n ^ ((b' : ℝ) - b'') * Real.log n ^ ((b'' : ℝ) - b') = 1 := by
      rw [← Real.rpow_add hL]
      simp
    subst ha
    calc (n : ℝ) ^ ((a' : ℝ) - a') * Real.log n ^ ((b' : ℝ) - b'') *
          Real.log (Real.log n) ^ ((c' : ℝ) - c'')
        = Real.log n ^ ((b' : ℝ) - b'') * Real.log (Real.log n) ^ ((c' : ℝ) - c'') := by
          simp
      _ ≤ Real.log n ^ ((b' : ℝ) - b'') * Real.log n ^ ((b'' : ℝ) - b') :=
          mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hL.le _)
      _ = 1 := hLb
  · -- `a' = a''`, `b' = b''`, `c' ≤ c''`: `(log log n)^(c' - c'') ≤ 1`.
    filter_upwards [eventually_ge_atTop 16] with n hn
    refine ⟨hn, ?_⟩
    subst ha
    subst hb
    have hc' : (c' : ℝ) - c'' ≤ 0 := sub_nonpos.2 (by exact_mod_cast hc)
    simpa using Real.rpow_le_one_of_one_le_of_nonpos (one_le_loglog hn) hc'

/-- A row also proves every slower time at the same density. -/
theorem weaker_time {a b a' b' c' a'' b'' c'' : ℚ}
    (h : a' < a'' ∨ (a' = a'' ∧ (b' < b'' ∨ (b' = b'' ∧ c' ≤ c'')))) :
    Bound a b a' b' c' → Bound a b a'' b'' c'' := by
  rintro ⟨P, hP, C, hC, N, hN, hS, hF⟩
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (time_eventually_le h)
  refine ⟨P, hP, C, hC, max N N1, hN.trans (le_max_left _ _), ?_, hF⟩
  intro G s hn hsp
  exact CorrectWithin.mono (hS G s ((le_max_left _ _).trans hn) hsp)
    (mul_le_mul_of_nonneg_left (hN1 _ ((le_max_right _ _).trans hn)) hC.le)

/-! ### `cover_sparser` -/

/-- `⌊log₂ n⌋ ≤ 2 log n`. -/
lemma natLog_le_two_log {n : ℕ} (hn : n ≠ 0) : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hp : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
  have := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at this
  have h2 := Real.log_two_gt_d9
  have hK : (0 : ℝ) ≤ (Nat.log 2 n : ℕ) := Nat.cast_nonneg _
  nlinarith

lemma one_le_natLog {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by
  have : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  exact_mod_cast this

/-- If `(a₀, b₀) ≤ (a, b)` in lexicographic order and `b₀, b ≥ 0`, eventually
`Cap a₀ b₀ n ≤ Cap a b n`. -/
lemma cap_eventually_le {a b a₀ b₀ : ℚ} (hb₀ : 0 ≤ b₀) (hb : 0 ≤ b)
    (h : a₀ < a ∨ (a₀ = a ∧ b₀ ≤ b)) :
    ∀ᶠ n : ℕ in atTop, Cap a₀ b₀ n ≤ Cap a b n := by
  rcases h with ha | ⟨ha, hbb⟩
  · have hd : (0 : ℝ) < (a : ℝ) - a₀ := sub_pos.2 (by exact_mod_cast ha)
    have hc : (0 : ℝ) < (2 : ℝ) ^ (b₀ : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    filter_upwards [eventually_ge_atTop 2, ev_nat_log_rpow_le (b₀ : ℝ) hd hc] with n hn hp
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : (0 : ℝ) < n := by linarith
    have hK1 := one_le_natLog hn
    have hKle := natLog_le_two_log (n := n) (by omega)
    have hb₀' : (0 : ℝ) ≤ b₀ := by exact_mod_cast hb₀
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    have hL : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
    -- `⌊K^b₀⌋ ≤ K^b₀ ≤ (2 log n)^b₀ = 2^b₀ (log n)^b₀ ≤ n^(a - a₀)`.
    have h1 : (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b₀ : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) ^ ((a : ℝ) - a₀) := by
      calc (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b₀ : ℝ)⌋₊ : ℝ)
          ≤ ((Nat.log 2 n : ℕ) : ℝ) ^ (b₀ : ℝ) :=
            Nat.floor_le (Real.rpow_nonneg (by linarith) _)
        _ ≤ (2 * Real.log n) ^ (b₀ : ℝ) := Real.rpow_le_rpow (by linarith) hKle hb₀'
        _ = (2 : ℝ) ^ (b₀ : ℝ) * Real.log n ^ (b₀ : ℝ) := Real.mul_rpow (by norm_num) hL
        _ ≤ _ := hp
    -- `1 ≤ ⌊K^b⌋`.
    have h2 : (1 : ℝ) ≤ (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ : ℝ) := by
      have : 1 ≤ ⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ :=
        Nat.le_floor (by simpa using Real.one_le_rpow hK1 hb')
      exact_mod_cast this
    have hxa : (n : ℝ) ^ (a₀ : ℝ) * (n : ℝ) ^ ((a : ℝ) - a₀) = (n : ℝ) ^ (a : ℝ) := by
      rw [← Real.rpow_add hx]
      simp
    unfold Cap
    calc (n : ℝ) ^ (a₀ : ℝ) * (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b₀ : ℝ)⌋₊ : ℝ)
        ≤ (n : ℝ) ^ (a₀ : ℝ) * (n : ℝ) ^ ((a : ℝ) - a₀) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx.le _)
      _ = (n : ℝ) ^ (a : ℝ) * 1 := by rw [hxa, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx.le _)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    subst ha
    have hbb' : (b₀ : ℝ) ≤ b := by exact_mod_cast hbb
    unfold Cap
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact_mod_cast Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (one_le_natLog hn) hbb')

/-- A row also proves its time at every sparser density. -/
theorem cover_sparser {a b a₀ b₀ a' b' c' : ℚ} (hb₀ : 0 ≤ b₀) (hb : 0 ≤ b)
    (h : a₀ < a ∨ (a₀ = a ∧ b₀ ≤ b)) :
    Bound a b a' b' c' → Bound a₀ b₀ a' b' c' := by
  rintro ⟨P, hP, C, hC, N, hN, hS, hF⟩
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (cap_eventually_le hb₀ hb h)
  refine ⟨P, hP, C, hC, max N N1, hN.trans (le_max_left _ _), ?_, hF⟩
  intro G s hn hsp
  have hsp' : (G.m : ℝ) ≤ Cap a₀ b₀ G.n := hsp
  exact hS G s ((le_max_left _ _).trans hn)
    (show (G.m : ℝ) ≤ Cap a b G.n from hsp'.trans (hN1 _ ((le_max_right _ _).trans hn)))

/-! ### The sparse clause is not empty -/

/-- For `a ≥ 1`, `b ≥ 0`, `n ≥ 2`, the cap is at least `n`: every graph with at most
`n` edges is in the sparse clause. -/
theorem cap_ge_self {a b : ℚ} (ha : 1 ≤ a) (hb : 0 ≤ b) {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ≤ Cap a b n := by
  have hx : (1 : ℝ) ≤ n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have h2 : (1 : ℝ) ≤ (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ : ℝ) := by
    have : 1 ≤ ⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ :=
      Nat.le_floor (by simpa using Real.one_le_rpow (one_le_natLog hn) hb')
    exact_mod_cast this
  unfold Cap
  calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (n : ℝ) ^ (a : ℝ) := Real.rpow_le_rpow_of_exponent_le hx ha'
    _ = (n : ℝ) ^ (a : ℝ) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith) _)

end BigOSpeedrun.DirectedSSSP.Validation
