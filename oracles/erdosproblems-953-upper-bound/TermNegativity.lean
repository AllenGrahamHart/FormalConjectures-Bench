import FormalConjecturesBench.PoissonKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

open Filter
open scoped Topology

namespace Erdos953Formalization

/-- The real variable `a = 2πm` used in the term-negativity proof. -/
noncomputable def aNat (m : ℕ) : ℝ :=
  2 * Real.pi * (m : ℝ)

/-- The real variable `b = 2πt` used in the term-negativity proof. -/
noncomputable def bOfT (t : ℝ) : ℝ :=
  2 * Real.pi * t

/-- The perturbation `ζ = s^2 + 2ias` used near the singular radii. -/
noncomputable def zeta (s a : ℝ) : ℂ :=
  Complex.ofReal (s ^ 2) + 2 * Complex.I * Complex.ofReal (a * s)

/-- Real shorthand for `D^{-3/2}` when `D > 0`. -/
def powNegThreeHalves (D : ℝ) : ℝ :=
  (D * Real.sqrt D)⁻¹

/-- Real shorthand for `D^{-5/2}` when `D > 0`. -/
def powNegFiveHalves (D : ℝ) : ℝ :=
  (D ^ 2 * Real.sqrt D)⁻¹

lemma powNegThreeHalves_pos {D : ℝ} (hD : 0 < D) :
    0 < powNegThreeHalves D := by
  unfold powNegThreeHalves
  exact inv_pos.mpr (mul_pos hD (Real.sqrt_pos.2 hD))

lemma powNegFiveHalves_pos {D : ℝ} (hD : 0 < D) :
    0 < powNegFiveHalves D := by
  unfold powNegFiveHalves
  exact inv_pos.mpr (mul_pos (sq_pos_of_ne_zero hD.ne') (Real.sqrt_pos.2 hD))

lemma mul_powNegFiveHalves_eq_powNegThreeHalves {D : ℝ} (hD : 0 < D) :
    D * powNegFiveHalves D = powNegThreeHalves D := by
  unfold powNegFiveHalves powNegThreeHalves
  have hsqrt_ne : Real.sqrt D ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  field_simp [hD.ne', hsqrt_ne]

lemma left_positive_correction_le_half {a s D : ℝ} (ha : 0 ≤ a)
    (hDpos : 0 < D) (hDge : 24 * s ^ 2 ≤ D) :
    12 * a * s ^ 2 * powNegFiveHalves D ≤
      (1 / 2 : ℝ) * a * powNegThreeHalves D := by
  have hcoef : 12 * s ^ 2 ≤ (1 / 2 : ℝ) * D := by linarith
  have hden_nonneg : 0 ≤ (D ^ 2 * Real.sqrt D)⁻¹ := by
    exact inv_nonneg.mpr (mul_nonneg (sq_nonneg D) (Real.sqrt_nonneg D))
  have hmain : a * (12 * s ^ 2) * (D ^ 2 * Real.sqrt D)⁻¹ ≤
      a * ((1 / 2 : ℝ) * D) * (D ^ 2 * Real.sqrt D)⁻¹ := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef ha) hden_nonneg
  unfold powNegFiveHalves powNegThreeHalves
  calc
    12 * a * s ^ 2 * (D ^ 2 * Real.sqrt D)⁻¹ =
        a * (12 * s ^ 2) * (D ^ 2 * Real.sqrt D)⁻¹ := by ring
    _ ≤ a * ((1 / 2 : ℝ) * D) * (D ^ 2 * Real.sqrt D)⁻¹ := hmain
    _ = (1 / 2 : ℝ) * a * (D * Real.sqrt D)⁻¹ := by
      have hsqrt_ne : Real.sqrt D ≠ 0 := (Real.sqrt_pos.2 hDpos).ne'
      field_simp [hDpos.ne', hsqrt_ne]

lemma main_magnitude_lower_of_bounds {a D U : ℝ}
    (hUpos : 0 < U) (ha : 2 * U ≤ a) (hDpos : 0 < D) (hDle : D ≤ 128 * U) :
    (1 / 2000 : ℝ) * (Real.sqrt U)⁻¹ ≤ a * powNegThreeHalves D := by
  have hUnonneg : 0 ≤ U := hUpos.le
  have hsqrtU_pos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUpos
  have hbig_pos : 0 < 1536 * U * Real.sqrt U := by positivity
  have hden_pos : 0 < D * Real.sqrt D := by positivity
  have hsqrt128_le : Real.sqrt (128 * U) ≤ 12 * Real.sqrt U := by
    rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 12 * Real.sqrt U)]
    rw [mul_pow, Real.sq_sqrt hUnonneg]
    nlinarith
  have hsqrtD_le : Real.sqrt D ≤ 12 * Real.sqrt U :=
    (Real.sqrt_le_sqrt hDle).trans hsqrt128_le
  have hden_le : D * Real.sqrt D ≤ 1536 * U * Real.sqrt U := by
    calc
      D * Real.sqrt D ≤ (128 * U) * (12 * Real.sqrt U) :=
        mul_le_mul hDle hsqrtD_le (Real.sqrt_nonneg D) (by positivity)
      _ = 1536 * U * Real.sqrt U := by ring
  have hinv : (1536 * U * Real.sqrt U)⁻¹ ≤ (D * Real.sqrt D)⁻¹ :=
    inv_anti₀ hden_pos hden_le
  have hpow_ge : (1536 * U * Real.sqrt U)⁻¹ ≤ powNegThreeHalves D := by
    simpa [powNegThreeHalves] using hinv
  have hapos : 0 ≤ a := (mul_pos (by norm_num : (0 : ℝ) < 2) hUpos).le.trans ha
  have hbig_inv_nonneg : 0 ≤ (1536 * U * Real.sqrt U)⁻¹ := inv_nonneg.mpr hbig_pos.le
  have hmul : (2 * U) * (1536 * U * Real.sqrt U)⁻¹ ≤ a * powNegThreeHalves D := by
    exact mul_le_mul ha hpow_ge hbig_inv_nonneg hapos
  have hleft_eq : (2 * U) * (1536 * U * Real.sqrt U)⁻¹ =
      (1 / 768 : ℝ) * (Real.sqrt U)⁻¹ := by
    field_simp [hUpos.ne', hsqrtU_pos.ne']
    ring
  have hsmall : (1 / 2000 : ℝ) * (Real.sqrt U)⁻¹ ≤
      (1 / 768 : ℝ) * (Real.sqrt U)⁻¹ := by
    exact mul_le_mul_of_nonneg_right (by norm_num : (1 / 2000 : ℝ) ≤ 1 / 768)
      (by positivity)
  calc
    (1 / 2000 : ℝ) * (Real.sqrt U)⁻¹ ≤ (1 / 768 : ℝ) * (Real.sqrt U)⁻¹ := hsmall
    _ = (2 * U) * (1536 * U * Real.sqrt U)⁻¹ := hleft_eq.symm
    _ ≤ a * powNegThreeHalves D := hmul

lemma aNat_pos {m : ℕ} (hm : 0 < m) : 0 < aNat m := by
  unfold aNat
  positivity

lemma bOfT_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ bOfT t := by
  unfold bOfT
  positivity

lemma one_le_two_pi : (1 : ℝ) ≤ 2 * Real.pi := by
  nlinarith [Real.two_le_pi]

lemma lam_complex_norm_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    ‖Complex.ofReal s + Complex.I * Complex.ofReal a‖ ≤ s + a := by
  calc
    ‖Complex.ofReal s + Complex.I * Complex.ofReal a‖ ≤
        ‖Complex.ofReal s‖ + ‖Complex.I * Complex.ofReal a‖ := norm_add_le _ _
    _ = s + a := by
      rw [norm_mul]
      simp [abs_of_nonneg hs, abs_of_nonneg ha]

lemma lam_complex_norm_le_two_mul {s a : ℝ} (hsle : s ≤ 1) (hs0 : 0 ≤ s)
    (ha : 2 * Real.pi ≤ a) :
    ‖Complex.ofReal s + Complex.I * Complex.ofReal a‖ ≤ 2 * a := by
  have ha0 : 0 ≤ a := (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hnorm := lam_complex_norm_le hs0 ha0
  have hs_le_a : s ≤ a := hsle.trans (one_le_two_pi.trans ha)
  linarith

lemma zeta_norm_le {s a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : 2 * Real.pi ≤ a) :
    ‖zeta s a‖ ≤ 3 * a * s := by
  have ha_nonneg : 0 ≤ a := le_trans (by positivity) ha
  unfold zeta
  calc
    ‖Complex.ofReal (s ^ 2) + 2 * Complex.I * Complex.ofReal (a * s)‖
        ≤ ‖Complex.ofReal (s ^ 2)‖ +
            ‖2 * Complex.I * Complex.ofReal (a * s)‖ := norm_add_le _ _
    _ = s ^ 2 + 2 * (a * s) := by
      have h1 : ‖Complex.ofReal (s ^ 2)‖ = s ^ 2 := by simp
      have h2 :
          ‖(2 : ℂ) * Complex.I * Complex.ofReal (a * s)‖ = 2 * (a * s) := by
        rw [norm_mul, norm_mul]
        simp [abs_of_nonneg ha_nonneg, abs_of_nonneg hs0]
      rw [h1, h2]
    _ ≤ a * s + 2 * (a * s) := by
      have hle_as : s ^ 2 ≤ a * s := by
        have hsa : s ≤ a := hs1.trans (one_le_two_pi.trans ha)
        nlinarith
      nlinarith
    _ = 3 * a * s := by ring

lemma D_lower {a b L s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsep : L * s ≤ |a - b|) :
    a * L * s ≤ |a ^ 2 - b ^ 2| := by
  calc
    a * L * s = a * (L * s) := by ring
    _ ≤ a * |a - b| := mul_le_mul_of_nonneg_left hsep ha
    _ ≤ (a + b) * |a - b| := by
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = |a ^ 2 - b ^ 2| := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by linarith : 0 ≤ a + b)]

lemma zeta_div_D_le {s a b L : ℝ}
    (hspos : 0 < s) (hs1 : s ≤ 1) (hLpos : 0 < L)
    (ha : 2 * Real.pi ≤ a) (hb : 0 ≤ b)
    (hsep : L * s ≤ |a - b|) :
    ‖zeta s a / (Complex.ofReal |a ^ 2 - b ^ 2|)‖ ≤ 3 / L := by
  have hs0 : 0 ≤ s := hspos.le
  have htwopipos : 0 < 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have ha_pos : 0 < a := htwopipos.trans_le ha
  have ha0 : 0 ≤ a := ha_pos.le
  have hz := zeta_norm_le hs0 hs1 ha
  have hDlower : a * L * s ≤ |a ^ 2 - b ^ 2| := D_lower ha0 hb hsep
  have hdenpos : 0 < a * L * s := by positivity
  have hDpos : 0 < |a ^ 2 - b ^ 2| := hdenpos.trans_le hDlower
  calc
    ‖zeta s a / (Complex.ofReal |a ^ 2 - b ^ 2|)‖
        = ‖zeta s a‖ / |a ^ 2 - b ^ 2| := by
          rw [norm_div]
          simp [abs_of_pos hDpos]
    _ ≤ (3 * a * s) / |a ^ 2 - b ^ 2| :=
      div_le_div_of_nonneg_right hz hDpos.le
    _ ≤ (3 * a * s) / (a * L * s) := by
      exact div_le_div_of_nonneg_left (by positivity) hdenpos hDlower
    _ = 3 / L := by
      field_simp [ne_of_gt hLpos, ne_of_gt hspos, ne_of_gt ha_pos]

lemma zeta_div_ofReal_im (s a D : ℝ) :
    (zeta s a / (D : ℂ)).im = (2 * (a * s)) / D := by
  unfold zeta
  rw [div_eq_mul_inv]
  simp [-Complex.ofReal_pow, Complex.mul_im, Complex.add_im]
  ring

lemma scaled_integer_separation {A s t : ℝ} (m : ℤ)
    (haway : AwayFromIntegers (A * s) t) :
    (2 * Real.pi * A) * s ≤
      |2 * Real.pi * (m : ℝ) - 2 * Real.pi * t| := by
  have htwopi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hm := haway m
  calc
    (2 * Real.pi * A) * s = 2 * Real.pi * (A * s) := by ring
    _ ≤ 2 * Real.pi * |t - (m : ℝ)| :=
      mul_le_mul_of_nonneg_left hm htwopi_nonneg
    _ = |2 * Real.pi * (m : ℝ) - 2 * Real.pi * t| := by
      rw [show 2 * Real.pi * (m : ℝ) - 2 * Real.pi * t =
          -(2 * Real.pi * (t - (m : ℝ))) by ring]
      rw [abs_neg, abs_mul, abs_of_nonneg htwopi_nonneg]

lemma ceil_sub_nonneg (t : ℝ) : 0 ≤ (Int.ceil t : ℝ) - t := by
  have h := Int.le_ceil t
  linarith

lemma ceil_sub_le_one (t : ℝ) : (Int.ceil t : ℝ) - t ≤ 1 := by
  have hceil_floor : Int.ceil t ≤ Int.floor t + 1 := Int.ceil_le_floor_add_one t
  have hceil_le_floor : (Int.ceil t : ℝ) ≤ (Int.floor t : ℤ) + 1 := by
    exact_mod_cast hceil_floor
  have hfloor : ((Int.floor t : ℤ) : ℝ) ≤ t := Int.floor_le t
  linarith

lemma ceil_sub_lower_of_away {A s t : ℝ}
    (haway : AwayFromIntegers (A * s) t) :
    A * s ≤ (Int.ceil t : ℝ) - t := by
  have hnonpos : t - (Int.ceil t : ℝ) ≤ 0 := by
    have hceil_nonneg : 0 ≤ (Int.ceil t : ℝ) - t := ceil_sub_nonneg t
    linarith
  have hm := haway (Int.ceil t)
  calc
    A * s ≤ |t - (Int.ceil t : ℝ)| := hm
    _ = (Int.ceil t : ℝ) - t := by
      rw [abs_of_nonpos hnonpos]
      ring

lemma ceil_sub_pos_of_away {A s t : ℝ} (hApos : 0 < A) (hspos : 0 < s)
    (haway : AwayFromIntegers (A * s) t) :
    0 < (Int.ceil t : ℝ) - t := by
  exact (mul_pos hApos hspos).trans_le (ceil_sub_lower_of_away haway)

lemma ceil_pos_of_away_zero {A s t : ℝ} (hApos : 0 < A) (hspos : 0 < s)
    (ht : 0 ≤ t) (haway : AwayFromIntegers (A * s) t) :
    0 < Int.ceil t := by
  have hAst_pos : 0 < A * s := mul_pos hApos hspos
  have htpos : 0 < t := by
    have h0 : A * s ≤ t := by
      simpa [abs_of_nonneg ht] using haway 0
    exact hAst_pos.trans_le h0
  exact Int.ceil_pos.mpr htpos

lemma ceil_lower_one_plus {t : ℝ} (htpos : 0 < t) :
    (1 + t) / 2 ≤ (Int.ceil t : ℝ) := by
  by_cases ht1 : t ≤ 1
  · have hceil_one : (1 : ℝ) ≤ (Int.ceil t : ℝ) := by
      exact_mod_cast (Int.ceil_pos.mpr htpos)
    linarith
  · have hceil : t ≤ (Int.ceil t : ℝ) := Int.le_ceil t
    linarith

lemma ceil_scaled_square_gap_le {t : ℝ} (ht : 0 ≤ t) :
    (2 * Real.pi * (Int.ceil t : ℝ)) ^ 2 - (2 * Real.pi * t) ^ 2 ≤
      (2 * Real.pi) ^ 2 * (2 * (1 + t)) := by
  let n : ℝ := Int.ceil t
  have hn_ge : t ≤ n := by simpa [n] using Int.le_ceil t
  have hn_sub_le : n - t ≤ 1 := by simpa [n] using ceil_sub_le_one t
  have hsum_nonneg : 0 ≤ n + t := by linarith
  have hsum_le : n + t ≤ 2 * (1 + t) := by
    have hn_le : n ≤ t + 1 := by linarith
    linarith
  have hprod : (n - t) * (n + t) ≤ 2 * (1 + t) := by
    calc
      (n - t) * (n + t) ≤ 1 * (n + t) :=
        mul_le_mul_of_nonneg_right hn_sub_le hsum_nonneg
      _ ≤ 1 * (2 * (1 + t)) := mul_le_mul_of_nonneg_left hsum_le (by norm_num)
      _ = 2 * (1 + t) := by ring
  have hc_nonneg : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  calc
    (2 * Real.pi * (Int.ceil t : ℝ)) ^ 2 - (2 * Real.pi * t) ^ 2
        = (2 * Real.pi) ^ 2 * ((n - t) * (n + t)) := by
          dsimp [n]
          ring
    _ ≤ (2 * Real.pi) ^ 2 * (2 * (1 + t)) :=
      mul_le_mul_of_nonneg_left hprod hc_nonneg

lemma ceil_scaled_square_gap_pos_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    0 < (2 * Real.pi * (Int.ceil t : ℝ)) ^ 2 - (2 * Real.pi * t) ^ 2 := by
  have hceil_gap : 0 < (Int.ceil t : ℝ) - t :=
    ceil_sub_pos_of_away hApos hspos haway
  have hceil_gt : t < (Int.ceil t : ℝ) := by linarith
  have htwopipos : 0 < 2 * Real.pi := by positivity
  have hleft_lt : 2 * Real.pi * t < 2 * Real.pi * (Int.ceil t : ℝ) :=
    mul_lt_mul_of_pos_left hceil_gt htwopipos
  have hleft_nonneg : 0 ≤ 2 * Real.pi * t := by positivity
  have hright_pos : 0 < 2 * Real.pi * (Int.ceil t : ℝ) :=
    hleft_nonneg.trans_lt hleft_lt
  have hsq_lt : (2 * Real.pi * t) ^ 2 < (2 * Real.pi * (Int.ceil t : ℝ)) ^ 2 := by
    exact sq_lt_sq.mpr
      (by simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_pos.le] using hleft_lt)
  linarith

lemma ceil_scaled_lower_one_plus {t : ℝ} (htpos : 0 < t) :
    Real.pi * (1 + t) ≤ 2 * Real.pi * (Int.ceil t : ℝ) := by
  have hceil := ceil_lower_one_plus htpos
  have htwopi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hceil htwopi_nonneg
  nlinarith

lemma aNat_ceil (t : ℝ) (hceil_nonneg : 0 ≤ Int.ceil t) :
    aNat (Int.ceil t).toNat = 2 * Real.pi * (Int.ceil t : ℝ) := by
  unfold aNat
  have hcast : (((Int.ceil t).toNat : ℕ) : ℝ) = (Int.ceil t : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hceil_nonneg)
  rw [hcast]

lemma bOfT_le_aNat_ceil {t : ℝ} (ht : 0 ≤ t) :
    bOfT t ≤ aNat (Int.ceil t).toNat := by
  have hceil_cast_nonneg : (0 : ℝ) ≤ (Int.ceil t : ℝ) := le_trans ht (Int.le_ceil t)
  have hceil_nonneg : 0 ≤ Int.ceil t := by exact_mod_cast hceil_cast_nonneg
  rw [aNat_ceil t hceil_nonneg]
  unfold bOfT
  exact mul_le_mul_of_nonneg_left (Int.le_ceil t) (by positivity)

lemma ceil_left_square_gap_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2 := by
  have hba := bOfT_le_aNat_ceil ht
  have hb_nonneg : 0 ≤ bOfT t := bOfT_nonneg ht
  have hsquare : (bOfT t) ^ 2 ≤ (aNat (Int.ceil t).toNat) ^ 2 :=
    sq_le_sq' (by linarith) hba
  linarith

lemma ceil_left_square_gap_le {t : ℝ} (ht : 0 ≤ t) :
    (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2 ≤
      (2 * Real.pi) ^ 2 * (2 * (1 + t)) := by
  have hceil_cast_nonneg : (0 : ℝ) ≤ (Int.ceil t : ℝ) := le_trans ht (Int.le_ceil t)
  have hceil_nonneg : 0 ≤ Int.ceil t := by exact_mod_cast hceil_cast_nonneg
  rw [aNat_ceil t hceil_nonneg]
  unfold bOfT
  exact ceil_scaled_square_gap_le ht

lemma ceil_left_square_gap_pos_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    0 < (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2 := by
  have hceil_pos := ceil_pos_of_away_zero hApos hspos ht haway
  rw [aNat_ceil t hceil_pos.le]
  unfold bOfT
  exact ceil_scaled_square_gap_pos_of_away hApos hspos ht haway

/-- The positive square gap for the ceiling term, `a_ceil^2 - b^2`. -/
noncomputable def ceilLeftGap (t : ℝ) : ℝ :=
  (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2

/--
The normalized ceiling-term base.  Under the away hypothesis this lies in the
upper half-plane and tends to `-1` as the away parameter grows.
-/
noncomputable def ceilLeftBase (s t : ℝ) : ℂ :=
  (-1 : ℂ) + zeta s (aNat (Int.ceil t).toNat) / (ceilLeftGap t : ℂ)

/-- The positive-side square gap `a_m^2 - b^2` for an arbitrary natural index. -/
noncomputable def leftGap (t : ℝ) (m : ℕ) : ℝ :=
  (aNat m) ^ 2 - (bOfT t) ^ 2

/-- The normalized left-branch base for an arbitrary natural index. -/
noncomputable def leftBase (s t : ℝ) (m : ℕ) : ℂ :=
  (-1 : ℂ) + zeta s (aNat m) / (leftGap t m : ℂ)

/-- The square gap `b^2 - a_m^2` for the right-branch case. -/
noncomputable def rightGap (t : ℝ) (m : ℕ) : ℝ :=
  (bOfT t) ^ 2 - (aNat m) ^ 2

/-- The normalized right-branch base for an arbitrary natural index. -/
noncomputable def rightBase (s t : ℝ) (m : ℕ) : ℂ :=
  (1 : ℂ) + zeta s (aNat m) / (rightGap t m : ℂ)

lemma leftGap_pos {t : ℝ} {m : ℕ} (hleft : bOfT t < aNat m) (hb : 0 ≤ bOfT t) :
    0 < leftGap t m := by
  unfold leftGap
  have ha_pos : 0 < aNat m := lt_of_le_of_lt hb hleft
  have hsq : (bOfT t) ^ 2 < (aNat m) ^ 2 := by
    exact sq_lt_sq.mpr (by simpa [abs_of_nonneg hb, abs_of_nonneg ha_pos.le] using hleft)
  linarith

lemma rightGap_pos {t : ℝ} {m : ℕ} (hright : aNat m < bOfT t) (ha : 0 ≤ aNat m) :
    0 < rightGap t m := by
  unfold rightGap
  have hb_pos : 0 < bOfT t := lt_of_le_of_lt ha hright
  have hsq : (aNat m) ^ 2 < (bOfT t) ^ 2 := by
    exact sq_lt_sq.mpr (by simpa [abs_of_nonneg ha, abs_of_nonneg hb_pos.le] using hright)
  linarith

lemma ceilLeftGap_pos_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    0 < ceilLeftGap t := by
  simpa [ceilLeftGap] using ceil_left_square_gap_pos_of_away hApos hspos ht haway

lemma ceilLeftGap_le {t : ℝ} (ht : 0 ≤ t) :
    ceilLeftGap t ≤ (2 * Real.pi) ^ 2 * (2 * (1 + t)) := by
  simpa [ceilLeftGap] using ceil_left_square_gap_le ht

lemma aNat_ceil_lower_one_plus_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    Real.pi * (1 + t) ≤ aNat (Int.ceil t).toNat := by
  have hAst_pos : 0 < A * s := mul_pos hApos hspos
  have htpos : 0 < t := by
    have h0 : A * s ≤ t := by
      simpa [abs_of_nonneg ht] using haway 0
    exact hAst_pos.trans_le h0
  have hceil_pos := ceil_pos_of_away_zero hApos hspos ht haway
  rw [aNat_ceil t hceil_pos.le]
  exact ceil_scaled_lower_one_plus htpos

lemma two_pi_le_aNat_ceil_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    2 * Real.pi ≤ aNat (Int.ceil t).toNat := by
  have hceil_pos := ceil_pos_of_away_zero hApos hspos ht haway
  rw [aNat_ceil t hceil_pos.le]
  have hceil_one : (1 : ℝ) ≤ (Int.ceil t : ℝ) := by
    exact_mod_cast (Int.add_one_le_iff.mpr hceil_pos)
  nlinarith [Real.pi_pos]

lemma ceil_lam_complex_norm_le_two_mul {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    ‖Complex.ofReal s + Complex.I * Complex.ofReal (aNat (Int.ceil t).toNat)‖ ≤
      2 * aNat (Int.ceil t).toNat := by
  exact lam_complex_norm_le_two_mul hsle hspos.le
    (two_pi_le_aNat_ceil_of_away hApos hspos ht haway)

lemma ceil_scaled_separation_aNat {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    (2 * Real.pi * A) * s ≤ |aNat (Int.ceil t).toNat - bOfT t| := by
  have hceil_pos := ceil_pos_of_away_zero hApos hspos ht haway
  have hsep := scaled_integer_separation (Int.ceil t) haway
  simpa [aNat_ceil t hceil_pos.le, bOfT] using hsep

lemma zeta_div_ceilLeftGap_le {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1)
    (ht : 0 ≤ t) (haway : AwayFromIntegers (A * s) t) :
    ‖zeta s (aNat (Int.ceil t).toNat) / (ceilLeftGap t : ℂ)‖ ≤
      3 / (2 * Real.pi * A) := by
  have hDpos := ceilLeftGap_pos_of_away hApos hspos ht haway
  have hLpos : 0 < 2 * Real.pi * A := by positivity
  have ha : 2 * Real.pi ≤ aNat (Int.ceil t).toNat :=
    two_pi_le_aNat_ceil_of_away hApos hspos ht haway
  have hb : 0 ≤ bOfT t := bOfT_nonneg ht
  have hsep : (2 * Real.pi * A) * s ≤ |aNat (Int.ceil t).toNat - bOfT t| :=
    ceil_scaled_separation_aNat hApos hspos ht haway
  have hz := zeta_div_D_le (s := s) (a := aNat (Int.ceil t).toNat) (b := bOfT t)
    (L := 2 * Real.pi * A) hspos hsle hLpos ha hb hsep
  change ‖zeta s (aNat (Int.ceil t).toNat) / (Complex.ofReal (ceilLeftGap t))‖ ≤
    3 / (2 * Real.pi * A)
  have hDexprpos : 0 < (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2 := by
    simpa [ceilLeftGap] using hDpos
  rw [ceilLeftGap]
  rw [show (((aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2 : ℝ) : ℂ) =
      (Complex.ofReal |(aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2|) by
    rw [abs_of_pos hDexprpos]]
  exact hz

lemma ceilLeftGap_lower_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    aNat (Int.ceil t).toNat * (2 * Real.pi * A) * s ≤ ceilLeftGap t := by
  have hDpos := ceilLeftGap_pos_of_away hApos hspos ht haway
  have ha : 0 ≤ aNat (Int.ceil t).toNat := by
    unfold aNat
    positivity
  have hb : 0 ≤ bOfT t := bOfT_nonneg ht
  have hsep := ceil_scaled_separation_aNat hApos hspos ht haway
  have hDlower := D_lower (a := aNat (Int.ceil t).toNat) (b := bOfT t)
    (L := 2 * Real.pi * A) (s := s) ha hb hsep
  have hDexprpos : 0 < (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2 := by
    simpa [ceilLeftGap] using hDpos
  simpa [ceilLeftGap, abs_of_pos hDexprpos] using hDlower

lemma twopi_mul_twopi_mul_ge_of_two_le {A : ℝ} (hAge : 2 ≤ A) :
    32 ≤ (2 * Real.pi) * (2 * Real.pi * A) := by
  have htwopi_ge4 : (4 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have hsecond : (8 : ℝ) ≤ 2 * Real.pi * A := by
    have hsecond' := mul_le_mul htwopi_ge4 hAge (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    norm_num at hsecond'
    exact hsecond'
  have hprod := mul_le_mul htwopi_ge4 hsecond (by norm_num : (0 : ℝ) ≤ 8)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  norm_num at hprod
  simpa [mul_assoc] using hprod

lemma ceilLeftGap_ge_twenty_four_sq {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    24 * s ^ 2 ≤ ceilLeftGap t := by
  have ha : 2 * Real.pi ≤ aNat (Int.ceil t).toNat :=
    two_pi_le_aNat_ceil_of_away hApos hspos ht haway
  have hlower := ceilLeftGap_lower_of_away hApos hspos ht haway
  have hcoef : 32 ≤ (2 * Real.pi) * (2 * Real.pi * A) :=
    twopi_mul_twopi_mul_ge_of_two_le hAge
  have hsnonneg : 0 ≤ s := hspos.le
  have hleft_to_base : 24 * s ^ 2 ≤ (2 * Real.pi) * (2 * Real.pi * A) * s := by
    have h24s : 24 * s ^ 2 ≤ 24 * s := by nlinarith
    have h32s : 24 * s ≤ 32 * s := by nlinarith
    have hcoef_s : 32 * s ≤ ((2 * Real.pi) * (2 * Real.pi * A)) * s :=
      mul_le_mul_of_nonneg_right hcoef hsnonneg
    nlinarith
  have hbase_to_a : (2 * Real.pi) * (2 * Real.pi * A) * s ≤
      aNat (Int.ceil t).toNat * (2 * Real.pi * A) * s := by
    have hfactor : 0 ≤ (2 * Real.pi * A) * s := by positivity
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right ha hfactor
  exact (hleft_to_base.trans hbase_to_a).trans hlower

lemma eight_mul_aNat_ceil_mul_s_le_gap {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    8 * (aNat (Int.ceil t).toNat * s) ≤ ceilLeftGap t := by
  have ha_nonneg : 0 ≤ aNat (Int.ceil t).toNat := by
    unfold aNat
    positivity
  have hs_nonneg : 0 ≤ s := hspos.le
  have hcoef : 8 ≤ 2 * Real.pi * A := by
    have htwopi_ge4 : (4 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
    have h := mul_le_mul htwopi_ge4 hAge (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    norm_num at h
    exact h
  have hmul : 8 * (aNat (Int.ceil t).toNat * s) ≤
      (2 * Real.pi * A) * (aNat (Int.ceil t).toNat * s) :=
    mul_le_mul_of_nonneg_right hcoef (mul_nonneg ha_nonneg hs_nonneg)
  have hlower := ceilLeftGap_lower_of_away hApos hspos ht haway
  nlinarith

lemma ceil_left_asq_d5_le_eighth {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    s * (aNat (Int.ceil t).toNat) ^ 2 * powNegFiveHalves (ceilLeftGap t) ≤
      (1 / 8 : ℝ) * aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) := by
  let a := aNat (Int.ceil t).toNat
  let D := ceilLeftGap t
  have h8 : 8 * (a * s) ≤ D := by
    simpa [a, D] using eight_mul_aNat_ceil_mul_s_le_gap hAge hApos hspos ht haway
  have ha_nonneg : 0 ≤ a := by
    dsimp [a, aNat]
    positivity
  have hDpos : 0 < D := by simpa [D] using ceilLeftGap_pos_of_away hApos hspos ht haway
  have hd5_nonneg : 0 ≤ powNegFiveHalves D := (powNegFiveHalves_pos hDpos).le
  have hfactor_nonneg : 0 ≤ a * powNegFiveHalves D := mul_nonneg ha_nonneg hd5_nonneg
  have hmul := mul_le_mul_of_nonneg_right h8 hfactor_nonneg
  have hDmul : D * powNegFiveHalves D = powNegThreeHalves D :=
    mul_powNegFiveHalves_eq_powNegThreeHalves hDpos
  dsimp [a, D] at hmul hDmul ⊢
  nlinarith

lemma ceil_left_positive_correction_le_half {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    12 * aNat (Int.ceil t).toNat * s ^ 2 * powNegFiveHalves (ceilLeftGap t) ≤
      (1 / 2 : ℝ) * aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) := by
  have ha : 0 ≤ aNat (Int.ceil t).toNat := by
    unfold aNat
    positivity
  exact left_positive_correction_le_half ha
    (ceilLeftGap_pos_of_away hApos hspos ht haway)
    (ceilLeftGap_ge_twenty_four_sq hAge hApos hspos hsle ht haway)

lemma ceil_left_main_bound {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    -aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) +
        12 * aNat (Int.ceil t).toNat * s ^ 2 * powNegFiveHalves (ceilLeftGap t) ≤
      -(1 / 2 : ℝ) * aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) := by
  have hcorr := ceil_left_positive_correction_le_half hAge hApos hspos hsle ht haway
  linarith

lemma twopi_sq_two_mul_one_add_le_128 {t : ℝ} (ht : 0 ≤ t) :
    (2 * Real.pi) ^ 2 * (2 * (1 + t)) ≤ 128 * (1 + t) := by
  have htwopi_le8 : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
  have hsq : (2 * Real.pi) ^ 2 ≤ 8 ^ 2 := by
    exact sq_le_sq' (by nlinarith [Real.pi_pos] : (-8 : ℝ) ≤ 2 * Real.pi) htwopi_le8
  nlinarith

lemma ceil_left_main_magnitude_lower {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    (1 / 2000 : ℝ) * invSqrtOnePlus t ≤
      aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) := by
  have hUpos : 0 < 1 + t := by linarith
  have hU_nonneg : 0 ≤ 1 + t := hUpos.le
  have ha_pi := aNat_ceil_lower_one_plus_of_away hApos hspos ht haway
  have htwoU_le : 2 * (1 + t) ≤ Real.pi * (1 + t) :=
    mul_le_mul_of_nonneg_right Real.two_le_pi hU_nonneg
  have ha : 2 * (1 + t) ≤ aNat (Int.ceil t).toNat := htwoU_le.trans ha_pi
  have hDpos := ceilLeftGap_pos_of_away hApos hspos ht haway
  have hDle : ceilLeftGap t ≤ 128 * (1 + t) :=
    (ceilLeftGap_le ht).trans (twopi_sq_two_mul_one_add_le_128 ht)
  simpa [invSqrtOnePlus] using
    main_magnitude_lower_of_bounds (a := aNat (Int.ceil t).toNat)
      (D := ceilLeftGap t) (U := 1 + t) hUpos ha hDpos hDle

lemma ceil_left_main_quantitative_bound {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    -aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) +
        12 * aNat (Int.ceil t).toNat * s ^ 2 * powNegFiveHalves (ceilLeftGap t) ≤
      -(1 / 4000 : ℝ) * invSqrtOnePlus t := by
  have hmain := ceil_left_main_bound hAge hApos hspos hsle ht haway
  have hmag := ceil_left_main_magnitude_lower hApos hspos ht haway
  have hneg : -(1 / 2 : ℝ) * aNat (Int.ceil t).toNat *
        powNegThreeHalves (ceilLeftGap t) ≤
      -(1 / 4000 : ℝ) * invSqrtOnePlus t := by
    nlinarith
  exact hmain.trans hneg

lemma ceilLeftBase_im_nonneg {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    0 ≤ (ceilLeftBase s t).im := by
  have _hDpos := ceilLeftGap_pos_of_away hApos hspos ht haway
  have _ha_nonneg : 0 ≤ aNat (Int.ceil t).toNat := by
    unfold aNat
    positivity
  unfold ceilLeftBase
  simp only [Complex.add_im, Complex.neg_im, Complex.one_im]
  rw [zeta_div_ofReal_im]
  positivity

lemma ceilLeftBase_im_pos {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    0 < (ceilLeftBase s t).im := by
  have hDpos := ceilLeftGap_pos_of_away hApos hspos ht haway
  have ha : 2 * Real.pi ≤ aNat (Int.ceil t).toNat :=
    two_pi_le_aNat_ceil_of_away hApos hspos ht haway
  have hapos : 0 < aNat (Int.ceil t).toNat := lt_of_lt_of_le (by positivity) ha
  unfold ceilLeftBase
  simp only [Complex.add_im, Complex.neg_im, Complex.one_im]
  rw [zeta_div_ofReal_im]
  positivity

lemma ceilLeftBase_ne_zero {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    ceilLeftBase s t ≠ 0 := by
  intro hzero
  have himpos := ceilLeftBase_im_pos hApos hspos ht haway
  have himzero : (ceilLeftBase s t).im = 0 := by simp [hzero]
  linarith

lemma ceilLeftBase_dist_le {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1)
    (ht : 0 ≤ t) (haway : AwayFromIntegers (A * s) t) :
    dist (ceilLeftBase s t) (-1 : ℂ) ≤ 3 / (2 * Real.pi * A) := by
  have hz := zeta_div_ceilLeftGap_le hApos hspos hsle ht haway
  simpa [ceilLeftBase, dist_eq_norm] using hz

lemma lam_zero (s : ℝ) : lam s 0 = (s : ℂ) := by
  unfold lam
  simp

lemma q_zero (s t : ℝ) :
    q s t 0 = (s ^ 2 + (2 * Real.pi * t) ^ 2 : ℝ) := by
  unfold q lam
  simp

lemma lam_ofNat (s : ℝ) (m : ℕ) :
    lam s (m : ℤ) = Complex.ofReal s + Complex.I * Complex.ofReal (aNat m) := by
  unfold lam aNat
  push_cast
  ring

lemma lam_ceil_of_away {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    lam s (Int.ceil t) = Complex.ofReal s + Complex.I * Complex.ofReal (aNat (Int.ceil t).toNat) := by
  have hceil_pos := ceil_pos_of_away_zero hApos hspos ht haway
  have hceil_nat : (((Int.ceil t).toNat : ℕ) : ℤ) = Int.ceil t :=
    Int.toNat_of_nonneg hceil_pos.le
  rw [← hceil_nat]
  exact lam_ofNat s (Int.ceil t).toNat

lemma lam_neg (s : ℝ) (m : ℤ) : lam s (-m) = star (lam s m) := by
  unfold lam
  push_cast
  simp

lemma q_ofNat (s t : ℝ) (m : ℕ) :
    q s t (m : ℤ) = Complex.ofReal ((bOfT t) ^ 2 - (aNat m) ^ 2) + zeta s (aNat m) := by
  unfold q bOfT zeta
  rw [lam_ofNat]
  unfold aNat
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma q_ofNat_left (s t : ℝ) (m : ℕ) :
    q s t (m : ℤ) = -(Complex.ofReal ((aNat m) ^ 2 - (bOfT t) ^ 2)) + zeta s (aNat m) := by
  rw [q_ofNat]
  push_cast
  ring

lemma q_ofNat_left_factor {s t D : ℝ} {m : ℕ}
    (hD : D = (aNat m) ^ 2 - (bOfT t) ^ 2) (hDne : D ≠ 0) :
    q s t (m : ℤ) = (D : ℂ) * (-1 + zeta s (aNat m) / (D : ℂ)) := by
  rw [q_ofNat_left]
  rw [hD]
  have hDexpr : (aNat m) ^ 2 - (bOfT t) ^ 2 ≠ 0 := by
    rw [← hD]
    exact hDne
  have hDexprC : (((aNat m) ^ 2 - (bOfT t) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hDexpr
  rw [div_eq_mul_inv]
  ring_nf
  rw [mul_comm (((aNat m) ^ 2 - (bOfT t) ^ 2 : ℝ) : ℂ) (zeta s (aNat m))]
  rw [mul_assoc, mul_inv_cancel₀ hDexprC, mul_one]

lemma q_ofNat_right_factor {s t D : ℝ} {m : ℕ}
    (hD : D = (bOfT t) ^ 2 - (aNat m) ^ 2) (hDne : D ≠ 0) :
    q s t (m : ℤ) = (D : ℂ) * (1 + zeta s (aNat m) / (D : ℂ)) := by
  rw [q_ofNat]
  rw [hD]
  have hDexpr : (bOfT t) ^ 2 - (aNat m) ^ 2 ≠ 0 := by
    rw [← hD]
    exact hDne
  have hDexprC : (((bOfT t) ^ 2 - (aNat m) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hDexpr
  rw [div_eq_mul_inv]
  ring_nf
  rw [mul_comm (((bOfT t) ^ 2 - (aNat m) ^ 2 : ℝ) : ℂ) (zeta s (aNat m))]
  rw [mul_assoc, mul_inv_cancel₀ hDexprC, mul_one]

lemma q_neg (s t : ℝ) (m : ℤ) : q s t (-m) = star (q s t m) := by
  unfold q
  rw [lam_neg]
  simp

lemma q_im (s t : ℝ) (m : ℤ) :
    (q s t m).im = 4 * Real.pi * s * (m : ℝ) := by
  unfold q lam
  simp [pow_two]
  ring

lemma q_arg_ne_pi {s t : ℝ} {m : ℤ} (hs : 0 < s) (hm : m ≠ 0) :
    Complex.arg (q s t m) ≠ Real.pi := by
  rw [Ne, Complex.arg_eq_pi_iff]
  intro h
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have him_ne : (q s t m).im ≠ 0 := by
    rw [q_im]
    positivity
  exact him_ne h.2

lemma q_ceil_left_factor {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    q s t (Int.ceil t) = (ceilLeftGap t : ℂ) * ceilLeftBase s t := by
  have hceil_pos := ceil_pos_of_away_zero hApos hspos ht haway
  have hceil_nat : (((Int.ceil t).toNat : ℕ) : ℤ) = Int.ceil t :=
    Int.toNat_of_nonneg hceil_pos.le
  rw [← hceil_nat]
  simpa [ceilLeftGap, ceilLeftBase] using q_ofNat_left_factor
    (D := (aNat (Int.ceil t).toNat) ^ 2 - (bOfT t) ^ 2)
    rfl (ne_of_gt (ceil_left_square_gap_pos_of_away hApos hspos ht haway))

lemma q_ofNat_left_factor_base {s t : ℝ} {m : ℕ}
    (hDne : leftGap t m ≠ 0) :
    q s t (m : ℤ) = (leftGap t m : ℂ) * leftBase s t m := by
  simpa [leftGap, leftBase] using q_ofNat_left_factor (s := s) (t := t)
    (D := (aNat m) ^ 2 - (bOfT t) ^ 2) (m := m) rfl hDne

lemma q_ofNat_right_factor_base {s t : ℝ} {m : ℕ}
    (hDne : rightGap t m ≠ 0) :
    q s t (m : ℤ) = (rightGap t m : ℂ) * rightBase s t m := by
  simpa [rightGap, rightBase] using q_ofNat_right_factor (s := s) (t := t)
    (D := (bOfT t) ^ 2 - (aNat m) ^ 2) (m := m) rfl hDne

lemma Tterm_ofNat_formula (s t : ℝ) (m : ℕ) :
    Tterm s t (m : ℤ) =
      ((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
          cpowR (Complex.ofReal ((bOfT t) ^ 2 - (aNat m) ^ 2) + zeta s (aNat m))
            (-(3 / 2 : ℝ)) +
        2 * Complex.ofReal s *
          (-cpowR (Complex.ofReal ((bOfT t) ^ 2 - (aNat m) ^ 2) + zeta s (aNat m))
              (-(3 / 2 : ℝ)) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
              cpowR (Complex.ofReal ((bOfT t) ^ 2 - (aNat m) ^ 2) + zeta s (aNat m))
                (-(5 / 2 : ℝ)))).re := by
  unfold Tterm
  rw [lam_ofNat, q_ofNat]

lemma cpowR_ofReal_nonneg {D a : ℝ} (hD : 0 ≤ D) :
    cpowR (D : ℂ) a = (D ^ a : ℝ) := by
  unfold cpowR
  exact (Complex.ofReal_cpow hD a).symm

lemma cpowR_pos_mul {D : ℝ} (hD : 0 < D) {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    cpowR ((D : ℂ) * z) a = Complex.ofReal (D ^ a) * cpowR z a := by
  unfold cpowR
  have hD0 : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  rw [Complex.ofReal_cpow hD.le]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hD0 hz),
    Complex.cpow_def_of_ne_zero hD0, Complex.cpow_def_of_ne_zero hz]
  rw [Complex.log_ofReal_mul hD hz]
  rw [← Complex.ofReal_log hD.le]
  rw [← Complex.exp_add]
  congr 1
  ring

lemma cpowR_conj {z : ℂ} {a : ℝ} (harg : Complex.arg z ≠ Real.pi) :
    cpowR (star z) a = star (cpowR z a) := by
  unfold cpowR
  by_cases hz : z = 0
  · simp [hz, Complex.cpow_def]
  · rw [Complex.cpow_def, Complex.cpow_def]
    simp [hz]
    rw [Complex.log_conj z harg]
    rw [← Complex.exp_conj]
    congr 1
    simp

lemma cpowR_q_ceil_left {A s t a : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    cpowR (q s t (Int.ceil t)) a =
      Complex.ofReal ((ceilLeftGap t) ^ a) * cpowR (ceilLeftBase s t) a := by
  rw [q_ceil_left_factor hApos hspos ht haway]
  exact cpowR_pos_mul (ceilLeftGap_pos_of_away hApos hspos ht haway)
    (ceilLeftBase_ne_zero hApos hspos ht haway) a

lemma leftBase_im_pos {s t : ℝ} {m : ℕ}
    (hs : 0 < s) (hDpos : 0 < leftGap t m) (ha : 0 < aNat m) :
    0 < (leftBase s t m).im := by
  unfold leftBase
  simp only [Complex.add_im, Complex.neg_im, Complex.one_im]
  rw [zeta_div_ofReal_im]
  positivity

lemma leftBase_im_nonneg {s t : ℝ} {m : ℕ}
    (hs : 0 < s) (hDpos : 0 < leftGap t m) (ha : 0 ≤ aNat m) :
    0 ≤ (leftBase s t m).im := by
  unfold leftBase
  simp only [Complex.add_im, Complex.neg_im, Complex.one_im]
  rw [zeta_div_ofReal_im]
  positivity

lemma leftBase_ne_zero {s t : ℝ} {m : ℕ}
    (hs : 0 < s) (hDpos : 0 < leftGap t m) (ha : 0 < aNat m) :
    leftBase s t m ≠ 0 := by
  intro hzero
  have himpos := leftBase_im_pos hs hDpos ha
  have himzero : (leftBase s t m).im = 0 := by simp [hzero]
  linarith

lemma cpowR_q_ofNat_left {s t a : ℝ} {m : ℕ}
    (hDpos : 0 < leftGap t m) (hbase_ne : leftBase s t m ≠ 0) :
    cpowR (q s t (m : ℤ)) a =
      Complex.ofReal ((leftGap t m) ^ a) * cpowR (leftBase s t m) a := by
  rw [q_ofNat_left_factor_base (ne_of_gt hDpos)]
  exact cpowR_pos_mul hDpos hbase_ne a

lemma rightBase_ne_zero {s t : ℝ} {m : ℕ}
    (hclose : dist (rightBase s t m) (1 : ℂ) < 1) :
    rightBase s t m ≠ 0 := by
  intro hzero
  have hdist : dist (rightBase s t m) (1 : ℂ) = 1 := by simp [hzero, dist_eq_norm]
  linarith

lemma cpowR_q_ofNat_right {s t a : ℝ} {m : ℕ}
    (hDpos : 0 < rightGap t m) (hbase_ne : rightBase s t m ≠ 0) :
    cpowR (q s t (m : ℤ)) a =
      Complex.ofReal ((rightGap t m) ^ a) * cpowR (rightBase s t m) a := by
  rw [q_ofNat_right_factor_base (ne_of_gt hDpos)]
  exact cpowR_pos_mul hDpos hbase_ne a

lemma Tterm_ofNat_left_factor_formula {s t : ℝ} {m : ℕ}
    (hDpos : 0 < leftGap t m) (hbase_ne : leftBase s t m ≠ 0) :
    Tterm s t (m : ℤ) =
      ((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
          (Complex.ofReal ((leftGap t m) ^ (-(3 / 2 : ℝ))) *
            cpowR (leftBase s t m) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal ((leftGap t m) ^ (-(3 / 2 : ℝ))) *
              cpowR (leftBase s t m) (-(3 / 2 : ℝ))) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
              (Complex.ofReal ((leftGap t m) ^ (-(5 / 2 : ℝ))) *
                cpowR (leftBase s t m) (-(5 / 2 : ℝ))))).re := by
  unfold Tterm
  rw [lam_ofNat]
  rw [cpowR_q_ofNat_left hDpos hbase_ne]
  rw [cpowR_q_ofNat_left hDpos hbase_ne]

lemma Tterm_ofNat_right_factor_formula {s t : ℝ} {m : ℕ}
    (hDpos : 0 < rightGap t m) (hbase_ne : rightBase s t m ≠ 0) :
    Tterm s t (m : ℤ) =
      ((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
          (Complex.ofReal ((rightGap t m) ^ (-(3 / 2 : ℝ))) *
            cpowR (rightBase s t m) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal ((rightGap t m) ^ (-(3 / 2 : ℝ))) *
              cpowR (rightBase s t m) (-(3 / 2 : ℝ))) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
              (Complex.ofReal ((rightGap t m) ^ (-(5 / 2 : ℝ))) *
                cpowR (rightBase s t m) (-(5 / 2 : ℝ))))).re := by
  unfold Tterm
  rw [lam_ofNat]
  rw [cpowR_q_ofNat_right hDpos hbase_ne]
  rw [cpowR_q_ofNat_right hDpos hbase_ne]

lemma leftBase_dist_le {s t L : ℝ} {m : ℕ}
    (hspos : 0 < s) (hsle : s ≤ 1) (hLpos : 0 < L)
    (ha : 2 * Real.pi ≤ aNat m) (hb : 0 ≤ bOfT t)
    (hDpos : 0 < leftGap t m)
    (hsep : L * s ≤ |aNat m - bOfT t|) :
    dist (leftBase s t m) (-1 : ℂ) ≤ 3 / L := by
  have hz := zeta_div_D_le (s := s) (a := aNat m) (b := bOfT t) (L := L)
    hspos hsle hLpos ha hb hsep
  change dist ((-1 : ℂ) + zeta s (aNat m) / (leftGap t m : ℂ)) (-1 : ℂ) ≤ 3 / L
  have hDexprpos : 0 < (aNat m) ^ 2 - (bOfT t) ^ 2 := by simpa [leftGap] using hDpos
  simpa [leftGap, leftBase, dist_eq_norm, abs_of_pos hDexprpos] using hz

lemma rightBase_dist_le {s t L : ℝ} {m : ℕ}
    (hspos : 0 < s) (hsle : s ≤ 1) (hLpos : 0 < L)
    (ha : 2 * Real.pi ≤ aNat m) (hb : 0 ≤ bOfT t)
    (hDpos : 0 < rightGap t m)
    (hsep : L * s ≤ |aNat m - bOfT t|) :
    dist (rightBase s t m) (1 : ℂ) ≤ 3 / L := by
  have hz := zeta_div_D_le (s := s) (a := aNat m) (b := bOfT t) (L := L)
    hspos hsle hLpos ha hb hsep
  change dist ((1 : ℂ) + zeta s (aNat m) / (rightGap t m : ℂ)) (1 : ℂ) ≤ 3 / L
  have hDexprpos : 0 < (bOfT t) ^ 2 - (aNat m) ^ 2 := by simpa [rightGap] using hDpos
  have habs : |(aNat m) ^ 2 - (bOfT t) ^ 2| = rightGap t m := by
    unfold rightGap
    rw [show (aNat m) ^ 2 - (bOfT t) ^ 2 = -((bOfT t) ^ 2 - (aNat m) ^ 2) by ring]
    rw [abs_neg, abs_of_pos hDexprpos]
  simpa [rightBase, dist_eq_norm, habs] using hz

lemma rightGap_mul_norm_rightBase_sub_one_le {s t : ℝ} {m : ℕ}
    (hspos : 0 < s) (hsle : s ≤ 1)
    (ha : 2 * Real.pi ≤ aNat m) (hDpos : 0 < rightGap t m) :
    rightGap t m * ‖rightBase s t m - 1‖ ≤ 3 * aNat m * s := by
  have hz := zeta_norm_le hspos.le hsle ha
  calc
    rightGap t m * ‖rightBase s t m - 1‖ = ‖zeta s (aNat m)‖ := by
      unfold rightBase
      simp [sub_eq_add_neg, abs_of_pos hDpos]
      field_simp [hDpos.ne']
    _ ≤ 3 * aNat m * s := hz

lemma leftGap_lower_of_sep {s t L : ℝ} {m : ℕ}
    (ha0 : 0 ≤ aNat m) (hb : 0 ≤ bOfT t)
    (hDpos : 0 < leftGap t m)
    (hsep : L * s ≤ |aNat m - bOfT t|) :
    aNat m * L * s ≤ leftGap t m := by
  have hDlower := D_lower (a := aNat m) (b := bOfT t) (L := L) (s := s) ha0 hb hsep
  have hDexprpos : 0 < (aNat m) ^ 2 - (bOfT t) ^ 2 := by simpa [leftGap] using hDpos
  simpa [leftGap, abs_of_pos hDexprpos] using hDlower

lemma leftGap_ge_twenty_four_sq_of_sep {s t L : ℝ} {m : ℕ}
    (hLge8 : 8 ≤ L) (hspos : 0 < s) (hsle : s ≤ 1)
    (ha : 2 * Real.pi ≤ aNat m) (hb : 0 ≤ bOfT t)
    (hDpos : 0 < leftGap t m)
    (hsep : L * s ≤ |aNat m - bOfT t|) :
    24 * s ^ 2 ≤ leftGap t m := by
  have ha0 : 0 ≤ aNat m := (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hlower := leftGap_lower_of_sep (s := s) (t := t) (L := L) (m := m) ha0 hb hDpos hsep
  have hcoef : 32 ≤ aNat m * L := by
    have htwopi_ge4 : (4 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
    have hage4 : 4 ≤ aNat m := htwopi_ge4.trans ha
    have h := mul_le_mul hage4 hLge8 (by norm_num : (0 : ℝ) ≤ 8) ha0
    norm_num at h
    exact h
  have hsnonneg : 0 ≤ s := hspos.le
  have hleft_to_base : 24 * s ^ 2 ≤ aNat m * L * s := by
    have h24s : 24 * s ^ 2 ≤ 24 * s := by nlinarith
    have h32s : 24 * s ≤ 32 * s := by nlinarith
    have hcoef_s : 32 * s ≤ (aNat m * L) * s := mul_le_mul_of_nonneg_right hcoef hsnonneg
    nlinarith
  exact hleft_to_base.trans hlower

lemma left_asq_d5_le_eighth_of_sep {s t L : ℝ} {m : ℕ}
    (hLge8 : 8 ≤ L) (hspos : 0 < s)
    (ha : 2 * Real.pi ≤ aNat m) (hb : 0 ≤ bOfT t)
    (hDpos : 0 < leftGap t m)
    (hsep : L * s ≤ |aNat m - bOfT t|) :
    s * (aNat m) ^ 2 * powNegFiveHalves (leftGap t m) ≤
      (1 / 8 : ℝ) * aNat m * powNegThreeHalves (leftGap t m) := by
  let a := aNat m
  let D := leftGap t m
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hlower := leftGap_lower_of_sep (s := s) (t := t) (L := L) (m := m) ha0 hb hDpos hsep
  have h8 : 8 * (a * s) ≤ D := by
    have hmul : 8 * (a * s) ≤ L * (a * s) :=
      mul_le_mul_of_nonneg_right hLge8 (mul_nonneg ha0 hspos.le)
    dsimp [a, D]
    nlinarith
  have hDpos' : 0 < D := by simpa [D] using hDpos
  have hd5_nonneg : 0 ≤ powNegFiveHalves D := (powNegFiveHalves_pos hDpos').le
  have hfactor_nonneg : 0 ≤ a * powNegFiveHalves D := mul_nonneg ha0 hd5_nonneg
  have hmul := mul_le_mul_of_nonneg_right h8 hfactor_nonneg
  have hDmul : D * powNegFiveHalves D = powNegThreeHalves D :=
    mul_powNegFiveHalves_eq_powNegThreeHalves hDpos'
  dsimp [a, D] at hmul hDmul ⊢
  nlinarith

lemma Tterm_ceil_left_factor_formula {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    Tterm s t (Int.ceil t) =
      ((Complex.ofReal s + Complex.I * Complex.ofReal (aNat (Int.ceil t).toNat)) *
          (Complex.ofReal ((ceilLeftGap t) ^ (-(3 / 2 : ℝ))) *
            cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal ((ceilLeftGap t) ^ (-(3 / 2 : ℝ))) *
              cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ))) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat (Int.ceil t).toNat)) ^ 2 *
              (Complex.ofReal ((ceilLeftGap t) ^ (-(5 / 2 : ℝ))) *
                cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ))))).re := by
  unfold Tterm
  rw [lam_ceil_of_away hApos hspos ht haway]
  rw [cpowR_q_ceil_left hApos hspos ht haway]
  rw [cpowR_q_ceil_left hApos hspos ht haway]

lemma cos_three_pi_halves : Real.cos (Real.pi * (3 / 2 : ℝ)) = 0 := by
  rw [show Real.pi * (3 / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
  rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

lemma neg_sin_three_pi_halves : -Real.sin (Real.pi * (3 / 2 : ℝ)) = 1 := by
  rw [show Real.pi * (3 / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
  rw [Real.sin_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

lemma cos_five_pi_halves : Real.cos (Real.pi * (5 / 2 : ℝ)) = 0 := by
  rw [show Real.pi * (5 / 2 : ℝ) = 2 * Real.pi + Real.pi / 2 by ring]
  rw [Real.cos_add, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

lemma sin_five_pi_halves : Real.sin (Real.pi * (5 / 2 : ℝ)) = 1 := by
  rw [show Real.pi * (5 / 2 : ℝ) = 2 * Real.pi + Real.pi / 2 by ring]
  rw [Real.sin_add, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

lemma cpow_neg_one_neg_three_half :
    cpowR (-1 : ℂ) (-(3 / 2 : ℝ)) = Complex.I := by
  apply Complex.ext
  · unfold cpowR
    rw [Complex.cpow_ofReal_re]
    simpa [Complex.arg_neg_one] using cos_three_pi_halves
  · unfold cpowR
    rw [Complex.cpow_ofReal_im]
    simpa [Complex.arg_neg_one] using neg_sin_three_pi_halves

lemma cpow_neg_one_neg_five_half :
    cpowR (-1 : ℂ) (-(5 / 2 : ℝ)) = -Complex.I := by
  apply Complex.ext
  · unfold cpowR
    rw [Complex.cpow_ofReal_re]
    simpa [Complex.arg_neg_one] using cos_five_pi_halves
  · unfold cpowR
    rw [Complex.cpow_ofReal_im]
    simpa [Complex.arg_neg_one] using sin_five_pi_halves

lemma cpowR_neg_ofReal_neg_three_half {D : ℝ} (hD : 0 < D) :
    cpowR (-(D : ℂ)) (-(3 / 2 : ℝ)) =
      Complex.ofReal (D ^ (-(3 / 2 : ℝ))) * Complex.I := by
  have hnegC : -(D : ℂ) = ((-D : ℝ) : ℂ) := by norm_num
  apply Complex.ext
  · unfold cpowR
    rw [hnegC, Complex.cpow_ofReal_re]
    have hneg : (-D : ℝ) < 0 := by linarith
    rw [Complex.arg_ofReal_of_neg hneg]
    simp [abs_of_pos hD, cos_three_pi_halves]
  · unfold cpowR
    rw [hnegC, Complex.cpow_ofReal_im]
    have hneg : (-D : ℝ) < 0 := by linarith
    rw [Complex.arg_ofReal_of_neg hneg]
    simp [abs_of_pos hD, neg_sin_three_pi_halves]

lemma cpowR_neg_ofReal_neg_five_half {D : ℝ} (hD : 0 < D) :
    cpowR (-(D : ℂ)) (-(5 / 2 : ℝ)) =
      -Complex.ofReal (D ^ (-(5 / 2 : ℝ))) * Complex.I := by
  have hnegC : -(D : ℂ) = ((-D : ℝ) : ℂ) := by norm_num
  apply Complex.ext
  · unfold cpowR
    rw [hnegC, Complex.cpow_ofReal_re]
    have hneg : (-D : ℝ) < 0 := by linarith
    rw [Complex.arg_ofReal_of_neg hneg]
    simp [abs_of_pos hD, cos_five_pi_halves]
  · unfold cpowR
    rw [hnegC, Complex.cpow_ofReal_im]
    have hneg : (-D : ℝ) < 0 := by linarith
    rw [Complex.arg_ofReal_of_neg hneg]
    simp [abs_of_pos hD, sin_five_pi_halves]

lemma cpowR_neg_one_neg_three_half :
    cpowR (-1 : ℂ) (-(3 / 2 : ℝ)) = Complex.I := by
  simpa using (cpowR_neg_ofReal_neg_three_half (D := 1) (by norm_num : (0 : ℝ) < 1))

lemma cpowR_neg_one_neg_five_half :
    cpowR (-1 : ℂ) (-(5 / 2 : ℝ)) = -Complex.I := by
  simpa using (cpowR_neg_ofReal_neg_five_half (D := 1) (by norm_num : (0 : ℝ) < 1))

lemma cpowR_one (a : ℝ) : cpowR (1 : ℂ) a = 1 := by
  unfold cpowR
  simp

/--
Principal complex powers are continuous at `-1` from the upper half-plane.
This is the branch used by the `b < a` Poisson terms: the imaginary part of
`q` is positive, so the argument tends to `π`, not to `-π`.
-/
lemma tendsto_cpowR_neg_one_upper (a : ℝ) :
    Tendsto (fun z : ℂ => cpowR z a) (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ))
      (𝓝 (cpowR (-1 : ℂ) a)) := by
  unfold cpowR
  have harg : Tendsto Complex.arg (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) (𝓝 Real.pi) := by
    exact Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (by norm_num) (by simp)
  have hnorm : Tendsto (fun z : ℂ => ‖z‖ ^ a) (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ))
      (𝓝 (‖(-1 : ℂ)‖ ^ a)) := by
    exact (continuous_norm.continuousWithinAt.rpow_const (Or.inl (by norm_num))).tendsto
  have hcos : Tendsto (fun z : ℂ => Real.cos (Complex.arg z * a))
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) (𝓝 (Real.cos (Real.pi * a))) := by
    exact Real.continuous_cos.tendsto _ |>.comp (harg.mul tendsto_const_nhds)
  have hsin : Tendsto (fun z : ℂ => Real.sin (Complex.arg z * a))
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) (𝓝 (Real.sin (Real.pi * a))) := by
    exact Real.continuous_sin.tendsto _ |>.comp (harg.mul tendsto_const_nhds)
  have hmain : Tendsto
      (fun z : ℂ => (↑(‖z‖ ^ a) : ℂ) *
        (Real.cos (Complex.arg z * a) + Real.sin (Complex.arg z * a) * Complex.I))
      (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ))
      (𝓝 ((↑(‖(-1 : ℂ)‖ ^ a) : ℂ) *
        (Real.cos (Real.pi * a) + Real.sin (Real.pi * a) * Complex.I))) := by
    exact (Complex.continuous_ofReal.tendsto _ |>.comp hnorm).mul
      ((Complex.continuous_ofReal.tendsto _ |>.comp hcos).add
        ((Complex.continuous_ofReal.tendsto _ |>.comp hsin).mul tendsto_const_nhds))
  convert hmain using 1
  · ext z
    rw [Complex.cpow_ofReal]
  · rw [Complex.cpow_ofReal]
    simp

lemma exists_cpowR_neg_one_upper_close (a ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, 0 ≤ z.im → dist z (-1 : ℂ) < δ →
      dist (cpowR z a) (cpowR (-1 : ℂ) a) < ε := by
  have ht := tendsto_cpowR_neg_one_upper a
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ),
      dist (cpowR z a) (cpowR (-1 : ℂ) a) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  rw [eventually_nhdsWithin_iff] at hev
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro z hzim hdist
  exact hδ hdist hzim

lemma exists_cpowR_left_branch_near :
    ∃ ε > 0, ∀ z : ℂ, 0 ≤ z.im → dist z (-1 : ℂ) < ε →
      ‖cpowR z (-(3 / 2 : ℝ)) - Complex.I‖ < 1 / 100 ∧
        ‖cpowR z (-(5 / 2 : ℝ)) + Complex.I‖ < 1 / 100 := by
  rcases exists_cpowR_neg_one_upper_close (-(3 / 2 : ℝ)) (1 / 100) (by norm_num) with
    ⟨ε3, hε3, h3⟩
  rcases exists_cpowR_neg_one_upper_close (-(5 / 2 : ℝ)) (1 / 100) (by norm_num) with
    ⟨ε5, hε5, h5⟩
  refine ⟨min ε3 ε5, lt_min hε3 hε5, ?_⟩
  intro z hzim hz
  have hz3 : dist z (-1 : ℂ) < ε3 := hz.trans_le (min_le_left _ _)
  have hz5 : dist z (-1 : ℂ) < ε5 := hz.trans_le (min_le_right _ _)
  constructor
  · have h := h3 z hzim hz3
    simpa [dist_eq_norm, cpowR_neg_one_neg_three_half] using h
  · have h := h5 z hzim hz5
    simpa [dist_eq_norm, cpowR_neg_one_neg_five_half, sub_eq_add_neg, add_comm] using h

lemma exists_cpowR_ceilLeftBase_close :
    ∃ A > 0, ∀ s t : ℝ, 0 < s → s ≤ 1 → 0 ≤ t →
      AwayFromIntegers (A * s) t →
        ‖cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ)) - Complex.I‖ < 1 / 100 ∧
          ‖cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ)) + Complex.I‖ < 1 / 100 := by
  rcases exists_cpowR_left_branch_near with ⟨ε, hεpos, hbranch⟩
  let A : ℝ := 3 / (Real.pi * ε) + 1
  have hApos : 0 < A := by positivity
  have hsmall : 3 / (2 * Real.pi * A) < ε := by
    have htwopipos : 0 < 2 * Real.pi := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have hA_gt : 3 / (Real.pi * ε) < A := by
      dsimp [A]
      linarith
    have hbase_eq : 6 / ε = 2 * Real.pi * (3 / (Real.pi * ε)) := by
      field_simp [hpi.ne', hεpos.ne']
      ring
    have hden_gt : 6 / ε < 2 * Real.pi * A := by
      rw [hbase_eq]
      exact mul_lt_mul_of_pos_left hA_gt htwopipos
    have hbase_pos : 0 < 6 / ε := by positivity
    have hlt : 3 / (2 * Real.pi * A) < 3 / (6 / ε) := by
      exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 3) hbase_pos hden_gt
    calc
      3 / (2 * Real.pi * A) < 3 / (6 / ε) := hlt
      _ = ε / 2 := by
        field_simp [hεpos.ne']
        norm_num
      _ < ε := by linarith
  refine ⟨A, hApos, ?_⟩
  intro s t hspos hsle ht haway
  have him := ceilLeftBase_im_nonneg hApos hspos ht haway
  have hdist : dist (ceilLeftBase s t) (-1 : ℂ) < ε :=
    (ceilLeftBase_dist_le hApos hspos hsle ht haway).trans_lt hsmall
  exact hbranch (ceilLeftBase s t) him hdist

lemma exists_A_ge_two_cpowR_ceilLeftBase_close :
    ∃ A > 0, 2 ≤ A ∧ ∀ s t : ℝ, 0 < s → s ≤ 1 → 0 ≤ t →
      AwayFromIntegers (A * s) t →
        ‖cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ)) - Complex.I‖ < 1 / 100 ∧
          ‖cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ)) + Complex.I‖ < 1 / 100 := by
  rcases exists_cpowR_ceilLeftBase_close with ⟨A0, hA0pos, hclose0⟩
  let A : ℝ := max 2 A0
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hAge : 2 ≤ A := le_max_left _ _
  have hA0le : A0 ≤ A := le_max_right _ _
  refine ⟨A, hApos, hAge, ?_⟩
  intro s t hspos hsle ht haway
  have hsnonneg : 0 ≤ s := hspos.le
  have haway0 : AwayFromIntegers (A0 * s) t := by
    exact away_mono (mul_le_mul_of_nonneg_right hA0le hsnonneg) haway
  exact hclose0 s t hspos hsle ht haway0

lemma exists_L_leftBase_close :
    ∃ L > 0, 8 ≤ L ∧ ∀ s t : ℝ, ∀ m : ℕ, 0 < s → s ≤ 1 → 1 ≤ m → 0 ≤ t →
      bOfT t < aNat m → L * s ≤ |aNat m - bOfT t| →
        ‖cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I‖ < 1 / 100 ∧
          ‖cpowR (leftBase s t m) (-(5 / 2 : ℝ)) + Complex.I‖ < 1 / 100 := by
  rcases exists_cpowR_left_branch_near with ⟨ε, hεpos, hbranch⟩
  let L : ℝ := max 8 (3 / ε + 1)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (le_max_left _ _)
  have hLge8 : 8 ≤ L := le_max_left _ _
  have hsmall : 3 / L < ε := by
    have hLgt : 3 / ε < L := by
      have hlt : 3 / ε < 3 / ε + 1 := by linarith
      exact hlt.trans_le (le_max_right _ _)
    have hbase_pos : 0 < 3 / ε := by positivity
    have hlt : 3 / L < 3 / (3 / ε) := by
      exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 3) hbase_pos hLgt
    calc
      3 / L < 3 / (3 / ε) := hlt
      _ = ε := by field_simp [hεpos.ne']
  refine ⟨L, hLpos, hLge8, ?_⟩
  intro s t m hspos hsle hm ht hleft hsep
  have hb : 0 ≤ bOfT t := bOfT_nonneg ht
  have hDpos : 0 < leftGap t m := leftGap_pos hleft hb
  have ha : 2 * Real.pi ≤ aNat m := by
    unfold aNat
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have him := leftBase_im_nonneg hspos hDpos ((by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha)
  have hdist : dist (leftBase s t m) (-1 : ℂ) < ε :=
    (leftBase_dist_le hspos hsle hLpos ha hb hDpos hsep).trans_lt hsmall
  exact hbranch (leftBase s t m) him hdist

lemma tendsto_cpowR_one (a : ℝ) :
    Tendsto (fun z : ℂ => cpowR z a) (𝓝 (1 : ℂ)) (𝓝 (cpowR (1 : ℂ) a)) := by
  unfold cpowR
  exact (continuousAt_id.cpow continuousAt_const (by
    rw [Complex.mem_slitPlane_iff_not_le_zero, RCLike.le_iff_re_im]
    norm_num)).tendsto

lemma exists_cpowR_one_close (a ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, dist z (1 : ℂ) < δ →
      dist (cpowR z a) (cpowR (1 : ℂ) a) < ε := by
  have ht := tendsto_cpowR_one a
  have hev : ∀ᶠ z in 𝓝 (1 : ℂ),
      dist (cpowR z a) (cpowR (1 : ℂ) a) < ε :=
    ht.eventually (Metric.ball_mem_nhds _ hε)
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδpos, hδ⟩
  exact ⟨δ, hδpos, fun z hz => hδ hz⟩

lemma exists_cpowR_one_linear_close (a η : ℝ) (hη : 0 < η) :
    ∃ ε > 0, ∀ w : ℂ, ‖w‖ < ε →
      ‖cpowR ((1 : ℂ) + w) a - ((1 : ℂ) + (a : ℂ) * w)‖ ≤ η * ‖w‖ := by
  let f : ℂ → ℂ := fun z => cpowR z a
  have hderiv : HasDerivAt f (a : ℂ) (1 : ℂ) := by
    dsimp [f, cpowR]
    have h := (Complex.hasStrictDerivAt_cpow_const (x := (1 : ℂ)) (c := (a : ℂ))
      Complex.one_mem_slitPlane).hasDerivAt
    simpa [Complex.one_cpow] using h
  have ht := hderiv.tendsto_slope_zero
  have hev : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ),
      ‖w⁻¹ • (f ((1 : ℂ) + w) - f (1 : ℂ)) - (a : ℂ)‖ < η := by
    exact ht.eventually (Metric.ball_mem_nhds _ hη)
  rw [eventually_nhdsWithin_iff] at hev
  rcases Metric.eventually_nhds_iff.mp hev with ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_⟩
  intro w hwε
  by_cases hw : w = 0
  · subst w
    simp [cpowR_one]
  · have hslope : ‖w⁻¹ • (f ((1 : ℂ) + w) - f (1 : ℂ)) - (a : ℂ)‖ < η := by
      exact hε (by simpa [dist_eq_norm] using hwε) hw
    have halg : f ((1 : ℂ) + w) - ((1 : ℂ) + (a : ℂ) * w) =
        w * (w⁻¹ • (f ((1 : ℂ) + w) - f (1 : ℂ)) - (a : ℂ)) := by
      rw [show f (1 : ℂ) = (1 : ℂ) by simp [f, cpowR_one]]
      simp [smul_eq_mul]
      field_simp [hw]
      ring
    rw [halg, norm_mul]
    have hmul := mul_lt_mul_of_pos_left hslope (norm_pos_iff.mpr hw)
    simpa [mul_comm] using le_of_lt hmul

lemma exists_cpowR_right_branch_near :
    ∃ ε > 0, ∀ z : ℂ, dist z (1 : ℂ) < ε →
      ‖cpowR z (-(3 / 2 : ℝ)) - 1‖ < 1 / 100 ∧
        ‖cpowR z (-(5 / 2 : ℝ)) - 1‖ < 1 / 100 := by
  rcases exists_cpowR_one_close (-(3 / 2 : ℝ)) (1 / 100) (by norm_num) with
    ⟨ε3, hε3, h3⟩
  rcases exists_cpowR_one_close (-(5 / 2 : ℝ)) (1 / 100) (by norm_num) with
    ⟨ε5, hε5, h5⟩
  refine ⟨min ε3 ε5, lt_min hε3 hε5, ?_⟩
  intro z hz
  have hz3 : dist z (1 : ℂ) < ε3 := hz.trans_le (min_le_left _ _)
  have hz5 : dist z (1 : ℂ) < ε5 := hz.trans_le (min_le_right _ _)
  constructor
  · have h := h3 z hz3
    simpa [dist_eq_norm, cpowR_one] using h
  · have h := h5 z hz5
    simpa [dist_eq_norm, cpowR_one] using h

lemma exists_L_rightBase_close :
    ∃ L > 0, 8 ≤ L ∧ ∀ s t : ℝ, ∀ m : ℕ, 0 < s → s ≤ 1 → 1 ≤ m → 0 ≤ t →
      aNat m < bOfT t → L * s ≤ |aNat m - bOfT t| →
        ‖cpowR (rightBase s t m) (-(3 / 2 : ℝ)) -
            ((1 : ℂ) - (3 / 2 : ℂ) * zeta s (aNat m) / (rightGap t m : ℂ))‖ ≤
            (1 / 100 : ℝ) * ‖rightBase s t m - 1‖ ∧
          ‖cpowR (rightBase s t m) (-(5 / 2 : ℝ)) - 1‖ < 1 / 100 := by
  rcases exists_cpowR_one_linear_close (-(3 / 2 : ℝ)) (1 / 100) (by norm_num) with
    ⟨ε3, hε3, h3⟩
  rcases exists_cpowR_one_close (-(5 / 2 : ℝ)) (1 / 100) (by norm_num) with
    ⟨ε5, hε5, h5⟩
  let ε : ℝ := min ε3 ε5
  have hεpos : 0 < ε := lt_min hε3 hε5
  let L : ℝ := max 8 (3 / ε + 1)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (le_max_left _ _)
  have hLge8 : 8 ≤ L := le_max_left _ _
  have hsmall : 3 / L < ε := by
    have hLgt : 3 / ε < L := by
      have hlt : 3 / ε < 3 / ε + 1 := by linarith
      exact hlt.trans_le (le_max_right _ _)
    have hbase_pos : 0 < 3 / ε := by positivity
    have hlt : 3 / L < 3 / (3 / ε) := by
      exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 3) hbase_pos hLgt
    calc
      3 / L < 3 / (3 / ε) := hlt
      _ = ε := by field_simp [hεpos.ne']
  refine ⟨L, hLpos, hLge8, ?_⟩
  intro s t m hspos hsle hm ht hright hsep
  have hb : 0 ≤ bOfT t := bOfT_nonneg ht
  have ha : 2 * Real.pi ≤ aNat m := by
    unfold aNat
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have ha0 : 0 ≤ aNat m := (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hDpos : 0 < rightGap t m := rightGap_pos hright ha0
  have hdist : dist (rightBase s t m) (1 : ℂ) < ε :=
    (rightBase_dist_le hspos hsle hLpos ha hb hDpos hsep).trans_lt hsmall
  constructor
  · let w : ℂ := rightBase s t m - 1
    have hwε3 : ‖w‖ < ε3 := by
      have hwε : ‖w‖ < ε := by
        simpa [w, dist_eq_norm] using hdist
      exact hwε.trans_le (min_le_left _ _)
    have hlin := h3 w hwε3
    have hw_eq : w = zeta s (aNat m) / (rightGap t m : ℂ) := by
      dsimp [w, rightBase]
      ring
    simpa [rightBase, w, hw_eq, sub_eq_add_neg, div_eq_mul_inv, mul_assoc] using hlin
  · have hdist5 : dist (rightBase s t m) (1 : ℂ) < ε5 :=
      hdist.trans_le (min_le_right _ _)
    have h := h5 (rightBase s t m) hdist5
    simpa [dist_eq_norm, cpowR_one] using h

lemma rpow_neg_three_halves_eq_powNegThreeHalves {D : ℝ} (hD : 0 < D) :
    D ^ (-(3 / 2 : ℝ)) = powNegThreeHalves D := by
  unfold powNegThreeHalves
  rw [Real.rpow_neg hD.le]
  congr 1
  calc
    D ^ (3 / 2 : ℝ) = D ^ ((1 : ℝ) + 1 / 2) := by norm_num
    _ = D ^ (1 : ℝ) * D ^ (1 / 2 : ℝ) := Real.rpow_add hD 1 (1 / 2)
    _ = D * Real.sqrt D := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma rpow_neg_five_halves_eq_powNegFiveHalves {D : ℝ} (hD : 0 < D) :
    D ^ (-(5 / 2 : ℝ)) = powNegFiveHalves D := by
  unfold powNegFiveHalves
  rw [Real.rpow_neg hD.le]
  congr 1
  calc
    D ^ (5 / 2 : ℝ) = D ^ ((2 : ℝ) + 1 / 2) := by norm_num
    _ = D ^ (2 : ℝ) * D ^ (1 / 2 : ℝ) := Real.rpow_add hD 2 (1 / 2)
    _ = D ^ 2 * Real.sqrt D := by rw [Real.rpow_two, ← Real.sqrt_eq_rpow]

lemma ceilLeftGap_rpow_neg_three_halves_eq {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    ceilLeftGap t ^ (-(3 / 2 : ℝ)) = powNegThreeHalves (ceilLeftGap t) := by
  exact rpow_neg_three_halves_eq_powNegThreeHalves
    (ceilLeftGap_pos_of_away hApos hspos ht haway)

lemma ceilLeftGap_rpow_neg_five_halves_eq {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    ceilLeftGap t ^ (-(5 / 2 : ℝ)) = powNegFiveHalves (ceilLeftGap t) := by
  exact rpow_neg_five_halves_eq_powNegFiveHalves
    (ceilLeftGap_pos_of_away hApos hspos ht haway)

lemma leftGap_rpow_neg_three_halves_eq {t : ℝ} {m : ℕ} (hDpos : 0 < leftGap t m) :
    leftGap t m ^ (-(3 / 2 : ℝ)) = powNegThreeHalves (leftGap t m) := by
  exact rpow_neg_three_halves_eq_powNegThreeHalves hDpos

lemma leftGap_rpow_neg_five_halves_eq {t : ℝ} {m : ℕ} (hDpos : 0 < leftGap t m) :
    leftGap t m ^ (-(5 / 2 : ℝ)) = powNegFiveHalves (leftGap t m) := by
  exact rpow_neg_five_halves_eq_powNegFiveHalves hDpos

lemma rightGap_rpow_neg_three_halves_eq {t : ℝ} {m : ℕ} (hDpos : 0 < rightGap t m) :
    rightGap t m ^ (-(3 / 2 : ℝ)) = powNegThreeHalves (rightGap t m) := by
  exact rpow_neg_three_halves_eq_powNegThreeHalves hDpos

lemma rightGap_rpow_neg_five_halves_eq {t : ℝ} {m : ℕ} (hDpos : 0 < rightGap t m) :
    rightGap t m ^ (-(5 / 2 : ℝ)) = powNegFiveHalves (rightGap t m) := by
  exact rpow_neg_five_halves_eq_powNegFiveHalves hDpos

lemma Tterm_ofNat_left_error_decomposition {s t : ℝ} {m : ℕ}
    (hDpos : 0 < leftGap t m) (hbase_ne : leftBase s t m ≠ 0) :
    Tterm s t (m : ℤ) =
      (-aNat m * powNegThreeHalves (leftGap t m) +
          12 * aNat m * s ^ 2 * powNegFiveHalves (leftGap t m)) +
        ((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
            (Complex.ofReal (powNegThreeHalves (leftGap t m)) *
              (cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I)) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal (powNegThreeHalves (leftGap t m)) *
              (cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I)) +
              3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
                (Complex.ofReal (powNegFiveHalves (leftGap t m)) *
                  (cpowR (leftBase s t m) (-(5 / 2 : ℝ)) + Complex.I)))).re := by
  rw [Tterm_ofNat_left_factor_formula hDpos hbase_ne]
  rw [leftGap_rpow_neg_three_halves_eq hDpos]
  rw [leftGap_rpow_neg_five_halves_eq hDpos]
  let e3 := cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I
  let e5 := cpowR (leftBase s t m) (-(5 / 2 : ℝ)) + Complex.I
  have h3 : cpowR (leftBase s t m) (-(3 / 2 : ℝ)) = Complex.I + e3 := by
    dsimp [e3]
    abel
  have h5 : cpowR (leftBase s t m) (-(5 / 2 : ℝ)) = -Complex.I + e5 := by
    dsimp [e5]
    abel
  rw [h3, h5]
  dsimp [e3, e5]
  simp [pow_two]
  ring

lemma Tterm_right_main_algebra (s a d3 d5 : ℝ) :
    ((Complex.ofReal s + Complex.I * Complex.ofReal a) *
          (Complex.ofReal d3 - (3 / 2 : ℂ) * zeta s a * Complex.ofReal d5) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal d3 - (3 / 2 : ℂ) * zeta s a * Complex.ofReal d5) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal a) ^ 2 *
              Complex.ofReal d5)).re =
      -s * d3 - 3 * a ^ 2 * s * d5 + (15 / 2) * s ^ 3 * d5 := by
  unfold zeta
  simp [pow_two]
  ring

lemma Tterm_right_error_decomposition_algebra (s a d3 d5 : ℝ) (e3 e5 : ℂ) :
    ((Complex.ofReal s + Complex.I * Complex.ofReal a) *
          ((Complex.ofReal d3 - (3 / 2 : ℂ) * zeta s a * Complex.ofReal d5) +
            Complex.ofReal d3 * e3) +
        2 * Complex.ofReal s *
          (-((Complex.ofReal d3 - (3 / 2 : ℂ) * zeta s a * Complex.ofReal d5) +
              Complex.ofReal d3 * e3) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal a) ^ 2 *
              (Complex.ofReal d5 * (1 + e5)))).re =
      (-s * d3 - 3 * a ^ 2 * s * d5 + (15 / 2) * s ^ 3 * d5) +
        ((Complex.ofReal s + Complex.I * Complex.ofReal a) * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * (Complex.ofReal s + Complex.I * Complex.ofReal a) ^ 2 *
                (Complex.ofReal d5 * e5))).re := by
  unfold zeta
  simp [pow_two]
  ring

lemma Tterm_ofNat_right_error_decomposition {s t : ℝ} {m : ℕ}
    (hDpos : 0 < rightGap t m) (hbase_ne : rightBase s t m ≠ 0) :
    let a := aNat m
    let D := rightGap t m
    let d3 := powNegThreeHalves D
    let d5 := powNegFiveHalves D
    let L := Complex.ofReal s + Complex.I * Complex.ofReal a
    let e3 := cpowR (rightBase s t m) (-(3 / 2 : ℝ)) -
      ((1 : ℂ) - (3 / 2 : ℂ) * zeta s a / (D : ℂ))
    let e5 := cpowR (rightBase s t m) (-(5 / 2 : ℝ)) - 1
    Tterm s t (m : ℤ) =
      (-s * d3 - 3 * a ^ 2 * s * d5 + (15 / 2) * s ^ 3 * d5) +
        (L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re := by
  intro a D d3 d5 L e3 e5
  rw [Tterm_ofNat_right_factor_formula hDpos hbase_ne]
  rw [rightGap_rpow_neg_three_halves_eq hDpos]
  rw [rightGap_rpow_neg_five_halves_eq hDpos]
  have hDmul : D * d5 = d3 := by
    dsimp [D, d3, d5]
    exact mul_powNegFiveHalves_eq_powNegThreeHalves hDpos
  have hDne : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hDpos.ne'
  have h3 :
      Complex.ofReal d3 * cpowR (rightBase s t m) (-(3 / 2 : ℝ)) =
        (Complex.ofReal d3 - (3 / 2 : ℂ) * zeta s a * Complex.ofReal d5) +
          Complex.ofReal d3 * e3 := by
    have hcp : cpowR (rightBase s t m) (-(3 / 2 : ℝ)) =
        ((1 : ℂ) - (3 / 2 : ℂ) * zeta s a / (D : ℂ)) + e3 := by
      dsimp [e3]
      abel
    have hratio : (d3 : ℂ) / (D : ℂ) = (d5 : ℂ) := by
      rw [div_eq_mul_inv]
      rw [← hDmul]
      rw [Complex.ofReal_mul]
      field_simp [hDne]
    rw [hcp]
    rw [mul_add]
    congr 1
    rw [sub_eq_add_neg]
    ring_nf
    rw [show (↑d3 : ℂ) * zeta s a * (↑D)⁻¹ * (-3 / 2 : ℂ) =
        zeta s a * ((↑d3 : ℂ) * (↑D)⁻¹) * (-3 / 2 : ℂ) by ring]
    rw [show (↑d3 : ℂ) * (↑D)⁻¹ = (↑d5 : ℂ) by
      simpa [div_eq_mul_inv] using hratio]
  have h5 :
      Complex.ofReal d5 * cpowR (rightBase s t m) (-(5 / 2 : ℝ)) =
        Complex.ofReal d5 * (1 + e5) := by
    dsimp [e5]
    ring
  change ((L * (Complex.ofReal d3 * cpowR (rightBase s t m) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal d3 * cpowR (rightBase s t m) (-(3 / 2 : ℝ))) +
            3 * L ^ 2 *
              (Complex.ofReal d5 * cpowR (rightBase s t m) (-(5 / 2 : ℝ))))).re =
      (-s * d3 - 3 * a ^ 2 * s * d5 + (15 / 2) * s ^ 3 * d5) +
        (L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re)
  rw [h3, h5]
  exact Tterm_right_error_decomposition_algebra s a d3 d5 e3 e5

lemma Tterm_left_main_algebra (s a d3 d5 : ℝ) :
    ((Complex.ofReal s + Complex.I * Complex.ofReal a) *
          (Complex.ofReal d3 * Complex.I) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal d3 * Complex.I) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal a) ^ 2 *
              (-Complex.ofReal d5 * Complex.I))).re =
      -a * d3 + 12 * a * s ^ 2 * d5 := by
  simp [pow_two]
  ring

lemma Tterm_left_error_decomposition (s a d3 d5 : ℝ) (e3 e5 : ℂ) :
    ((Complex.ofReal s + Complex.I * Complex.ofReal a) *
          (Complex.ofReal d3 * (Complex.I + e3)) +
        2 * Complex.ofReal s *
          (-(Complex.ofReal d3 * (Complex.I + e3)) +
            3 * (Complex.ofReal s + Complex.I * Complex.ofReal a) ^ 2 *
              (Complex.ofReal d5 * (-Complex.I + e5)))).re =
      (-a * d3 + 12 * a * s ^ 2 * d5) +
        ((Complex.ofReal s + Complex.I * Complex.ofReal a) * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * (Complex.ofReal s + Complex.I * Complex.ofReal a) ^ 2 *
                (Complex.ofReal d5 * e5))).re := by
  simp [pow_two]
  ring

lemma Tterm_left_error_abs_bound {s d3 d5 η3 η5 : ℝ} {L e3 e5 : ℂ}
    (hs : 0 ≤ s) (hd3 : 0 ≤ d3) (hd5 : 0 ≤ d5)
    (he3 : ‖e3‖ ≤ η3) (he5 : ‖e5‖ ≤ η5) :
    |(L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re| ≤
      ‖L‖ * d3 * η3 + 2 * s * (d3 * η3 + 3 * ‖L‖ ^ 2 * d5 * η5) := by
  let X : ℂ := Complex.ofReal d3 * e3
  let Y : ℂ := 3 * L ^ 2 * (Complex.ofReal d5 * e5)
  have hX : ‖X‖ ≤ d3 * η3 := by
    dsimp [X]
    calc
      ‖Complex.ofReal d3 * e3‖ = d3 * ‖e3‖ := by
        rw [norm_mul]
        simp [abs_of_nonneg hd3]
      _ ≤ d3 * η3 := mul_le_mul_of_nonneg_left he3 hd3
  have hY : ‖Y‖ ≤ 3 * ‖L‖ ^ 2 * d5 * η5 := by
    dsimp [Y]
    calc
      ‖(3 : ℂ) * L ^ 2 * (Complex.ofReal d5 * e5)‖ = 3 * ‖L‖ ^ 2 * (d5 * ‖e5‖) := by
        rw [norm_mul, norm_mul, norm_pow, norm_mul]
        simp [abs_of_nonneg hd5]
      _ ≤ 3 * ‖L‖ ^ 2 * (d5 * η5) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he5 hd5)
          (by positivity)
      _ = 3 * ‖L‖ ^ 2 * d5 * η5 := by ring
  have hnegX_Y : ‖-X + Y‖ ≤ d3 * η3 + 3 * ‖L‖ ^ 2 * d5 * η5 := by
    calc
      ‖-X + Y‖ ≤ ‖-X‖ + ‖Y‖ := norm_add_le _ _
      _ = ‖X‖ + ‖Y‖ := by rw [norm_neg]
      _ ≤ d3 * η3 + 3 * ‖L‖ ^ 2 * d5 * η5 := add_le_add hX hY
  have hterm1 : ‖L * X‖ ≤ ‖L‖ * d3 * η3 := by
    calc
      ‖L * X‖ = ‖L‖ * ‖X‖ := norm_mul _ _
      _ ≤ ‖L‖ * (d3 * η3) := mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ = ‖L‖ * d3 * η3 := by ring
  have hterm2 : ‖2 * Complex.ofReal s * (-X + Y)‖ ≤
      2 * s * (d3 * η3 + 3 * ‖L‖ ^ 2 * d5 * η5) := by
    calc
      ‖(2 : ℂ) * Complex.ofReal s * (-X + Y)‖ = 2 * s * ‖-X + Y‖ := by
        rw [norm_mul, norm_mul]
        simp [abs_of_nonneg hs]
      _ ≤ 2 * s * (d3 * η3 + 3 * ‖L‖ ^ 2 * d5 * η5) := by
        exact mul_le_mul_of_nonneg_left hnegX_Y (by positivity)
  calc
    |(L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re| =
        |(L * X + 2 * Complex.ofReal s * (-X + Y)).re| := by rfl
    _ ≤ ‖L * X + 2 * Complex.ofReal s * (-X + Y)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖L * X‖ + ‖2 * Complex.ofReal s * (-X + Y)‖ := norm_add_le _ _
    _ ≤ ‖L‖ * d3 * η3 + 2 * s * (d3 * η3 + 3 * ‖L‖ ^ 2 * d5 * η5) :=
      add_le_add hterm1 hterm2

lemma Tterm_ceil_left_error_decomposition {A s t : ℝ}
    (hApos : 0 < A) (hspos : 0 < s) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t) :
    let a := aNat (Int.ceil t).toNat
    let D := ceilLeftGap t
    let d3 := powNegThreeHalves D
    let d5 := powNegFiveHalves D
    let L := Complex.ofReal s + Complex.I * Complex.ofReal a
    let e3 := cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ)) - Complex.I
    let e5 := cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ)) + Complex.I
    Tterm s t (Int.ceil t) =
      (-a * d3 + 12 * a * s ^ 2 * d5) +
        (L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re := by
  intro a D d3 d5 L e3 e5
  rw [Tterm_ceil_left_factor_formula hApos hspos ht haway]
  rw [ceilLeftGap_rpow_neg_three_halves_eq hApos hspos ht haway]
  rw [ceilLeftGap_rpow_neg_five_halves_eq hApos hspos ht haway]
  change ((L * (Complex.ofReal d3 * cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s * (-(Complex.ofReal d3 * cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ))) +
          3 * L ^ 2 * (Complex.ofReal d5 * cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ))))).re =
      (-a * d3 + 12 * a * s ^ 2 * d5) +
        (L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re)
  have h3 : cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ)) = Complex.I + e3 := by
    dsimp [e3]
    abel
  have h5 : cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ)) = -Complex.I + e5 := by
    dsimp [e5]
    abel
  rw [h3, h5]
  exact Tterm_left_error_decomposition s a d3 d5 e3 e5

lemma Tterm_ceil_left_error_abs_bound {A s t : ℝ} {e3 e5 : ℂ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t)
    (he3 : ‖e3‖ ≤ (1 / 100 : ℝ)) (he5 : ‖e5‖ ≤ (1 / 100 : ℝ)) :
    |((Complex.ofReal s + Complex.I * Complex.ofReal (aNat (Int.ceil t).toNat)) *
        (Complex.ofReal (powNegThreeHalves (ceilLeftGap t)) * e3) +
      2 * Complex.ofReal s *
        (-(Complex.ofReal (powNegThreeHalves (ceilLeftGap t)) * e3) +
          3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat (Int.ceil t).toNat)) ^ 2 *
            (Complex.ofReal (powNegFiveHalves (ceilLeftGap t)) * e5))).re| ≤
      (1 / 10 : ℝ) * aNat (Int.ceil t).toNat * powNegThreeHalves (ceilLeftGap t) := by
  let a := aNat (Int.ceil t).toNat
  let D := ceilLeftGap t
  let d3 := powNegThreeHalves D
  let d5 := powNegFiveHalves D
  let L : ℂ := Complex.ofReal s + Complex.I * Complex.ofReal a
  have hDpos : 0 < D := by simpa [D] using ceilLeftGap_pos_of_away hApos hspos ht haway
  have hd3_nonneg : 0 ≤ d3 := (powNegThreeHalves_pos hDpos).le
  have hd5_nonneg : 0 ≤ d5 := (powNegFiveHalves_pos hDpos).le
  have ha_nonneg : 0 ≤ a := by
    dsimp [a, aNat]
    positivity
  have hLnorm : ‖L‖ ≤ 2 * a := by
    dsimp [L, a]
    exact ceil_lam_complex_norm_le_two_mul hApos hspos hsle ht haway
  have hLnorm_sq : ‖L‖ ^ 2 ≤ (2 * a) ^ 2 := by
    exact sq_le_sq' (by nlinarith [norm_nonneg L, ha_nonneg] : -(2 * a) ≤ ‖L‖) hLnorm
  have hbase := Tterm_left_error_abs_bound (s := s) (d3 := d3) (d5 := d5)
      (η3 := (1 / 100 : ℝ)) (η5 := (1 / 100 : ℝ)) (L := L) (e3 := e3) (e5 := e5)
      hspos.le hd3_nonneg hd5_nonneg he3 he5
  have hs_le_a : s ≤ a := by
    dsimp [a]
    exact hsle.trans (one_le_two_pi.trans (two_pi_le_aNat_ceil_of_away hApos hspos ht haway))
  have hasq_d5 := ceil_left_asq_d5_le_eighth hAge hApos hspos ht haway
  have hterm1 : ‖L‖ * d3 * (1 / 100 : ℝ) ≤ (1 / 50 : ℝ) * a * d3 := by
    have hLd3 : ‖L‖ * d3 ≤ (2 * a) * d3 := mul_le_mul_of_nonneg_right hLnorm hd3_nonneg
    calc
      ‖L‖ * d3 * (1 / 100 : ℝ) ≤ (2 * a) * d3 * (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hLd3 (by norm_num)
      _ = (1 / 50 : ℝ) * a * d3 := by ring
  have hterm2a : 2 * s * (d3 * (1 / 100 : ℝ)) ≤ (1 / 50 : ℝ) * a * d3 := by
    have hsd3 : s * d3 ≤ a * d3 := mul_le_mul_of_nonneg_right hs_le_a hd3_nonneg
    calc
      2 * s * (d3 * (1 / 100 : ℝ)) = (1 / 50 : ℝ) * (s * d3) := by ring
      _ ≤ (1 / 50 : ℝ) * (a * d3) := mul_le_mul_of_nonneg_left hsd3 (by norm_num)
      _ = (1 / 50 : ℝ) * a * d3 := by ring
  have hhalf : s * ‖L‖ ^ 2 * d5 ≤ (1 / 2 : ℝ) * a * d3 := by
    have hnormd5 : ‖L‖ ^ 2 * d5 ≤ (2 * a) ^ 2 * d5 :=
      mul_le_mul_of_nonneg_right hLnorm_sq hd5_nonneg
    have hsnormd5 : s * (‖L‖ ^ 2 * d5) ≤ s * ((2 * a) ^ 2 * d5) :=
      mul_le_mul_of_nonneg_left hnormd5 hspos.le
    nlinarith
  have hterm2b : 2 * s * (3 * ‖L‖ ^ 2 * d5 * (1 / 100 : ℝ)) ≤
      (3 / 100 : ℝ) * a * d3 := by
    calc
      2 * s * (3 * ‖L‖ ^ 2 * d5 * (1 / 100 : ℝ)) =
          (6 / 100 : ℝ) * (s * ‖L‖ ^ 2 * d5) := by ring
      _ ≤ (6 / 100 : ℝ) * ((1 / 2 : ℝ) * a * d3) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = (3 / 100 : ℝ) * a * d3 := by ring
  have hE : ‖L‖ * d3 * (1 / 100 : ℝ) +
        2 * s * (d3 * (1 / 100 : ℝ) + 3 * ‖L‖ ^ 2 * d5 * (1 / 100 : ℝ)) ≤
      (1 / 10 : ℝ) * a * d3 := by
    nlinarith
  dsimp [a, D, d3, d5, L] at hbase hE ⊢
  exact hbase.trans hE

lemma Tterm_ofNat_left_error_abs_bound {s t Lsep : ℝ} {m : ℕ} {e3 e5 : ℂ}
    (hLge8 : 8 ≤ Lsep) (hspos : 0 < s) (hsle : s ≤ 1)
    (ha : 2 * Real.pi ≤ aNat m) (hb : 0 ≤ bOfT t)
    (hDpos : 0 < leftGap t m)
    (hsep : Lsep * s ≤ |aNat m - bOfT t|)
    (he3 : ‖e3‖ ≤ (1 / 100 : ℝ)) (he5 : ‖e5‖ ≤ (1 / 100 : ℝ)) :
    |((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
        (Complex.ofReal (powNegThreeHalves (leftGap t m)) * e3) +
      2 * Complex.ofReal s *
        (-(Complex.ofReal (powNegThreeHalves (leftGap t m)) * e3) +
          3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
            (Complex.ofReal (powNegFiveHalves (leftGap t m)) * e5))).re| ≤
      (1 / 10 : ℝ) * aNat m * powNegThreeHalves (leftGap t m) := by
  let a := aNat m
  let D := leftGap t m
  let d3 := powNegThreeHalves D
  let d5 := powNegFiveHalves D
  let Lc : ℂ := Complex.ofReal s + Complex.I * Complex.ofReal a
  have hDpos' : 0 < D := by simpa [D] using hDpos
  have hd3_nonneg : 0 ≤ d3 := (powNegThreeHalves_pos hDpos').le
  have hd5_nonneg : 0 ≤ d5 := (powNegFiveHalves_pos hDpos').le
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hLnorm : ‖Lc‖ ≤ 2 * a := by
    dsimp [Lc, a]
    exact lam_complex_norm_le_two_mul hsle hspos.le ha
  have hLnorm_sq : ‖Lc‖ ^ 2 ≤ (2 * a) ^ 2 := by
    exact sq_le_sq' (by nlinarith [norm_nonneg Lc, ha_nonneg] : -(2 * a) ≤ ‖Lc‖) hLnorm
  have hbase := Tterm_left_error_abs_bound (s := s) (d3 := d3) (d5 := d5)
      (η3 := (1 / 100 : ℝ)) (η5 := (1 / 100 : ℝ)) (L := Lc) (e3 := e3) (e5 := e5)
      hspos.le hd3_nonneg hd5_nonneg he3 he5
  have hs_le_a : s ≤ a := hsle.trans (one_le_two_pi.trans ha)
  have hasq_d5 := left_asq_d5_le_eighth_of_sep hLge8 hspos ha hb hDpos hsep
  have hterm1 : ‖Lc‖ * d3 * (1 / 100 : ℝ) ≤ (1 / 50 : ℝ) * a * d3 := by
    have hLd3 : ‖Lc‖ * d3 ≤ (2 * a) * d3 := mul_le_mul_of_nonneg_right hLnorm hd3_nonneg
    calc
      ‖Lc‖ * d3 * (1 / 100 : ℝ) ≤ (2 * a) * d3 * (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hLd3 (by norm_num)
      _ = (1 / 50 : ℝ) * a * d3 := by ring
  have hterm2a : 2 * s * (d3 * (1 / 100 : ℝ)) ≤ (1 / 50 : ℝ) * a * d3 := by
    have hsd3 : s * d3 ≤ a * d3 := mul_le_mul_of_nonneg_right hs_le_a hd3_nonneg
    calc
      2 * s * (d3 * (1 / 100 : ℝ)) = (1 / 50 : ℝ) * (s * d3) := by ring
      _ ≤ (1 / 50 : ℝ) * (a * d3) := mul_le_mul_of_nonneg_left hsd3 (by norm_num)
      _ = (1 / 50 : ℝ) * a * d3 := by ring
  have hhalf : s * ‖Lc‖ ^ 2 * d5 ≤ (1 / 2 : ℝ) * a * d3 := by
    have hnormd5 : ‖Lc‖ ^ 2 * d5 ≤ (2 * a) ^ 2 * d5 :=
      mul_le_mul_of_nonneg_right hLnorm_sq hd5_nonneg
    have hsnormd5 : s * (‖Lc‖ ^ 2 * d5) ≤ s * ((2 * a) ^ 2 * d5) :=
      mul_le_mul_of_nonneg_left hnormd5 hspos.le
    nlinarith
  have hterm2b : 2 * s * (3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) ≤
      (3 / 100 : ℝ) * a * d3 := by
    calc
      2 * s * (3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) =
          (6 / 100 : ℝ) * (s * ‖Lc‖ ^ 2 * d5) := by ring
      _ ≤ (6 / 100 : ℝ) * ((1 / 2 : ℝ) * a * d3) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = (3 / 100 : ℝ) * a * d3 := by ring
  have hE : ‖Lc‖ * d3 * (1 / 100 : ℝ) +
        2 * s * (d3 * (1 / 100 : ℝ) + 3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) ≤
      (1 / 10 : ℝ) * a * d3 := by
    nlinarith
  dsimp [a, D, d3, d5, Lc] at hbase hE ⊢
  exact hbase.trans hE

lemma Tterm_ofNat_right_error_abs_bound {s t : ℝ} {m : ℕ} {e3 e5 : ℂ}
    (hspos : 0 < s) (hsle : s ≤ 1)
    (ha : 2 * Real.pi ≤ aNat m)
    (hDpos : 0 < rightGap t m)
    (he3 : ‖e3‖ ≤ (1 / 100 : ℝ) * ‖rightBase s t m - 1‖)
    (he5 : ‖e5‖ ≤ (1 / 100 : ℝ)) :
    |((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
        (Complex.ofReal (powNegThreeHalves (rightGap t m)) * e3) +
      2 * Complex.ofReal s *
        (-(Complex.ofReal (powNegThreeHalves (rightGap t m)) * e3) +
          3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
            (Complex.ofReal (powNegFiveHalves (rightGap t m)) * e5))).re| ≤
      (1 / 2 : ℝ) * (aNat m) ^ 2 * s * powNegFiveHalves (rightGap t m) := by
  let a := aNat m
  let D := rightGap t m
  let d3 := powNegThreeHalves D
  let d5 := powNegFiveHalves D
  let Lc : ℂ := Complex.ofReal s + Complex.I * Complex.ofReal a
  let η3 : ℝ := (1 / 100 : ℝ) * ‖rightBase s t m - 1‖
  have hDpos' : 0 < D := by simpa [D] using hDpos
  have hd3_nonneg : 0 ≤ d3 := (powNegThreeHalves_pos hDpos').le
  have hd5_nonneg : 0 ≤ d5 := (powNegFiveHalves_pos hDpos').le
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hLnorm : ‖Lc‖ ≤ 2 * a := by
    dsimp [Lc, a]
    exact lam_complex_norm_le_two_mul hsle hspos.le ha
  have hLnorm_sq : ‖Lc‖ ^ 2 ≤ (2 * a) ^ 2 := by
    exact sq_le_sq' (by nlinarith [norm_nonneg Lc, ha_nonneg] : -(2 * a) ≤ ‖Lc‖) hLnorm
  have hbase := Tterm_left_error_abs_bound (s := s) (d3 := d3) (d5 := d5)
      (η3 := η3) (η5 := (1 / 100 : ℝ)) (L := Lc) (e3 := e3) (e5 := e5)
      hspos.le hd3_nonneg hd5_nonneg (by simpa [η3] using he3) he5
  have hDmul : D * d5 = d3 := mul_powNegFiveHalves_eq_powNegThreeHalves hDpos'
  have hbase_gap := rightGap_mul_norm_rightBase_sub_one_le hspos hsle ha hDpos
  have hd3w : d3 * ‖rightBase s t m - 1‖ ≤ 3 * a * s * d5 := by
    calc
      d3 * ‖rightBase s t m - 1‖ = (D * d5) * ‖rightBase s t m - 1‖ := by
        rw [hDmul]
      _ = (D * ‖rightBase s t m - 1‖) * d5 := by ring
      _ ≤ (3 * a * s) * d5 := by
        exact mul_le_mul_of_nonneg_right (by simpa [a, D] using hbase_gap) hd5_nonneg
      _ = 3 * a * s * d5 := by ring
  have hs_le_a : s ≤ a := hsle.trans (one_le_two_pi.trans ha)
  have hd3η3 : d3 * η3 ≤ (3 / 100 : ℝ) * a * s * d5 := by
    dsimp [η3]
    calc
      d3 * ((1 / 100 : ℝ) * ‖rightBase s t m - 1‖) =
          (1 / 100 : ℝ) * (d3 * ‖rightBase s t m - 1‖) := by ring
      _ ≤ (1 / 100 : ℝ) * (3 * a * s * d5) :=
        mul_le_mul_of_nonneg_left hd3w (by norm_num)
      _ = (3 / 100 : ℝ) * a * s * d5 := by ring
  have hterm1 : ‖Lc‖ * d3 * η3 ≤ (6 / 100 : ℝ) * a ^ 2 * s * d5 := by
    calc
      ‖Lc‖ * d3 * η3 = ‖Lc‖ * (d3 * η3) := by ring
      _ ≤ (2 * a) * ((3 / 100 : ℝ) * a * s * d5) := by
        exact mul_le_mul hLnorm hd3η3
          (by positivity : 0 ≤ d3 * η3) (by positivity)
      _ = (6 / 100 : ℝ) * a ^ 2 * s * d5 := by ring
  have hterm2a : 2 * s * (d3 * η3) ≤
      (6 / 100 : ℝ) * a ^ 2 * s * d5 := by
    calc
      2 * s * (d3 * η3) ≤ 2 * s * ((3 / 100 : ℝ) * a * s * d5) := by
        exact mul_le_mul_of_nonneg_left hd3η3 (by positivity)
      _ = (6 / 100 : ℝ) * a * s * (s * d5) := by ring
      _ ≤ (6 / 100 : ℝ) * a * s * (a * d5) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hs_le_a hd5_nonneg) (by positivity)
      _ = (6 / 100 : ℝ) * a ^ 2 * s * d5 := by ring
  have hterm2b : 2 * s * (3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) ≤
      (24 / 100 : ℝ) * a ^ 2 * s * d5 := by
    have hnormd5 : ‖Lc‖ ^ 2 * d5 ≤ (2 * a) ^ 2 * d5 :=
      mul_le_mul_of_nonneg_right hLnorm_sq hd5_nonneg
    have hsnormd5 : s * (‖Lc‖ ^ 2 * d5) ≤ s * ((2 * a) ^ 2 * d5) :=
      mul_le_mul_of_nonneg_left hnormd5 hspos.le
    nlinarith
  have hE : ‖Lc‖ * d3 * η3 +
        2 * s * (d3 * η3 + 3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) ≤
      (1 / 2 : ℝ) * a ^ 2 * s * d5 := by
    calc
      ‖Lc‖ * d3 * η3 +
          2 * s * (d3 * η3 + 3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) =
        ‖Lc‖ * d3 * η3 + 2 * s * (d3 * η3) +
          2 * s * (3 * ‖Lc‖ ^ 2 * d5 * (1 / 100 : ℝ)) := by ring
      _ ≤ (6 / 100 : ℝ) * a ^ 2 * s * d5 +
            (6 / 100 : ℝ) * a ^ 2 * s * d5 +
            (24 / 100 : ℝ) * a ^ 2 * s * d5 := by
        exact add_le_add (add_le_add hterm1 hterm2a) hterm2b
      _ ≤ (1 / 2 : ℝ) * a ^ 2 * s * d5 := by
        have hprod_nonneg : 0 ≤ a ^ 2 * s * d5 := by positivity
        calc
          (6 / 100 : ℝ) * a ^ 2 * s * d5 +
                (6 / 100 : ℝ) * a ^ 2 * s * d5 +
                (24 / 100 : ℝ) * a ^ 2 * s * d5 =
              (36 / 100 : ℝ) * (a ^ 2 * s * d5) := by ring
          _ ≤ (1 / 2 : ℝ) * (a ^ 2 * s * d5) :=
            mul_le_mul_of_nonneg_right (by norm_num : (36 / 100 : ℝ) ≤ 1 / 2) hprod_nonneg
          _ = (1 / 2 : ℝ) * a ^ 2 * s * d5 := by ring
  dsimp [a, D, d3, d5, Lc, η3] at hbase hE ⊢
  exact hbase.trans hE

lemma Tterm_ofNat_left_nonpos_of_branch_close {s t Lsep : ℝ} {m : ℕ}
    (hLge8 : 8 ≤ Lsep) (hspos : 0 < s) (hsle : s ≤ 1) (hm : 1 ≤ m) (ht : 0 ≤ t)
    (hleft : bOfT t < aNat m)
    (hsep : Lsep * s ≤ |aNat m - bOfT t|)
    (hclose3 : ‖cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I‖ < 1 / 100)
    (hclose5 : ‖cpowR (leftBase s t m) (-(5 / 2 : ℝ)) + Complex.I‖ < 1 / 100) :
    Tterm s t (m : ℤ) ≤ 0 := by
  have hb : 0 ≤ bOfT t := bOfT_nonneg ht
  have hDpos : 0 < leftGap t m := leftGap_pos hleft hb
  have ha : 2 * Real.pi ≤ aNat m := by
    unfold aNat
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have hapos : 0 ≤ aNat m := (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hbase_ne : leftBase s t m ≠ 0 := leftBase_ne_zero hspos hDpos (lt_of_lt_of_le (by positivity) ha)
  rw [Tterm_ofNat_left_error_decomposition hDpos hbase_ne]
  have hDge := leftGap_ge_twenty_four_sq_of_sep hLge8 hspos hsle ha hb hDpos hsep
  have hcorr := left_positive_correction_le_half (a := aNat m) (s := s) (D := leftGap t m)
    hapos hDpos hDge
  have hmain : -aNat m * powNegThreeHalves (leftGap t m) +
      12 * aNat m * s ^ 2 * powNegFiveHalves (leftGap t m) ≤
      -(1 / 2 : ℝ) * aNat m * powNegThreeHalves (leftGap t m) := by
    linarith
  have herr_abs := Tterm_ofNat_left_error_abs_bound hLge8 hspos hsle ha hb hDpos hsep
    (le_of_lt hclose3) (le_of_lt hclose5)
  have herr : ((Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) *
            (Complex.ofReal (powNegThreeHalves (leftGap t m)) *
              (cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I)) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal (powNegThreeHalves (leftGap t m)) *
              (cpowR (leftBase s t m) (-(3 / 2 : ℝ)) - Complex.I)) +
              3 * (Complex.ofReal s + Complex.I * Complex.ofReal (aNat m)) ^ 2 *
                (Complex.ofReal (powNegFiveHalves (leftGap t m)) *
                  (cpowR (leftBase s t m) (-(5 / 2 : ℝ)) + Complex.I)))).re ≤
      (1 / 10 : ℝ) * aNat m * powNegThreeHalves (leftGap t m) := by
    exact (le_abs_self _).trans herr_abs
  have hd3nonneg : 0 ≤ powNegThreeHalves (leftGap t m) := (powNegThreeHalves_pos hDpos).le
  nlinarith

theorem Tterm_ofNat_left_nonpos :
    ∃ L > 0, 8 ≤ L ∧ ∀ s t : ℝ, ∀ m : ℕ, 0 < s → s ≤ 1 → 1 ≤ m → 0 ≤ t →
      bOfT t < aNat m → L * s ≤ |aNat m - bOfT t| → Tterm s t (m : ℤ) ≤ 0 := by
  rcases exists_L_leftBase_close with ⟨L, hLpos, hLge8, hclose⟩
  refine ⟨L, hLpos, hLge8, ?_⟩
  intro s t m hspos hsle hm ht hleft hsep
  rcases hclose s t m hspos hsle hm ht hleft hsep with ⟨h3, h5⟩
  exact Tterm_ofNat_left_nonpos_of_branch_close hLge8 hspos hsle hm ht hleft hsep h3 h5

lemma Tterm_ofNat_right_nonpos_of_branch_close {s t Lsep : ℝ} {m : ℕ}
    (hLge8 : 8 ≤ Lsep) (hspos : 0 < s) (hsle : s ≤ 1) (hm : 1 ≤ m) (ht : 0 ≤ t)
    (hright : aNat m < bOfT t)
    (hsep : Lsep * s ≤ |aNat m - bOfT t|)
    (hclose3 : ‖cpowR (rightBase s t m) (-(3 / 2 : ℝ)) -
          ((1 : ℂ) - (3 / 2 : ℂ) * zeta s (aNat m) / (rightGap t m : ℂ))‖ ≤
        (1 / 100 : ℝ) * ‖rightBase s t m - 1‖)
    (hclose5 : ‖cpowR (rightBase s t m) (-(5 / 2 : ℝ)) - 1‖ < 1 / 100) :
    Tterm s t (m : ℤ) ≤ 0 := by
  let a := aNat m
  let D := rightGap t m
  let d3 := powNegThreeHalves D
  let d5 := powNegFiveHalves D
  let Lc : ℂ := Complex.ofReal s + Complex.I * Complex.ofReal a
  let e3 := cpowR (rightBase s t m) (-(3 / 2 : ℝ)) -
      ((1 : ℂ) - (3 / 2 : ℂ) * zeta s a / (D : ℂ))
  let e5 := cpowR (rightBase s t m) (-(5 / 2 : ℝ)) - 1
  let err : ℝ := (Lc * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * Lc ^ 2 * (Complex.ofReal d5 * e5))).re
  have hb : 0 ≤ bOfT t := bOfT_nonneg ht
  have ha : 2 * Real.pi ≤ aNat m := by
    unfold aNat
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [Real.pi_pos]
  have ha0 : 0 ≤ aNat m := (by positivity : (0 : ℝ) ≤ 2 * Real.pi).trans ha
  have hDpos : 0 < rightGap t m := rightGap_pos hright ha0
  have hLpos : 0 < Lsep := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hLge8
  have hdist_base : dist (rightBase s t m) (1 : ℂ) < 1 := by
    have hdist_le := rightBase_dist_le hspos hsle hLpos ha hb hDpos hsep
    have hsmall : 3 / Lsep < 1 := by
      rw [div_lt_one hLpos]
      linarith
    exact hdist_le.trans_lt hsmall
  have hbase_ne : rightBase s t m ≠ 0 := rightBase_ne_zero hdist_base
  have hdec := Tterm_ofNat_right_error_decomposition hDpos hbase_ne
  dsimp [a, D, d3, d5, Lc, e3, e5] at hdec
  rw [hdec]
  have hDpos' : 0 < D := by simpa [D] using hDpos
  have hd3_nonneg : 0 ≤ d3 := (powNegThreeHalves_pos hDpos').le
  have hd5_nonneg : 0 ≤ d5 := (powNegFiveHalves_pos hDpos').le
  have hage4 : 4 ≤ a := by
    dsimp [a]
    nlinarith [Real.two_le_pi, ha]
  have ha_sq_ge15 : (15 : ℝ) ≤ a ^ 2 := by nlinarith
  have hs_sq_le_one : s ^ 2 ≤ 1 := by nlinarith [hspos.le, hsle]
  have hcorr : (15 / 2 : ℝ) * s ^ 3 * d5 ≤
      (1 / 2 : ℝ) * a ^ 2 * s * d5 := by
    have hcoef : (15 / 2 : ℝ) * s ^ 2 ≤ (1 / 2 : ℝ) * a ^ 2 := by
      nlinarith
    calc
      (15 / 2 : ℝ) * s ^ 3 * d5 = ((15 / 2 : ℝ) * s ^ 2) * (s * d5) := by ring
      _ ≤ ((1 / 2 : ℝ) * a ^ 2) * (s * d5) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (1 / 2 : ℝ) * a ^ 2 * s * d5 := by ring
  have hmain : -s * d3 - 3 * a ^ 2 * s * d5 + (15 / 2 : ℝ) * s ^ 3 * d5 ≤
      -(5 / 2 : ℝ) * a ^ 2 * s * d5 := by
    nlinarith [hcorr, mul_nonneg hspos.le hd3_nonneg]
  have herr_abs := Tterm_ofNat_right_error_abs_bound hspos hsle ha hDpos
    (by simpa [a, D, e3] using hclose3) (le_of_lt hclose5)
  dsimp [a, D, d3, d5, Lc, e3, e5] at herr_abs
  have herr : err ≤ (1 / 2 : ℝ) * a ^ 2 * s * d5 := by
    dsimp [err, a, D, d3, d5, Lc, e3, e5]
    exact (le_abs_self _).trans herr_abs
  have hsum : -s * d3 - 3 * a ^ 2 * s * d5 + (15 / 2 : ℝ) * s ^ 3 * d5 + err ≤
      -2 * a ^ 2 * s * d5 := by
    nlinarith
  have hnonneg : 0 ≤ a ^ 2 * s * d5 := by positivity
  exact hsum.trans (by nlinarith)

theorem Tterm_ofNat_right_nonpos :
    ∃ L > 0, 8 ≤ L ∧ ∀ s t : ℝ, ∀ m : ℕ, 0 < s → s ≤ 1 → 1 ≤ m → 0 ≤ t →
      aNat m < bOfT t → L * s ≤ |aNat m - bOfT t| → Tterm s t (m : ℤ) ≤ 0 := by
  rcases exists_L_rightBase_close with ⟨L, hLpos, hLge8, hclose⟩
  refine ⟨L, hLpos, hLge8, ?_⟩
  intro s t m hspos hsle hm ht hright hsep
  rcases hclose s t m hspos hsle hm ht hright hsep with ⟨h3, h5⟩
  exact Tterm_ofNat_right_nonpos_of_branch_close hLge8 hspos hsle hm ht hright hsep h3 h5

lemma Tterm_ceil_left_negative_of_branch_close {A s t : ℝ}
    (hAge : 2 ≤ A) (hApos : 0 < A) (hspos : 0 < s) (hsle : s ≤ 1) (ht : 0 ≤ t)
    (haway : AwayFromIntegers (A * s) t)
    (hclose3 : ‖cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ)) - Complex.I‖ < 1 / 100)
    (hclose5 : ‖cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ)) + Complex.I‖ < 1 / 100) :
    Tterm s t (Int.ceil t) ≤ -(1 / 5000 : ℝ) * invSqrtOnePlus t := by
  let a := aNat (Int.ceil t).toNat
  let D := ceilLeftGap t
  let d3 := powNegThreeHalves D
  let d5 := powNegFiveHalves D
  let L : ℂ := Complex.ofReal s + Complex.I * Complex.ofReal a
  let e3 := cpowR (ceilLeftBase s t) (-(3 / 2 : ℝ)) - Complex.I
  let e5 := cpowR (ceilLeftBase s t) (-(5 / 2 : ℝ)) + Complex.I
  let err : ℝ := (L * (Complex.ofReal d3 * e3) +
          2 * Complex.ofReal s *
            (-(Complex.ofReal d3 * e3) +
              3 * L ^ 2 * (Complex.ofReal d5 * e5))).re
  have hdec := Tterm_ceil_left_error_decomposition hApos hspos ht haway
  dsimp [a, D, d3, d5, L, e3, e5] at hdec
  rw [hdec]
  have hmain := ceil_left_main_bound hAge hApos hspos hsle ht haway
  have hmag := ceil_left_main_magnitude_lower hApos hspos ht haway
  have herr_abs := Tterm_ceil_left_error_abs_bound hAge hApos hspos hsle ht haway
    (le_of_lt hclose3) (le_of_lt hclose5)
  dsimp [a, D, d3, d5, L, e3, e5] at herr_abs
  have herr : err ≤ (1 / 10 : ℝ) * a * d3 := by
    dsimp [err, a, D, d3, d5, L, e3, e5]
    exact (le_abs_self _).trans herr_abs
  have hmain_err : -a * d3 + 12 * a * s ^ 2 * d5 + err ≤
      -(2 / 5 : ℝ) * a * d3 := by
    nlinarith
  have hfinal : -(2 / 5 : ℝ) * a * d3 ≤ -(1 / 5000 : ℝ) * invSqrtOnePlus t := by
    nlinarith
  exact hmain_err.trans hfinal

lemma Tterm_neg (s t : ℝ) (m : ℤ) (hs : 0 < s) :
    Tterm s t (-m) = Tterm s t m := by
  by_cases hm : m = 0
  · simp [hm]
  unfold Tterm
  rw [lam_neg, q_neg]
  rw [cpowR_conj (q_arg_ne_pi hs hm)]
  rw [cpowR_conj (q_arg_ne_pi hs hm)]
  let X : ℂ := (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) +
      2 * Complex.ofReal s *
        (-cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)))
  have hleft :
      star (lam s m) * star (cpowR (q s t m) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-star (cpowR (q s t m) (-(3 / 2 : ℝ))) +
            3 * star (lam s m) ^ 2 * star (cpowR (q s t m) (-(5 / 2 : ℝ)))) = star X := by
    dsimp [X]
    simp [Complex.conj_ofNat]
  change (star (lam s m) * star (cpowR (q s t m) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-star (cpowR (q s t m) (-(3 / 2 : ℝ))) +
            3 * star (lam s m) ^ 2 * star (cpowR (q s t m) (-(5 / 2 : ℝ))))).re = X.re
  rw [hleft]
  exact Complex.conj_re X

theorem exists_negative_ceiling_term :
    ∃ A c s0 : ℝ, 0 < A ∧ 0 < c ∧ 0 < s0 ∧
      ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A * s) t →
        ∃ m : ℤ, Tterm s t m ≤ -c * invSqrtOnePlus t := by
  rcases exists_A_ge_two_cpowR_ceilLeftBase_close with ⟨A, hApos, hAge, hclose⟩
  refine ⟨A, 1 / 5000, 1, hApos, by norm_num, by norm_num, ?_⟩
  intro s t hspos hslt ht haway
  have hsle : s ≤ 1 := le_of_lt hslt
  rcases hclose s t hspos hsle ht haway with ⟨h3, h5⟩
  exact ⟨Int.ceil t, Tterm_ceil_left_negative_of_branch_close
    hAge hApos hspos hsle ht haway h3 h5⟩

/-- Exact formula for the zero Poisson-side term before combining powers. -/
lemma Tterm_zero_formula_rpow_unsimplified {s t : ℝ} :
    Tterm s t 0 =
      -s * (s ^ 2 + (2 * Real.pi * t) ^ 2) ^ (-(3 / 2 : ℝ)) +
        6 * s ^ 3 * (s ^ 2 + (2 * Real.pi * t) ^ 2) ^ (-(5 / 2 : ℝ)) := by
  unfold Tterm
  rw [lam_zero, q_zero]
  have hD : 0 ≤ s ^ 2 + (2 * Real.pi * t) ^ 2 := by positivity
  rw [cpowR_ofReal_nonneg (D := s ^ 2 + (2 * Real.pi * t) ^ 2)
    (a := -(3 / 2 : ℝ)) hD]
  rw [cpowR_ofReal_nonneg (D := s ^ 2 + (2 * Real.pi * t) ^ 2)
    (a := -(5 / 2 : ℝ)) hD]
  norm_num [pow_two]
  ring_nf

lemma rpow_neg_three_halves_eq_mul_neg_five_halves {D : ℝ} (hD : 0 < D) :
    D ^ (-(3 / 2 : ℝ)) = D * D ^ (-(5 / 2 : ℝ)) := by
  calc
    D ^ (-(3 / 2 : ℝ)) = D ^ ((1 : ℝ) + (-(5 / 2 : ℝ))) := by norm_num
    _ = D ^ (1 : ℝ) * D ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_add hD 1 (-(5 / 2 : ℝ))
    _ = D * D ^ (-(5 / 2 : ℝ)) := by rw [Real.rpow_one]

/-- The `m = 0` term from Proposition 4 of the note. -/
lemma Tterm_zero_formula_rpow {s t : ℝ} (hs : 0 < s) :
    Tterm s t 0 =
      s * (5 * s ^ 2 - (2 * Real.pi * t) ^ 2) *
        (s ^ 2 + (2 * Real.pi * t) ^ 2) ^ (-(5 / 2 : ℝ)) := by
  let D : ℝ := s ^ 2 + (2 * Real.pi * t) ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_ne_zero hs.ne', sq_nonneg (2 * Real.pi * t)]
  rw [Tterm_zero_formula_rpow_unsimplified]
  change -s * D ^ (-(3 / 2 : ℝ)) + 6 * s ^ 3 * D ^ (-(5 / 2 : ℝ)) =
    s * (5 * s ^ 2 - (2 * Real.pi * t) ^ 2) * D ^ (-(5 / 2 : ℝ))
  rw [rpow_neg_three_halves_eq_mul_neg_five_halves hDpos]
  dsimp [D]
  ring

lemma Tterm_zero_nonpos {L s t : ℝ}
    (hL : Real.sqrt 5 ≤ L) (hs : 0 < s) (ht : 0 ≤ t)
    (hsep0 : L * s ≤ 2 * Real.pi * t) :
    Tterm s t 0 ≤ 0 := by
  rw [Tterm_zero_formula_rpow hs]
  have hs_nonneg : 0 ≤ s := hs.le
  have hsqrt_mul_le : Real.sqrt 5 * s ≤ 2 * Real.pi * t := by
    calc
      Real.sqrt 5 * s ≤ L * s := mul_le_mul_of_nonneg_right hL hs_nonneg
      _ ≤ 2 * Real.pi * t := hsep0
  have hnumer : 5 * s ^ 2 - (2 * Real.pi * t) ^ 2 ≤ 0 := by
    have hleft : -(2 * Real.pi * t) ≤ Real.sqrt 5 * s := by
      have hb_nonneg : 0 ≤ 2 * Real.pi * t := by positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 * s := by positivity
      linarith
    have hsquare := sq_le_sq' hleft hsqrt_mul_le
    have hsqrt_sq : (Real.sqrt 5 * s) ^ 2 = 5 * s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    nlinarith
  have htail : 0 ≤
      (s ^ 2 + (2 * Real.pi * t) ^ 2) ^ (-(5 / 2 : ℝ)) := by
    exact Real.rpow_nonneg (by positivity) _
  have hprod : s * (s ^ 2 + (2 * Real.pi * t) ^ 2) ^ (-(5 / 2 : ℝ)) *
      (5 * s ^ 2 - (2 * Real.pi * t) ^ 2) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs.le htail) hnumer
  nlinarith

lemma Tterm_zero_nonpos_of_scaled_separation {L s t : ℝ}
    (hL : Real.sqrt 5 ≤ L) (hs : 0 < s) (ht : 0 ≤ t)
    (hsep : L * s ≤ |2 * Real.pi * (0 : ℝ) - 2 * Real.pi * t|) :
    Tterm s t 0 ≤ 0 := by
  have htwopi_t_nonneg : 0 ≤ 2 * Real.pi * t := by positivity
  have hsep0 : L * s ≤ 2 * Real.pi * t := by
    simpa [abs_of_nonneg htwopi_t_nonneg] using hsep
  exact Tterm_zero_nonpos hL hs ht hsep0

theorem Tterm_nonpos_away_terms :
    ∃ A s0 : ℝ, 0 < A ∧ 0 < s0 ∧
      ∀ (s t : ℝ) (m : ℤ), 0 < s → s < s0 → 0 ≤ t →
        AwayFromIntegers (A * s) t → Tterm s t m ≤ 0 := by
  rcases Tterm_ofNat_left_nonpos with ⟨Lleft, hLleftpos, hLleftge8, hleft_terms⟩
  rcases Tterm_ofNat_right_nonpos with ⟨Lright, hLrightpos, hLrightge8, hright_terms⟩
  let L0 : ℝ := max (Real.sqrt 5) (max Lleft Lright)
  let A : ℝ := L0 / (2 * Real.pi) + 1
  have htwopipos : 0 < 2 * Real.pi := by positivity
  have hL0_nonneg : 0 ≤ L0 := by
    dsimp [L0]
    exact le_trans (Real.sqrt_nonneg 5) (le_max_left _ _)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hL0_le_twopiA : L0 ≤ 2 * Real.pi * A := by
    calc
      L0 = 2 * Real.pi * (L0 / (2 * Real.pi)) := by
        field_simp [ne_of_gt htwopipos]
      _ ≤ 2 * Real.pi * (L0 / (2 * Real.pi) + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith : L0 / (2 * Real.pi) ≤
          L0 / (2 * Real.pi) + 1) htwopipos.le
      _ = 2 * Real.pi * A := by rfl
  have hsqrt_le_twopiA : Real.sqrt 5 ≤ 2 * Real.pi * A := by
    have hsqrt_le_L0 : Real.sqrt 5 ≤ L0 := by
      dsimp [L0]
      exact le_max_left _ _
    exact hsqrt_le_L0.trans hL0_le_twopiA
  have hLleft_le_twopiA : Lleft ≤ 2 * Real.pi * A := by
    have hleft_le_L0 : Lleft ≤ L0 := by
      dsimp [L0]
      exact (le_max_left _ _ : Lleft ≤ max Lleft Lright).trans (le_max_right _ _)
    exact hleft_le_L0.trans hL0_le_twopiA
  have hLright_le_twopiA : Lright ≤ 2 * Real.pi * A := by
    have hright_le_L0 : Lright ≤ L0 := by
      dsimp [L0]
      exact (le_max_right _ _ : Lright ≤ max Lleft Lright).trans (le_max_right _ _)
    exact hright_le_L0.trans hL0_le_twopiA
  refine ⟨A, 1, hApos, by norm_num, ?_⟩
  intro s t m hspos hslt ht haway
  have hsle : s ≤ 1 := le_of_lt hslt
  have hs_nonneg : 0 ≤ s := hspos.le
  have positive_term_nonpos :
      ∀ n : ℕ, 1 ≤ n → Tterm s t (n : ℤ) ≤ 0 := by
    intro n hn
    have hsep_scaled :
        (2 * Real.pi * A) * s ≤ |aNat n - bOfT t| := by
      have hsep := scaled_integer_separation (n : ℤ) haway
      simpa [aNat, bOfT] using hsep
    by_cases hleft : bOfT t < aNat n
    · have hsep_left : Lleft * s ≤ |aNat n - bOfT t| := by
        exact (mul_le_mul_of_nonneg_right hLleft_le_twopiA hs_nonneg).trans hsep_scaled
      exact hleft_terms s t n hspos hsle hn ht hleft hsep_left
    · have hle_right : aNat n ≤ bOfT t := le_of_not_gt hleft
      by_cases heq : aNat n = bOfT t
      · have hzero : |aNat n - bOfT t| = 0 := by simp [heq]
        have hpos : 0 < (2 * Real.pi * A) * s := by positivity
        have : (2 * Real.pi * A) * s ≤ 0 := by simpa [hzero] using hsep_scaled
        exact (not_lt_of_ge this hpos).elim
      · have hright : aNat n < bOfT t := lt_of_le_of_ne hle_right heq
        have hsep_right : Lright * s ≤ |aNat n - bOfT t| := by
          exact (mul_le_mul_of_nonneg_right hLright_le_twopiA hs_nonneg).trans hsep_scaled
        exact hright_terms s t n hspos hsle hn ht hright hsep_right
  by_cases hm0 : m = 0
  · subst m
    have hsep0 : (2 * Real.pi * A) * s ≤
        |2 * Real.pi * (0 : ℝ) - 2 * Real.pi * t| := by
      simpa using scaled_integer_separation (0 : ℤ) haway
    exact Tterm_zero_nonpos_of_scaled_separation hsqrt_le_twopiA hspos ht hsep0
  by_cases hmpos : 0 < m
  · let n : ℕ := m.toNat
    have hm_nonneg : 0 ≤ m := le_of_lt hmpos
    have hn_cast : ((n : ℕ) : ℤ) = m := by
      dsimp [n]
      exact Int.toNat_of_nonneg hm_nonneg
    have hn_pos_int : (0 : ℤ) < (n : ℕ) := by
      simpa [hn_cast] using hmpos
    have hn : 1 ≤ n := by exact_mod_cast hn_pos_int
    simpa [hn_cast] using positive_term_nonpos n hn
  · have hmneg : m < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hmpos) hm0
    let n : ℕ := (-m).toNat
    have hnegpos : 0 < -m := by linarith
    have hn_cast : ((n : ℕ) : ℤ) = -m := by
      dsimp [n]
      exact Int.toNat_of_nonneg hnegpos.le
    have hn_pos_int : (0 : ℤ) < (n : ℕ) := by
      simpa [hn_cast] using hnegpos
    have hn : 1 ≤ n := by exact_mod_cast hn_pos_int
    have hsym : Tterm s t m = Tterm s t (n : ℤ) := by
      have hm_eq : m = -((n : ℕ) : ℤ) := by
        rw [hn_cast]
        simp
      rw [hm_eq, Tterm_neg s t (n : ℤ) hspos]
    rw [hsym]
    exact positive_term_nonpos n hn

lemma ceil_scaled_separation {A s t : ℝ}
    (haway : AwayFromIntegers (A * s) t) :
    (2 * Real.pi * A) * s ≤
      |2 * Real.pi * (Int.ceil t : ℝ) - 2 * Real.pi * t| := by
  exact scaled_integer_separation (Int.ceil t) haway

lemma tsum_le_term_of_summable_nonpos
    {ι : Type*} [DecidableEq ι] {a : ι → ℝ}
    (ha : Summable a) (hnonpos : ∀ i, a i ≤ 0) (i0 : ι) :
    (∑' i, a i) ≤ a i0 := by
  rw [ha.tsum_eq_add_tsum_ite i0]
  have htail : (∑' i, (if i = i0 then 0 else a i)) ≤ 0 := by
    exact tsum_nonpos (fun i => by by_cases hi : i = i0 <;> simp [hi, hnonpos i])
  linarith

end Erdos953Formalization
