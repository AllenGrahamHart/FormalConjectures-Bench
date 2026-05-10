import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

namespace Erdos699Formalization

/--
The interval form of Sylvester-Schur: every block of `k` consecutive integers
strictly above `k` contains an integer divisible by a prime greater than `k`.
-/
def SylvesterSchurInterval : Prop :=
  ∀ ⦃m k : ℕ⦄, 0 < k → k < m →
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

/--
A sufficient binomial-coefficient inequality for Sylvester-Schur, in the
notation of the interval `[m, m + k)`.  This is Granville's Proposition 5.10.1
criterion with `N = m + k - 1` and `π(k)` represented as
`(k + 1).primesBelow.card`.
-/
def SylvesterSchurChooseInequality : Prop :=
  ∀ ⦃m k : ℕ⦄, 0 < k → k < m →
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k

/--
For each interval length `k`, a threshold `m₀` where Granville's binomial
inequality holds, together with direct interval checks below that threshold.
The monotonicity lemma below propagates the threshold case to all larger
starts, where the binomial criterion supplies the interval witness.
-/
def SylvesterSchurIntervalThreshold : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

/--
The remaining bounded part after the explicit large-start criterion below:
for `k > 1`, it is enough to handle starts up to `k! * 2^(k-1)`.
-/
def SylvesterSchurSmallStart : Prop :=
  ∀ ⦃m k : ℕ⦄, 1 < k → k < m → m ≤ k.factorial * 2 ^ (k - 1) →
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

section RealInequalities

open Real

theorem real_central_gap_five_halves {x : ℝ} (hx_large : (4410 : ℝ) ≤ x) :
    x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) *
        4 ^ (((5 : ℝ) / 2 * x) / 3) < 4 ^ x := by
  let f : ℝ → ℝ :=
    fun x => log x + √(((5 : ℝ) / 2 * x)) * log (((5 : ℝ) / 2 * x)) -
      log 4 / 6 * x
  have hf_pos :
      ∀ x, 0 < x →
        0 < x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) / 4 ^ (x / 6) := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    exact div_pos (mul_pos hx (rpow_pos_of_pos hbase _)) (rpow_pos_of_pos four_pos _)
  have hf :
      ∀ x, 0 < x →
        f x =
          log (x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) / 4 ^ (x / 6)) := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    have hrpow : 0 < ((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x)) :=
      rpow_pos_of_pos hbase _
    rw [log_div (mul_pos hx hrpow).ne' (rpow_pos_of_pos four_pos _).ne',
      log_mul hx.ne' hrpow.ne', log_rpow hbase, log_rpow zero_lt_four]
    ring
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_large
  rw [← div_lt_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div,
    ← rpow_sub four_pos, show x - (5 / 2 * x) / 3 = x / 6 by ring,
    ← log_neg_iff (hf_pos x hx_pos), ← hf x hx_pos]
  · have hconcave : ConcaveOn ℝ (Set.Ioi 0.5) f := by
      apply ConcaveOn.sub
      · apply ConcaveOn.add
        · exact strictConcaveOn_log_Ioi.concaveOn.subset
            (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
        exact ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
          (((5 : ℝ) / 2) • LinearMap.id)).subset
            (fun y hy => by
              rw [Set.mem_Ioi] at hy
              simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
                LinearMap.id_coe, id_eq, smul_eq_mul]
              nlinarith [hy])
            (convex_Ioi 0.5))
      apply ConvexOn.smul
      · refine div_nonneg (log_nonneg (by norm_num)) (by norm_num)
      · exact convexOn_id (convex_Ioi (0.5 : ℝ))
    have hleft : 0.5 < (3240 : ℝ) := by norm_num
    have hx_mem : x ∈ Set.Ioi (0.5 : ℝ) := by exact lt_of_lt_of_le (by norm_num) hx_large
    have hleft_lt_right : (3240 : ℝ) < 4410 := by norm_num
    have hright_le_x : (4410 : ℝ) ≤ x := hx_large
    have hfleft : 0 ≤ f 3240 := by
      have hsqrt : √(((5 : ℝ) / 2 * 3240)) = 90 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_nonneg_iff (hf_pos _ (by norm_num)), hsqrt,
        one_le_div (by positivity)]
      rw [show (((5 : ℝ) / 2 * 3240) : ℝ) = 8100 by norm_num,
        show (90 : ℝ) = (90 : ℕ) by norm_num,
        show (3240 / 6 : ℝ) = (540 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      have hpow : (4 : ℝ) ^ (540 : ℕ) < (8100 : ℝ) ^ (90 : ℕ) := by
        calc
          (4 : ℝ) ^ (540 : ℕ) = 2 ^ (1080 : ℕ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
          _ = ((2 : ℝ) ^ (12 : ℕ)) ^ (90 : ℕ) := by
            rw [← pow_mul]
          _ < (8100 : ℝ) ^ (90 : ℕ) :=
            pow_lt_pow_left₀ (by norm_num : (2 : ℝ) ^ (12 : ℕ) < 8100)
              (by positivity)
              (by norm_num : (90 : ℕ) ≠ 0)
      exact hpow.le.trans (by
        have hpos : 0 < (8100 : ℝ) ^ (90 : ℕ) :=
          pow_pos (by norm_num : (0 : ℝ) < 8100) (90 : ℕ)
        nlinarith)
    have hfright : f 4410 < 0 := by
      have hsqrt : √(((5 : ℝ) / 2 * 4410)) = 105 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_neg_iff (hf_pos _ (by norm_num)), hsqrt,
        div_lt_one (by positivity)]
      rw [show (((5 : ℝ) / 2 * 4410) : ℝ) = 11025 by norm_num,
        show (105 : ℝ) = (105 : ℕ) by norm_num,
        show (4410 / 6 : ℝ) = (735 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast]
      have hbase : (11025 : ℝ) ^ (3 : ℕ) < 2 ^ (41 : ℕ) := by norm_num
      have hcoef : (4410 : ℝ) < 2 ^ (13 : ℕ) := by norm_num
      have hpow :
          (11025 : ℝ) ^ (105 : ℕ) < 2 ^ (1435 : ℕ) := by
        calc
          (11025 : ℝ) ^ (105 : ℕ) = ((11025 : ℝ) ^ (3 : ℕ)) ^ (35 : ℕ) := by
            norm_num [pow_mul]
          _ < (2 ^ (41 : ℕ) : ℝ) ^ (35 : ℕ) :=
            pow_lt_pow_left₀ hbase (by positivity) (by norm_num : (35 : ℕ) ≠ 0)
          _ = 2 ^ (1435 : ℕ) := by
            rw [← pow_mul]
      calc
        (4410 : ℝ) * 11025 ^ (105 : ℕ) < 2 ^ (13 : ℕ) * 2 ^ (1435 : ℕ) :=
          mul_lt_mul hcoef hpow.le (pow_pos (by norm_num : (0 : ℝ) < 11025) (105 : ℕ))
            (by positivity)
        _ = 2 ^ (1448 : ℕ) := by
          rw [← pow_add]
        _ < 2 ^ (1470 : ℕ) := pow_lt_pow_right₀ (by norm_num) (by norm_num)
        _ = 4 ^ (735 : ℕ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
    have hright_le_left : f 4410 ≤ f 3240 := le_trans (le_of_lt hfright) hfleft
    exact lt_of_le_of_lt
      (hconcave.right_le_of_le_left'' hleft hx_mem hleft_lt_right hright_le_x
        hright_le_left)
      hfright

theorem real_scaled_power_boundary_five_halves {x : ℝ} (hx_large : (4840 : ℝ) ≤ x) :
    x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) < ((5 : ℝ) / 4) ^ x := by
  let f : ℝ → ℝ :=
    fun x => log x + √(((5 : ℝ) / 2 * x)) * log (((5 : ℝ) / 2 * x)) -
      log ((5 : ℝ) / 4) * x
  have hf_pos :
      ∀ x, 0 < x →
        0 < x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) /
          ((5 : ℝ) / 4) ^ x := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    exact div_pos (mul_pos hx (rpow_pos_of_pos hbase _)) (rpow_pos_of_pos (by norm_num) _)
  have hf :
      ∀ x, 0 < x →
        f x =
          log (x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) /
            ((5 : ℝ) / 4) ^ x) := by
    intro x hx
    have hbase : 0 < (5 : ℝ) / 2 * x := mul_pos (by norm_num) hx
    have hrpow : 0 < ((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x)) :=
      rpow_pos_of_pos hbase _
    rw [log_div (mul_pos hx hrpow).ne' (rpow_pos_of_pos (by norm_num) _).ne',
      log_mul hx.ne' hrpow.ne', log_rpow hbase, log_rpow (by norm_num : (0 : ℝ) < 5 / 4)]
    ring
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_large
  rw [← div_lt_one (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 4) x),
    ← log_neg_iff (hf_pos x hx_pos), ← hf x hx_pos]
  · have hconcave : ConcaveOn ℝ (Set.Ioi 0.5) f := by
      apply ConcaveOn.sub
      · apply ConcaveOn.add
        · exact strictConcaveOn_log_Ioi.concaveOn.subset
            (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
        exact ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
          (((5 : ℝ) / 2) • LinearMap.id)).subset
            (fun y hy => by
              rw [Set.mem_Ioi] at hy
              simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
                LinearMap.id_coe, id_eq, smul_eq_mul]
              nlinarith [hy])
            (convex_Ioi 0.5))
      apply ConvexOn.smul
      · exact (log_nonneg (by norm_num : (1 : ℝ) ≤ 5 / 4))
      · exact convexOn_id (convex_Ioi (0.5 : ℝ))
    have hleft : 0.5 < (4410 : ℝ) := by norm_num
    have hx_mem : x ∈ Set.Ioi (0.5 : ℝ) := by exact lt_of_lt_of_le (by norm_num) hx_large
    have hleft_lt_right : (4410 : ℝ) < 4840 := by norm_num
    have hright_le_x : (4840 : ℝ) ≤ x := hx_large
    have hfleft : 0 ≤ f 4410 := by
      have hsqrt : √(((5 : ℝ) / 2 * 4410)) = 105 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_nonneg_iff (hf_pos _ (by norm_num)), hsqrt,
        one_le_div (by positivity)]
      rw [show (((5 : ℝ) / 2 * 4410) : ℝ) = 11025 by norm_num,
        show (105 : ℝ) = (105 : ℕ) by norm_num,
        show (4410 : ℝ) = (4410 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast, div_pow]
      rw [div_le_iff₀ (by positivity)]
      have hcoef : (5 : ℝ) ^ (5 : ℕ) < 4410 := by norm_num
      have hmid : (5 : ℝ) ^ (607 : ℕ) < 11025 ^ (105 : ℕ) := by
        have h₁ : (5 : ℝ) ^ (133 : ℕ) < 11025 ^ (23 : ℕ) := by norm_num
        have h₂ : (5 : ℝ) ^ (75 : ℕ) < 11025 ^ (13 : ℕ) := by norm_num
        calc
          (5 : ℝ) ^ (607 : ℕ) = ((5 : ℝ) ^ (133 : ℕ)) ^ (4 : ℕ) * 5 ^ (75 : ℕ) := by
            rw [← pow_mul, ← pow_add]
          _ < (11025 ^ (23 : ℕ)) ^ (4 : ℕ) * 11025 ^ (13 : ℕ) :=
            mul_lt_mul
              (pow_lt_pow_left₀ h₁ (by positivity) (by norm_num : (4 : ℕ) ≠ 0))
              h₂.le (by positivity) (by positivity)
          _ = 11025 ^ (105 : ℕ) := by
            rw [← pow_mul, ← pow_add]
      have hfour : (5 : ℝ) ^ (3798 : ℕ) < 4 ^ (4410 : ℕ) := by
        have h₁ : (5 : ℝ) ^ (149 : ℕ) < 4 ^ (173 : ℕ) := by norm_num
        have h₂ : (5 : ℝ) ^ (73 : ℕ) < 4 ^ (85 : ℕ) := by norm_num
        calc
          (5 : ℝ) ^ (3798 : ℕ) = ((5 : ℝ) ^ (149 : ℕ)) ^ (25 : ℕ) * 5 ^ (73 : ℕ) := by
            rw [← pow_mul, ← pow_add]
          _ < (4 ^ (173 : ℕ)) ^ (25 : ℕ) * 4 ^ (85 : ℕ) :=
            mul_lt_mul
              (pow_lt_pow_left₀ h₁ (by positivity) (by norm_num : (25 : ℕ) ≠ 0))
              h₂.le (by positivity) (by positivity)
          _ = 4 ^ (4410 : ℕ) := by
            rw [← pow_mul, ← pow_add]
      have hprod :
          (5 : ℝ) ^ (4410 : ℕ) < 4410 * 11025 ^ (105 : ℕ) * 4 ^ (4410 : ℕ) := by
        calc
          (5 : ℝ) ^ (4410 : ℕ) =
              (5 ^ (5 : ℕ) * 5 ^ (607 : ℕ)) * 5 ^ (3798 : ℕ) := by
            rw [← pow_add, ← pow_add]
          _ < (4410 * 11025 ^ (105 : ℕ)) * 4 ^ (4410 : ℕ) :=
            mul_lt_mul
              (mul_lt_mul hcoef hmid.le (by positivity) (by positivity))
              hfour.le (by positivity) (by positivity)
          _ = 4410 * 11025 ^ (105 : ℕ) * 4 ^ (4410 : ℕ) := by rfl
      exact hprod.le
    have hfright : f 4840 < 0 := by
      have hsqrt : √(((5 : ℝ) / 2 * 4840)) = 110 := by
        rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
        norm_num
      rw [hf _ (by norm_num), log_neg_iff (hf_pos _ (by norm_num)), hsqrt,
        div_lt_one (by positivity)]
      rw [show (((5 : ℝ) / 2 * 4840) : ℝ) = 12100 by norm_num,
        show (110 : ℝ) = (110 : ℕ) by norm_num,
        show (4840 : ℝ) = (4840 : ℕ) by norm_num]
      rw [Real.rpow_natCast, Real.rpow_natCast, div_pow]
      rw [lt_div_iff₀ (by positivity)]
      have hcoef : (4840 : ℝ) < 5 ^ (6 : ℕ) := by norm_num
      have hmid : (12100 : ℝ) ^ (110 : ℕ) < 5 ^ (660 : ℕ) := by
        calc
          (12100 : ℝ) ^ (110 : ℕ) < (5 ^ (6 : ℕ) : ℝ) ^ (110 : ℕ) :=
            pow_lt_pow_left₀ (by norm_num : (12100 : ℝ) < 5 ^ (6 : ℕ))
              (by positivity) (by norm_num : (110 : ℕ) ≠ 0)
          _ = 5 ^ (660 : ℕ) := by
            rw [← pow_mul]
      have hfour : (4 : ℝ) ^ (4840 : ℕ) < 5 ^ (4173 : ℕ) := by
        have h₁ : (4 : ℝ) ^ (29 : ℕ) < 5 ^ (25 : ℕ) := by norm_num
        have h₂ : (4 : ℝ) ^ (26 : ℕ) < 5 ^ (23 : ℕ) := by norm_num
        calc
          (4 : ℝ) ^ (4840 : ℕ) = ((4 : ℝ) ^ (29 : ℕ)) ^ (166 : ℕ) * 4 ^ (26 : ℕ) := by
            rw [← pow_mul, ← pow_add]
          _ < (5 ^ (25 : ℕ)) ^ (166 : ℕ) * 5 ^ (23 : ℕ) :=
            mul_lt_mul
              (pow_lt_pow_left₀ h₁ (by positivity) (by norm_num : (166 : ℕ) ≠ 0))
              h₂.le (by positivity) (by positivity)
          _ = 5 ^ (4173 : ℕ) := by
            rw [← pow_mul, ← pow_add]
      calc
        (4840 : ℝ) * 12100 ^ (110 : ℕ) * 4 ^ (4840 : ℕ)
            < 5 ^ (6 : ℕ) * 5 ^ (660 : ℕ) * 5 ^ (4173 : ℕ) :=
          mul_lt_mul
            (mul_lt_mul hcoef hmid.le (by positivity) (by positivity))
            hfour.le (by positivity) (by positivity)
        _ = 5 ^ (4839 : ℕ) := by
          rw [← pow_add, ← pow_add]
        _ < 5 ^ (4840 : ℕ) := pow_lt_pow_right₀ (by norm_num) (by norm_num)
    have hright_le_left : f 4840 ≤ f 4410 := le_trans (le_of_lt hfright) hfleft
    exact lt_of_le_of_lt
      (hconcave.right_le_of_le_left'' hleft hx_mem hleft_lt_right hright_le_x
        hright_le_left)
      hfright

noncomputable def scaledPowerLog (x y : ℝ) : ℝ :=
  log x + √y * log y - x * log (y / (2 * x))

lemma hasDerivAt_scaledPowerLog {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y => scaledPowerLog x y)
      (((2 + log y) / (2 * √y)) - x / y) y := by
  have hne2x : 2 * x ≠ 0 := by positivity
  have hlog : HasDerivAt (fun t : ℝ => log t) (1 / y) y := by
    simpa [one_div] using hasDerivAt_log hy.ne'
  have hsqrt : HasDerivAt (fun t : ℝ => √t) (1 / (2 * √y)) y :=
    hasDerivAt_sqrt hy.ne'
  have hprod :
      HasDerivAt (fun t : ℝ => √t * log t)
        (√y * (1 / y) + (1 / (2 * √y)) * log y) y :=
    by simpa [mul_comm, add_comm, add_left_comm] using hsqrt.mul hlog
  have hdiv :
      HasDerivAt (fun t : ℝ => t / (2 * x)) (1 / (2 * x)) y := by
    simpa using (hasDerivAt_id y).div_const (2 * x)
  have hlogdiv :
      HasDerivAt (fun t : ℝ => log (t / (2 * x))) (1 / y) y := by
    have hydiv : y / (2 * x) ≠ 0 := by positivity
    have hcomp := (hasDerivAt_log hydiv).comp y hdiv
    convert hcomp using 1
    field_simp [hy.ne', hne2x]
  have hmain :
      HasDerivAt (fun t : ℝ => log x + √t * log t - x * log (t / (2 * x)))
        ((√y * (1 / y) + (1 / (2 * √y)) * log y) - x * (1 / y)) y :=
    by
      have hmain0 := ((hasDerivAt_const y (log x)).add hprod).sub
        ((hasDerivAt_const y x).mul hlogdiv)
      convert hmain0 using 1
      ring
  convert hmain using 1
  · field_simp [sqrt_sq_eq_abs, abs_of_pos (sqrt_pos_of_pos hy)]
    rw [sq_sqrt hy.le]
    ring

lemma deriv_scaledPowerLog_nonpos {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hmain : √y * (2 + log y) ≤ 2 * x) :
    deriv (fun t => scaledPowerLog x t) y ≤ 0 := by
  have hderiv := (hasDerivAt_scaledPowerLog (x := x) (y := y) hx hy).deriv
  rw [hderiv]
  have hsqrt_pos : 0 < √y := sqrt_pos_of_pos hy
  rw [sub_nonpos]
  rw [div_le_div_iff₀ (mul_pos two_pos hsqrt_pos) hy]
  nlinarith [sq_sqrt hy.le]

lemma scaledPowerLog_eq_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    scaledPowerLog x y = log (x * y ^ √y / (y / (2 * x)) ^ x) := by
  unfold scaledPowerLog
  rw [log_div (mul_pos hx (rpow_pos_of_pos hy _)).ne'
      (rpow_pos_of_pos (div_pos hy (mul_pos two_pos hx)) _).ne',
    log_mul hx.ne' (rpow_pos_of_pos hy _).ne',
    log_rpow hy, log_rpow (div_pos hy (mul_pos two_pos hx))]

theorem real_scaled_power_of_deriv_bound {x y : ℝ} (hx_large : (4840 : ℝ) ≤ x)
    (hy_lower : (5 : ℝ) / 2 * x ≤ y)
    (hderiv : ∀ z ∈ Set.Icc (((5 : ℝ) / 2) * x) y, √z * (2 + log z) ≤ 2 * x) :
    x * y ^ √y < (y / (2 * x)) ^ x := by
  let a : ℝ := (5 : ℝ) / 2 * x
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx_large
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 0 < y := lt_of_lt_of_le ha (by simpa [a] using hy_lower)
  have hcont : ContinuousOn (fun t => scaledPowerLog x t) (Set.Icc a y) := by
    unfold scaledPowerLog
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Icc a y) := continuous_id.continuousOn
    have hlogt : ContinuousOn (fun t : ℝ => log t) (Set.Icc a y) :=
      hid.log (fun t ht => by nlinarith [ha, ht.1])
    have hdiv : ContinuousOn (fun t : ℝ => t / (2 * x)) (Set.Icc a y) := by
      exact hid.div continuous_const.continuousOn (fun _ _ => by positivity)
    have hlogdiv : ContinuousOn (fun t : ℝ => log (t / (2 * x))) (Set.Icc a y) :=
      hdiv.log (fun t ht => by
        have htpos : 0 < t := by nlinarith [ha, ht.1]
        exact (div_pos htpos (mul_pos two_pos hx)).ne')
    exact (continuous_const.continuousOn.add (hid.sqrt.mul hlogt)).sub
      (continuous_const.continuousOn.mul hlogdiv)
  have hdiff : DifferentiableOn ℝ (fun t => scaledPowerLog x t) (interior (Set.Icc a y)) := by
    intro z hz
    have hzIcc : z ∈ Set.Icc a y := interior_subset hz
    have hzpos : 0 < z := by nlinarith [ha, hzIcc.1]
    exact (hasDerivAt_scaledPowerLog hx hzpos).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ z ∈ interior (Set.Icc a y), deriv (fun t => scaledPowerLog x t) z ≤ 0 := by
    intro z hz
    have hzIcc : z ∈ Set.Icc a y := interior_subset hz
    have hzpos : 0 < z := by nlinarith [ha, hzIcc.1]
    exact deriv_scaledPowerLog_nonpos hx hzpos (hderiv z hzIcc)
  have hanti : AntitoneOn (fun t => scaledPowerLog x t) (Set.Icc a y) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a y) hcont hdiff hnonpos
  have ha_mem : a ∈ Set.Icc a y := ⟨le_rfl, by simpa [a] using hy_lower⟩
  have hy_mem : y ∈ Set.Icc a y := ⟨by simpa [a] using hy_lower, le_rfl⟩
  have hlog_le : scaledPowerLog x y ≤ scaledPowerLog x a :=
    hanti ha_mem hy_mem (by simpa [a] using hy_lower)
  have hboundary : scaledPowerLog x a < 0 := by
    have hb := real_scaled_power_boundary_five_halves (x := x) hx_large
    have hratio_pos : 0 < x * a ^ √a / (a / (2 * x)) ^ x := by positivity
    rw [scaledPowerLog_eq_log_ratio hx ha, log_neg_iff hratio_pos]
    have ha_eq : a / (2 * x) = (5 : ℝ) / 4 := by
      dsimp [a]
      field_simp [(ne_of_gt hx)]
      ring
    rw [ha_eq, div_lt_one (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 4) x)]
    simpa [a] using hb
  have hlog_neg : scaledPowerLog x y < 0 := lt_of_le_of_lt hlog_le hboundary
  have hratio_pos : 0 < x * y ^ √y / (y / (2 * x)) ^ x := by positivity
  rw [scaledPowerLog_eq_log_ratio hx hy, log_neg_iff hratio_pos] at hlog_neg
  rwa [div_lt_one (rpow_pos_of_pos (div_pos hy (mul_pos two_pos hx)) x)] at hlog_neg

theorem real_deriv_bound_four_thirds {x y : ℝ} (hx_large : (4840 : ℝ) ≤ x)
    (hy_pos : 0 < y) (hy_cube : y ^ (3 : ℕ) ≤ x ^ (4 : ℕ)) :
    √y * (2 + log y) ≤ 2 * x := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hlog : log y ≤ y ^ ((1 : ℝ) / 10) / ((1 : ℝ) / 10) :=
    log_le_rpow_div hy_nonneg (by norm_num)
  have hlog' : log y ≤ 10 * y ^ ((1 : ℝ) / 10) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog
  have hy_sqrt_le : √y ≤ x ^ ((2 : ℝ) / 3) := by
    rw [sqrt_eq_rpow]
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ y ^ (3 : ℕ)) hy_cube
      (by norm_num : 0 ≤ (1 : ℝ) / 6)
    rw [← Real.rpow_natCast y 3, ← Real.rpow_natCast x 4] at h
    rw [← Real.rpow_mul hy_nonneg, ← Real.rpow_mul hx_nonneg] at h
    norm_num at h
    exact h
  have hy_three_fifths_le : y ^ ((3 : ℝ) / 5) ≤ x ^ ((4 : ℝ) / 5) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ y ^ (3 : ℕ)) hy_cube
      (by norm_num : 0 ≤ (1 : ℝ) / 5)
    rw [← Real.rpow_natCast y 3, ← Real.rpow_natCast x 4] at h
    rw [← Real.rpow_mul hy_nonneg, ← Real.rpow_mul hx_nonneg] at h
    norm_num at h
    exact h
  have hmain_terms : 2 * x ^ ((2 : ℝ) / 3) + 10 * x ^ ((4 : ℝ) / 5) ≤ 2 * x := by
    let t : ℝ := x ^ ((1 : ℝ) / 15)
    have ht_lower : (44 : ℝ) / 25 ≤ t := by
      dsimp [t]
      rw [show (1 : ℝ) / 15 = (15 : ℝ)⁻¹ by norm_num]
      rw [Real.le_rpow_inv_iff_of_pos (by norm_num : 0 ≤ (44 : ℝ) / 25) hx_nonneg
        (by norm_num : 0 < (15 : ℝ))]
      norm_num
      nlinarith
    have hx23 : x ^ ((2 : ℝ) / 3) = t ^ (10 : ℕ) := by
      dsimp [t]
      calc
        x ^ ((2 : ℝ) / 3) = x ^ ((1 : ℝ) / 15 * (10 : ℝ)) := by norm_num
        _ = (x ^ ((1 : ℝ) / 15)) ^ (10 : ℝ) := Real.rpow_mul hx_nonneg _ _
        _ = (x ^ ((1 : ℝ) / 15)) ^ (10 : ℕ) := Real.rpow_natCast _ _
    have hx45 : x ^ ((4 : ℝ) / 5) = t ^ (12 : ℕ) := by
      dsimp [t]
      calc
        x ^ ((4 : ℝ) / 5) = x ^ ((1 : ℝ) / 15 * (12 : ℝ)) := by norm_num
        _ = (x ^ ((1 : ℝ) / 15)) ^ (12 : ℝ) := Real.rpow_mul hx_nonneg _ _
        _ = (x ^ ((1 : ℝ) / 15)) ^ (12 : ℕ) := Real.rpow_natCast _ _
    have hx1 : x = t ^ (15 : ℕ) := by
      dsimp [t]
      calc
        x = x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ ((1 : ℝ) / 15 * (15 : ℝ)) := by norm_num
        _ = (x ^ ((1 : ℝ) / 15)) ^ (15 : ℝ) := Real.rpow_mul hx_nonneg _ _
        _ = (x ^ ((1 : ℝ) / 15)) ^ (15 : ℕ) := Real.rpow_natCast _ _
    rw [hx23, hx45, hx1]
    have htpoly : 0 ≤ 2 * t ^ 5 - 10 * t ^ 2 - 2 := by
      have ht2 : ((44 : ℝ) / 25) ^ 2 ≤ t ^ 2 := by
        nlinarith [sq_nonneg (t - (44 : ℝ) / 25)]
      have ht3 : ((44 : ℝ) / 25) ^ 3 ≤ t ^ 3 := by
        nlinarith [sq_nonneg (t - (44 : ℝ) / 25),
          mul_nonneg (sub_nonneg.mpr ht_lower) (sq_nonneg (t + (44 : ℝ) / 25))]
      nlinarith
    have ht10 : 0 ≤ t ^ 10 := by positivity
    nlinarith [mul_nonneg ht10 htpoly]
  calc
    √y * (2 + log y) ≤ √y * (2 + 10 * y ^ ((1 : ℝ) / 10)) := by gcongr
    _ = 2 * √y + 10 * y ^ ((3 : ℝ) / 5) := by
      rw [sqrt_eq_rpow]
      calc
        y ^ ((1 : ℝ) / 2) * (2 + 10 * y ^ ((1 : ℝ) / 10))
            = 2 * y ^ ((1 : ℝ) / 2) +
                10 * (y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 10)) := by ring
        _ = 2 * y ^ ((1 : ℝ) / 2) + 10 * y ^ ((3 : ℝ) / 5) := by
          rw [← Real.rpow_add hy_pos]
          norm_num
    _ ≤ 2 * x ^ ((2 : ℝ) / 3) + 10 * x ^ ((4 : ℝ) / 5) := by gcongr
    _ ≤ 2 * x := hmain_terms

end RealInequalities

lemma sylvester_schur_interval_one {m : ℕ} (hm : 1 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 1) ∧ p.Prime ∧ 1 < p ∧ p ∣ j := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  exact ⟨m, p, by simp, hp, hp.one_lt, hpm⟩

lemma sylvester_schur_interval_boundary {k : ℕ} (hk : 0 < k) :
    ∃ j p : ℕ, j ∈ Set.Ico (k + 1) (k + 1 + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  obtain ⟨p, hp, hkp, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul k hk.ne'
  refine ⟨p, p, ?_, hp, hkp, dvd_rfl⟩
  exact ⟨Nat.succ_le_of_lt hkp, by omega⟩

lemma odd_has_prime_gt_two {j : ℕ} (hj_gt : 1 < j) (hj_odd : Odd j) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ j := by
  obtain ⟨p, hp, hpj⟩ := Nat.exists_prime_and_dvd (by omega : j ≠ 1)
  have hnot_two_dvd : ¬ 2 ∣ j := by
    intro h2
    have hev : Even j := (even_iff_two_dvd).mpr h2
    exact (Nat.not_even_iff_odd.mpr hj_odd) hev
  have hp_gt : 2 < p := by
    by_contra hnot
    have hp_two_le : 2 ≤ p := hp.two_le
    have hp_eq : p = 2 := by omega
    exact hnot_two_dvd (hp_eq ▸ hpj)
  exact ⟨p, hp, hp_gt, hpj⟩

lemma sylvester_schur_interval_two {m : ℕ} (hm : 2 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 2) ∧ p.Prime ∧ 2 < p ∧ p ∣ j := by
  rcases Nat.even_or_odd m with hm_even | hm_odd
  · have hodd : Odd (m + 1) := hm_even.add_one
    obtain ⟨p, hp, hpgt, hpj⟩ := odd_has_prime_gt_two (j := m + 1) (by omega) hodd
    exact ⟨m + 1, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · obtain ⟨p, hp, hpgt, hpj⟩ := odd_has_prime_gt_two (j := m) (by omega) hm_odd
    exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩

lemma odd_not_three_dvd_has_prime_gt_three {j : ℕ} (hj_gt : 1 < j) (hj_odd : Odd j)
    (hj_not_three : ¬ 3 ∣ j) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ j := by
  obtain ⟨p, hp, hpgt2, hpj⟩ := odd_has_prime_gt_two hj_gt hj_odd
  have hpgt3 : 3 < p := by
    by_contra hnot
    have hp_eq3 : p = 3 := by omega
    exact hj_not_three (hp_eq3 ▸ hpj)
  exact ⟨p, hp, hpgt3, hpj⟩

lemma odd_prime_dvd_not_three_has_prime_gt_three {j p : ℕ} (hp : p.Prime) (hpj : p ∣ j)
    (hp_odd : Odd p) (hj_not_three : ¬ 3 ∣ j) : 3 < p := by
  by_contra hnot
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    norm_num [Nat.odd_iff] at hp_odd
  have hp_eq3 : p = 3 := by omega
  exact hj_not_three (hp_eq3 ▸ hpj)

lemma sylvester_schur_interval_three {m : ℕ} (hm : 3 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 3) ∧ p.Prime ∧ 3 < p ∧ p ∣ j := by
  have hr : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : m % 6
  · have hodd : Odd (m + 1) := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m + 1 := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m + 1) (by omega) hodd hnot3
    exact ⟨m + 1, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd m := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m) (by omega) hodd hnot3
    exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hnot3m : ¬ 3 ∣ m := by intro hd; omega
    have hm2 : 2 < m := by omega
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm2 with h4m | hoddprime_m
    · have hnot3m2 : ¬ 3 ∣ m + 2 := by intro hd; omega
      have hm2_gt : 2 < m + 2 := by omega
      rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm2_gt with h4m2 | hoddprime_m2
      · obtain ⟨a, ha⟩ := h4m
        obtain ⟨b, hb⟩ := h4m2
        omega
      · obtain ⟨p, hp, hpj, hpodd⟩ := hoddprime_m2
        have hpgt : 3 < p := odd_prime_dvd_not_three_has_prime_gt_three hp hpj hpodd hnot3m2
        exact ⟨m + 2, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
    · obtain ⟨p, hp, hpj, hpodd⟩ := hoddprime_m
      have hpgt : 3 < p := odd_prime_dvd_not_three_has_prime_gt_three hp hpj hpodd hnot3m
      exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd (m + 2) := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m + 2 := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m + 2) (by omega) hodd hnot3
    exact ⟨m + 2, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd (m + 1) := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m + 1 := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m + 1) (by omega) hodd hnot3
    exact ⟨m + 1, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩
  · have hodd : Odd m := by rw [Nat.odd_iff]; omega
    have hnot3 : ¬ 3 ∣ m := by intro hd; omega
    obtain ⟨p, hp, hpgt, hpj⟩ :=
      odd_not_three_dvd_has_prime_gt_three (j := m) (by omega) hodd hnot3
    exact ⟨m, p, ⟨by omega, by omega⟩, hp, hpgt, hpj⟩

lemma sylvester_schur_interval_four {m : ℕ} (hm : 4 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 4) ∧ p.Prime ∧ 4 < p ∧ p ∣ j := by
  obtain ⟨j, p, hj, hp, hpgt3, hpj⟩ := sylvester_schur_interval_three (m := m) (by omega)
  have hp_ne4 : p ≠ 4 := by
    intro hp4
    subst hp4
    norm_num at hp
  have hpgt4 : 4 < p := by omega
  have hjhi : j < m + 4 := by
    have : j < m + 3 := hj.2
    omega
  exact ⟨j, p, ⟨hj.1, hjhi⟩, hp, hpgt4, hpj⟩

lemma sylvester_schur_interval_le_four {m k : ℕ} (hk : 0 < k) (hk4 : k ≤ 4) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_four {k : ℕ} (hk : 0 < k) (hk4 : k ≤ 4) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · refine ⟨2, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm
  · refine ⟨3, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm
  · refine ⟨7, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm
  · refine ⟨5, by omega, by decide, ?_⟩
    intro m hm hlt
    exact sylvester_schur_interval_le_four (by omega) (by omega) hm

lemma dvd_ascFactorial_of_mem {m k j : ℕ} (hlo : m ≤ j) (hhi : j < m + k) :
    j ∣ m.ascFactorial k := by
  induction k with
  | zero =>
      omega
  | succ k ih =>
      rw [Nat.ascFactorial_succ]
      by_cases hj : j = m + k
      · subst hj
        exact dvd_mul_right _ _
      · have hhi' : j < m + k := by omega
        exact dvd_mul_of_dvd_right (ih hhi') _

lemma prime_not_dvd_factorial_of_lt {p i : ℕ} (hp : p.Prime) (hpi : i < p) :
    ¬ p ∣ i.factorial := by
  rw [hp.dvd_factorial]
  exact not_le_of_gt hpi

lemma exists_mem_Ico_dvd_of_prime_dvd_ascFactorial {m k p : ℕ}
    (hp : p.Prime) (h : p ∣ m.ascFactorial k) :
    ∃ j : ℕ, j ∈ Set.Ico m (m + k) ∧ p ∣ j := by
  induction k with
  | zero =>
      rw [Nat.ascFactorial_zero] at h
      exact (hp.not_dvd_one h).elim
  | succ k ih =>
      rw [Nat.ascFactorial_succ] at h
      rcases hp.dvd_mul.mp h with hp_dvd | hp_dvd
      · exact ⟨m + k, ⟨by omega, by omega⟩, hp_dvd⟩
      · obtain ⟨j, hj, hpj⟩ := ih hp_dvd
        have hhi : j < m + Nat.succ k := by
          have : j < m + k := hj.2
          omega
        exact ⟨j, ⟨hj.1, hhi⟩, hpj⟩

lemma choose_le_pow_primesBelow_card_of_prime_factors_below
    {N k : ℕ} (hkn : k ≤ N) (hN : 0 < N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N k → p < k + 1) :
    Nat.choose N k ≤ N ^ (k + 1).primesBelow.card := by
  classical
  let s := (Finset.range (N + 1)).filter (fun p => p ∈ (k + 1).primesBelow)
  let f := fun p => p ^ (Nat.choose N k).factorization p
  have hs_subset : s ⊆ Finset.range (N + 1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hprod_eq : (∏ p ∈ Finset.range (N + 1), f p) = ∏ p ∈ s, f p := by
    symm
    refine Finset.prod_subset hs_subset ?_
    intro p hp_range hp_not_s
    have hp_not_primesBelow : p ∉ (k + 1).primesBelow := by
      intro hp_mem
      exact hp_not_s (by simp [s, hp_range, hp_mem])
    by_cases hfac : (Nat.choose N k).factorization p = 0
    · simp [f, hfac]
    · have hp_prime : p.Prime := by
        by_contra hp_not_prime
        exact hfac (Nat.factorization_eq_zero_of_not_prime (Nat.choose N k) hp_not_prime)
      have hp_dvd : p ∣ Nat.choose N k := Nat.dvd_of_factorization_pos hfac
      exact (hp_not_primesBelow (Nat.mem_primesBelow.mpr ⟨hsmall p hp_prime hp_dvd, hp_prime⟩)).elim
  have hs_card : s.card ≤ (k + 1).primesBelow.card := by
    refine Finset.card_le_card ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  calc
    Nat.choose N k = ∏ p ∈ Finset.range (N + 1), f p := by
      rw [Nat.prod_pow_factorization_choose N k hkn]
    _ = ∏ p ∈ s, f p := hprod_eq
    _ ≤ ∏ _p ∈ s, N := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      exact Nat.pow_factorization_choose_le hN
    _ = N ^ s.card := by
      rw [Finset.prod_const]
    _ ≤ N ^ (k + 1).primesBelow.card := Nat.pow_le_pow_right hN hs_card

theorem exists_large_prime_factor_of_choose_gt_pow_prime_count_direct
    {N k : ℕ} (hkN : k ≤ N) (hN : 0 < N)
    (hgt : N ^ (k + 1).primesBelow.card < Nat.choose N k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ Nat.choose N k := by
  by_contra hno
  have hsmall :
      ∀ p : ℕ, p.Prime → p ∣ Nat.choose N k → p < k + 1 := by
    intro p hp hp_choose
    by_contra hnot
    have hkp : k < p := by omega
    exact hno ⟨p, hp, hkp, hp_choose⟩
  have hle :
      Nat.choose N k ≤ N ^ (k + 1).primesBelow.card :=
    choose_le_pow_primesBelow_card_of_prime_factors_below hkN hN hsmall
  exact (not_lt_of_ge hle) hgt

theorem exists_large_prime_factor_of_choose_gt_pow_prime_count
    {m k : ℕ} (hk : 0 < k) (hm : k < m)
    (hgt : (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_contra hno
  have hno' :
      ∀ j p : ℕ, j ∈ Set.Ico m (m + k) → p.Prime → k < p → p ∣ j → False := by
    intro j p hj hp hkp hpj
    exact hno ⟨j, p, hj, hp, hkp, hpj⟩
  have hm_pos : 0 < m := by omega
  have hN_pos : 0 < m + k - 1 := by omega
  have hkN : k ≤ m + k - 1 := by omega
  have hasc_choose : m.ascFactorial k = k.factorial * Nat.choose (m + k - 1) k := by
    have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    have hm_add : m - 1 + k = m + k - 1 := by omega
    simpa [hm_sub, hm_add] using Nat.ascFactorial_eq_factorial_mul_choose (m - 1) k
  have hsmall :
      ∀ p : ℕ, p.Prime → p ∣ Nat.choose (m + k - 1) k → p < k + 1 := by
    intro p hp hp_choose
    have hp_asc : p ∣ m.ascFactorial k := by
      rw [hasc_choose]
      exact dvd_mul_of_dvd_right hp_choose k.factorial
    obtain ⟨j, hj, hpj⟩ := exists_mem_Ico_dvd_of_prime_dvd_ascFactorial hp hp_asc
    have hpk : p ≤ k := by
      by_contra hnot
      exact hno' j p hj hp (Nat.lt_of_not_ge hnot) hpj
    exact Nat.lt_succ_iff.mpr hpk
  have hle :
      Nat.choose (m + k - 1) k ≤ (m + k - 1) ^ (k + 1).primesBelow.card :=
    choose_le_pow_primesBelow_card_of_prime_factors_below hkN hN_pos hsmall
  exact (not_lt_of_ge hle) hgt

theorem sylvester_schur_interval_of_choose_inequality
    (hineq : SylvesterSchurChooseInequality) :
    SylvesterSchurInterval := by
  intro m k hk hm
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count hk hm (hineq hk hm)

theorem sylvester_schur_of_choose_inequality
    (hineq : ∀ ⦃n i : ℕ⦄, 1 ≤ i → i ≤ n / 2 →
      n ^ (i + 1).primesBelow.card < Nat.choose n i)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn_pos : 0 < n := by omega
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count_direct hi_le_n hn_pos
    (hineq hi hi_half)

lemma succ_pow_mul_sub_le_pow_mul_succ {N r : ℕ} (hr : r ≤ N + 1) :
    (N + 1) ^ r * (N + 1 - r) ≤ N ^ r * (N + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hr' : r ≤ N + 1 := by omega
      have ih' := ih hr'
      have hsub : N + 1 - (r + 1) = N - r := by omega
      have hsub2 : N + 1 - r = N - r + 1 := by omega
      have hmul_step : (N + 1) * (N - r) ≤ N * (N + 1 - r) := by
        rw [hsub2, Nat.mul_add, Nat.mul_one, Nat.succ_mul]
        exact Nat.add_le_add_left (Nat.sub_le N r) (N * (N - r))
      calc
        (N + 1) ^ (r + 1) * (N + 1 - (r + 1))
            = (N + 1) ^ r * ((N + 1) * (N - r)) := by
              rw [pow_succ, hsub]
              ring
        _ ≤ (N + 1) ^ r * (N * (N + 1 - r)) :=
              Nat.mul_le_mul_left _ hmul_step
        _ = ((N + 1) ^ r * (N + 1 - r)) * N := by ring
        _ ≤ (N ^ r * (N + 1)) * N := Nat.mul_le_mul_right _ ih'
        _ = N ^ (r + 1) * (N + 1) := by
              rw [pow_succ]
              ring

lemma choose_inequality_succ {N k r : ℕ} (hkN : k ≤ N) (hrk : r ≤ k)
    (h : N ^ r < Nat.choose N k) :
    (N + 1) ^ r < Nat.choose (N + 1) k := by
  have hleft_le : (N + 1) ^ r * (N + 1 - k) ≤ N ^ r * (N + 1) := by
    calc
      (N + 1) ^ r * (N + 1 - k)
          ≤ (N + 1) ^ r * (N + 1 - r) :=
            Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hrk (N + 1))
      _ ≤ N ^ r * (N + 1) := succ_pow_mul_sub_le_pow_mul_succ (N := N) (r := r) (by omega)
  have hright_lt : N ^ r * (N + 1) < Nat.choose N k * (N + 1) :=
    Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos N)
  have hprod_lt :
      (N + 1) ^ r * (N + 1 - k) < Nat.choose (N + 1) k * (N + 1 - k) := by
    calc
      (N + 1) ^ r * (N + 1 - k) ≤ N ^ r * (N + 1) := hleft_le
      _ < Nat.choose N k * (N + 1) := hright_lt
      _ = Nat.choose (N + 1) k * (N + 1 - k) := Nat.choose_mul_succ_eq N k
  exact Nat.lt_of_mul_lt_mul_right hprod_lt

lemma pow_le_pow_mul_choose (n k : ℕ) (hk : k ≤ n) :
    n ^ k ≤ k ^ k * Nat.choose n k := by
  refine Nat.le_induction (m := k)
    (P := fun N _ => N ^ k ≤ k ^ k * Nat.choose N k) ?_ ?_ n hk
  · simp
  · intro N hkN ih
    have hsub_pos : 0 < N + 1 - k := by omega
    refine Nat.le_of_mul_le_mul_right ?_ hsub_pos
    calc
      (N + 1) ^ k * (N + 1 - k) ≤ N ^ k * (N + 1) :=
        succ_pow_mul_sub_le_pow_mul_succ (N := N) (r := k) (by omega)
      _ ≤ (k ^ k * Nat.choose N k) * (N + 1) :=
        Nat.mul_le_mul_right _ ih
      _ = k ^ k * (Nat.choose N k * (N + 1)) := by ring
      _ = k ^ k * (Nat.choose (N + 1) k * (N + 1 - k)) := by
        rw [Nat.choose_mul_succ_eq]
      _ = (k ^ k * Nat.choose (N + 1) k) * (N + 1 - k) := by ring

lemma primesBelow_succ_card_le (k : ℕ) : (k + 1).primesBelow.card ≤ k := by
  have hsubset : (k + 1).primesBelow ⊆ Finset.Icc 1 k := by
    intro p hp
    rw [Finset.mem_Icc]
    have hlt : p < k + 1 := Nat.lt_of_mem_primesBelow hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    exact ⟨hprime.one_lt.le, Nat.lt_succ_iff.mp hlt⟩
  have hcard := Finset.card_le_card hsubset
  simpa using hcard

lemma choose_inequality_succ_start {m k : ℕ} (hk : 0 < k) (hm : k < m)
    (h : (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k) :
    (m + 1 + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + 1 + k - 1) k := by
  have hN : k ≤ m + k - 1 := by omega
  have hsucc := choose_inequality_succ (N := m + k - 1) (k := k)
    (r := (k + 1).primesBelow.card) hN (primesBelow_succ_card_le k) h
  have hN' : m + k - 1 + 1 = m + 1 + k - 1 := by omega
  simpa [hN'] using hsucc

lemma choose_inequality_of_ge_start {m₀ m k : ℕ} (hk : 0 < k) (hm₀ : k < m₀)
    (hle : m₀ ≤ m)
    (hbase : (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  exact Nat.le_induction (m := m₀)
    (P := fun n _ =>
      (n + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (n + k - 1) k)
    hbase
    (fun n hn ih => choose_inequality_succ_start hk (by omega) ih)
    m hle

lemma primesBelow_succ_card_le_pred (k : ℕ) : (k + 1).primesBelow.card ≤ k - 1 := by
  by_cases hk : 2 ≤ k
  · have hsubset : (k + 1).primesBelow ⊆ Finset.Icc 2 k := by
      intro p hp
      rw [Finset.mem_Icc]
      have hlt : p < k + 1 := Nat.lt_of_mem_primesBelow hp
      have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
      exact ⟨hprime.two_le, Nat.lt_succ_iff.mp hlt⟩
    have hcard := Finset.card_le_card hsubset
    have hIcc : (Finset.Icc 2 k).card = k - 1 := by
      rw [Nat.card_Icc]
      omega
    simpa [hIcc] using hcard
  · have hk' : k ≤ 1 := by omega
    interval_cases k <;> decide

lemma primesBelow_succ_card_le_half_add_one (k : ℕ) :
    (k + 1).primesBelow.card ≤ k / 2 + 1 := by
  classical
  let odds : Finset ℕ := (Finset.Icc 1 (k / 2)).image fun t => 2 * t + 1
  have hsubset : (k + 1).primesBelow ⊆ insert 2 odds := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp_le_k : p ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)
    by_cases hp_two : p = 2
    · exact Finset.mem_insert.mpr (Or.inl hp_two)
    · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_two
      have hp_two_le : 2 ≤ p := hp_prime.two_le
      have hp_div_mem : p / 2 ∈ Finset.Icc 1 (k / 2) := by
        rw [Finset.mem_Icc]
        exact ⟨Nat.div_pos hp_two_le (by norm_num),
          Nat.div_le_div_right hp_le_k⟩
      have hp_eq : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
      have hp_mem_odds : p ∈ odds := by
        rw [Finset.mem_image]
        exact ⟨p / 2, hp_div_mem, hp_eq⟩
      exact Finset.mem_insert.mpr (Or.inr hp_mem_odds)
  calc
    (k + 1).primesBelow.card ≤ (insert 2 odds).card := Finset.card_le_card hsubset
    _ ≤ odds.card + 1 := Finset.card_insert_le 2 odds
    _ ≤ (Finset.Icc 1 (k / 2)).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = k / 2 + 1 := by
      rw [Nat.card_Icc]
      omega

lemma primesBelow_succ_card_le_half {k : ℕ} (hk : 8 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 2 := by
  classical
  rcases k.even_or_odd with heven | hodd
  · obtain ⟨a, rfl⟩ := heven
    have ha : 4 ≤ a := by omega
    let odds : Finset ℕ := (Finset.Icc 1 (a - 1)).image fun t => 2 * t + 1
    have hsubset : (a + a + 1).primesBelow ⊆ insert 2 odds := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
      have hp_le : p ≤ a + a := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)
      by_cases hp_two : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp_two)
      · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_two
        have hp_two_le : 2 ≤ p := hp_prime.two_le
        have hp_lt : p < a + a := by
          have hp_ne : p ≠ a + a := by
            intro h
            have h_even : Even p := h.symm ▸ (show Even (a + a) from ⟨a, rfl⟩)
            exact (Nat.not_even_iff_odd.mpr hp_odd) h_even
          omega
        have hp_div_mem : p / 2 ∈ Finset.Icc 1 (a - 1) := by
          rw [Finset.mem_Icc]
          constructor
          · exact Nat.div_pos hp_two_le (by norm_num)
          · have hdiv_lt : p / 2 < a := by
              have hp_lt' : p < a * 2 := by omega
              exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mpr hp_lt'
            omega
        have hp_eq : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
        have hp_mem_odds : p ∈ odds := by
          rw [Finset.mem_image]
          exact ⟨p / 2, hp_div_mem, hp_eq⟩
        exact Finset.mem_insert.mpr (Or.inr hp_mem_odds)
    calc
      (a + a + 1).primesBelow.card ≤ (insert 2 odds).card := Finset.card_le_card hsubset
      _ ≤ odds.card + 1 := Finset.card_insert_le 2 odds
      _ ≤ (Finset.Icc 1 (a - 1)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
      _ = a := by
        rw [Nat.card_Icc]
        omega
      _ = (a + a) / 2 := by omega
  · obtain ⟨a, rfl⟩ := hodd
    have ha : 4 ≤ a := by omega
    let odds : Finset ℕ := (Finset.Icc 1 a).image fun t => 2 * t + 1
    have h9_mem : 9 ∈ odds := by
      rw [Finset.mem_image]
      refine ⟨4, ?_, by norm_num⟩
      rw [Finset.mem_Icc]
      omega
    have hsubset : (2 * a + 1 + 1).primesBelow ⊆ insert 2 (odds.erase 9) := by
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp
      have hp_le : p ≤ 2 * a + 1 := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)
      by_cases hp_two : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp_two)
      · have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_two
        have hp_two_le : 2 ≤ p := hp_prime.two_le
        have hp_div_mem : p / 2 ∈ Finset.Icc 1 a := by
          rw [Finset.mem_Icc]
          constructor
          · exact Nat.div_pos hp_two_le (by norm_num)
          · have hdiv_le : p / 2 ≤ (2 * a + 1) / 2 := Nat.div_le_div_right hp_le
            omega
        have hp_eq : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
        have hp_mem_odds : p ∈ odds := by
          rw [Finset.mem_image]
          exact ⟨p / 2, hp_div_mem, hp_eq⟩
        have hp_ne9 : p ≠ 9 := by
          intro h
          subst h
          norm_num at hp_prime
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hp_ne9, hp_mem_odds⟩))
    calc
      (2 * a + 1 + 1).primesBelow.card ≤ (insert 2 (odds.erase 9)).card :=
        Finset.card_le_card hsubset
      _ ≤ (odds.erase 9).card + 1 := Finset.card_insert_le 2 (odds.erase 9)
      _ = odds.card - 1 + 1 := by rw [Finset.card_erase_of_mem h9_mem]
      _ ≤ (Finset.Icc 1 a).card - 1 + 1 := by
        exact Nat.add_le_add_right (Nat.sub_le_sub_right Finset.card_image_le 1) 1
      _ = a := by
        rw [Nat.card_Icc]
        omega
      _ = (2 * a + 1) / 2 := by omega

lemma primesBelow_succ_card_le_third {k : ℕ} (hk : 49 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 3 := by
  classical
  let ones : Finset ℕ := (Finset.Icc 0 (k / 6)).image fun t => 6 * t + 1
  let fives : Finset ℕ := (Finset.Icc 0 (k / 6)).image fun t => 6 * t + 5
  let base : Finset ℕ := insert 2 (insert 3 (ones ∪ fives))
  let trimmed : Finset ℕ := (((base.erase 1).erase 25).erase 35).erase 49
  have h1_base : 1 ∈ base := by
    dsimp [base, ones]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl ?_
    rw [Finset.mem_image]
    refine ⟨0, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have h25_base : 25 ∈ base := by
    have h4 : 4 ≤ k / 6 := by omega
    dsimp [base, ones]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl ?_
    rw [Finset.mem_image]
    refine ⟨4, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have h35_base : 35 ∈ base := by
    have h5 : 5 ≤ k / 6 := by omega
    dsimp [base, fives]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inr ?_
    rw [Finset.mem_image]
    refine ⟨5, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have h49_base : 49 ∈ base := by
    have h8 : 8 ≤ k / 6 := by omega
    dsimp [base, ones]
    refine Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_union.mpr <| Or.inl ?_
    rw [Finset.mem_image]
    refine ⟨8, ?_, by norm_num⟩
    rw [Finset.mem_Icc]
    omega
  have hsubset : (k + 1).primesBelow ⊆ trimmed := by
    intro p hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp_mem
    have hp_le_k : p ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp_mem)
    have hp_base : p ∈ base := by
      by_cases hp_two : p = 2
      · exact Finset.mem_insert.mpr (Or.inl hp_two)
      by_cases hp_three : p = 3
      · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr (Or.inl hp_three)
      have hmod_lt : p % 6 < 6 := Nat.mod_lt p (by norm_num)
      interval_cases hmod : p % 6
      · have hmod2 : p % 2 = 0 := by omega
        have h2dvd : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod2
        have hp_eq_two : p = 2 :=
          (hp_prime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd
        exact (hp_two hp_eq_two).elim
      · have hp_eq : 6 * (p / 6) + 1 = p := by
          have hdivmod := Nat.div_add_mod p 6
          omega
        have hp_div_mem : p / 6 ∈ Finset.Icc 0 (k / 6) := by
          rw [Finset.mem_Icc]
          exact ⟨Nat.zero_le _, Nat.div_le_div_right hp_le_k⟩
        have hp_ones : p ∈ ones := by
          rw [Finset.mem_image]
          exact ⟨p / 6, hp_div_mem, hp_eq⟩
        exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl hp_ones
      · have hmod2 : p % 2 = 0 := by omega
        have h2dvd : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod2
        have hp_eq_two : p = 2 :=
          (hp_prime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd
        exact (hp_two hp_eq_two).elim
      · have hmod3 : p % 3 = 0 := by omega
        have h3dvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod3
        have hp_eq_three : p = 3 :=
          (hp_prime.dvd_iff_eq (by norm_num : 3 ≠ 1)).mp h3dvd
        exact (hp_three hp_eq_three).elim
      · have hmod2 : p % 2 = 0 := by omega
        have h2dvd : 2 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod2
        have hp_eq_two : p = 2 :=
          (hp_prime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp h2dvd
        exact (hp_two hp_eq_two).elim
      · have hp_eq : 6 * (p / 6) + 5 = p := by
          have hdivmod := Nat.div_add_mod p 6
          omega
        have hp_div_mem : p / 6 ∈ Finset.Icc 0 (k / 6) := by
          rw [Finset.mem_Icc]
          exact ⟨Nat.zero_le _, Nat.div_le_div_right hp_le_k⟩
        have hp_fives : p ∈ fives := by
          rw [Finset.mem_image]
          exact ⟨p / 6, hp_div_mem, hp_eq⟩
        exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr hp_fives
    have hp_ne1 : p ≠ 1 := ne_of_gt hp_prime.one_lt
    have hp_ne25 : p ≠ 25 := by
      intro hp_eq
      subst hp_eq
      norm_num at hp_prime
    have hp_ne35 : p ≠ 35 := by
      intro hp_eq
      subst hp_eq
      norm_num at hp_prime
    have hp_ne49 : p ≠ 49 := by
      intro hp_eq
      subst hp_eq
      norm_num at hp_prime
    simpa [trimmed, hp_ne1, hp_ne25, hp_ne35, hp_ne49] using hp_base
  have hbase_card : base.card ≤ 2 * (k / 6 + 1) + 2 := by
    have hbase_le : base.card ≤ (ones ∪ fives).card + 2 := by
      dsimp [base]
      calc
        (insert 2 (insert 3 (ones ∪ fives))).card
            ≤ (insert 3 (ones ∪ fives)).card + 1 :=
          Finset.card_insert_le 2 _
        _ ≤ ((ones ∪ fives).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le 3 _) 1
        _ = (ones ∪ fives).card + 2 := by omega
    have hunion_le : (ones ∪ fives).card ≤ ones.card + fives.card :=
      Finset.card_union_le ones fives
    have hones_card : ones.card ≤ k / 6 + 1 := by
      calc
        ones.card ≤ (Finset.Icc 0 (k / 6)).card := Finset.card_image_le
        _ = k / 6 + 1 := by
          rw [Nat.card_Icc]
          omega
    have hfives_card : fives.card ≤ k / 6 + 1 := by
      calc
        fives.card ≤ (Finset.Icc 0 (k / 6)).card := Finset.card_image_le
        _ = k / 6 + 1 := by
          rw [Nat.card_Icc]
          omega
    omega
  have htrim_card : trimmed.card = base.card - 4 := by
    have h25_after1 : 25 ∈ base.erase 1 := by
      rw [Finset.mem_erase]
      exact ⟨by norm_num, h25_base⟩
    have h35_after25 : 35 ∈ (base.erase 1).erase 25 := by
      simp [h35_base]
    have h49_after35 : 49 ∈ ((base.erase 1).erase 25).erase 35 := by
      simp [h49_base]
    dsimp [trimmed]
    rw [Finset.card_erase_of_mem h49_after35]
    rw [Finset.card_erase_of_mem h35_after25]
    rw [Finset.card_erase_of_mem h25_after1]
    rw [Finset.card_erase_of_mem h1_base]
    omega
  calc
    (k + 1).primesBelow.card ≤ trimmed.card := Finset.card_le_card hsubset
    _ = base.card - 4 := htrim_card
    _ ≤ (2 * (k / 6 + 1) + 2) - 4 := Nat.sub_le_sub_right hbase_card 4
    _ ≤ k / 3 := by omega

lemma prime_coprime_210 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    p.Coprime 210 := by
  rw [hp.coprime_iff_not_dvd]
  intro hdiv
  have hdiv' : p ∣ 2 * (3 * (5 * 7)) := by
    simpa [show 210 = 2 * (3 * (5 * 7)) by norm_num] using hdiv
  rcases hp.dvd_mul.mp hdiv' with h2 | hrest
  · have hp_eq : p = 2 := by
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have hp_ge : 2 ≤ p := hp.two_le
      omega
    exact hp2 hp_eq
  rcases hp.dvd_mul.mp hrest with h3 | hrest
  · have hp_eq : p = 3 := by
      have hp_le : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      have hp_ge : 2 ≤ p := hp.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · rfl
    exact hp3 hp_eq
  rcases hp.dvd_mul.mp hrest with h5 | h7
  · have hp_eq : p = 5 := by
      have hp_le : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
      have hp_ge : 2 ≤ p := hp.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · exact (hp3 rfl).elim
      · norm_num at hp
      · rfl
    exact hp5 hp_eq
  · have hp_eq : p = 7 := by
      have hp_le : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7
      have hp_ge : 2 ≤ p := hp.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · exact (hp3 rfl).elim
      · norm_num at hp
      · exact (hp5 rfl).elim
      · norm_num at hp
      · rfl
    exact hp7 hp_eq

lemma coprime_mod_210 {p : ℕ} (hcop : p.Coprime 210) : (p % 210).Coprime 210 := by
  rw [Nat.Coprime]
  rw [← Nat.gcd_rec 210 p, Nat.gcd_comm 210 p]
  exact hcop

lemma primesBelow_succ_card_le_fourth {k : ℕ} (hk : 2500 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 4 := by
  classical
  let residues : Finset ℕ := (Finset.range 210).filter (fun r => Nat.Coprime r 210)
  let candidates : Finset ℕ := (Finset.Icc 0 (k / 210)).biUnion fun q =>
    residues.image fun r => 210 * q + r
  let base : Finset ℕ := insert 2 (insert 3 (insert 5 (insert 7 candidates)))
  have hsubset : (k + 1).primesBelow ⊆ base := by
    intro p hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp_mem
    have hp_le_k : p ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp_mem)
    by_cases hp2 : p = 2
    · exact Finset.mem_insert.mpr (Or.inl hp2)
    by_cases hp3 : p = 3
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inl hp3
    by_cases hp5 : p = 5
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_insert.mpr <| Or.inl hp5
    by_cases hp7 : p = 7
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
        Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inl hp7
    have hcop : p.Coprime 210 := prime_coprime_210 hp_prime hp2 hp3 hp5 hp7
    have hres : p % 210 ∈ residues := by
      dsimp [residues]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.mod_lt p (by norm_num)), coprime_mod_210 hcop⟩
    have hq : p / 210 ∈ Finset.Icc 0 (k / 210) := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.zero_le _, Nat.div_le_div_right hp_le_k⟩
    have hp_eq : 210 * (p / 210) + p % 210 = p := Nat.div_add_mod p 210
    have hmem_cand : p ∈ candidates := by
      dsimp [candidates]
      rw [Finset.mem_biUnion]
      refine ⟨p / 210, hq, ?_⟩
      rw [Finset.mem_image]
      exact ⟨p % 210, hres, hp_eq⟩
    exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inr hmem_cand
  have hres_card : residues.card = 48 := by decide
  have hcand_card : candidates.card ≤ (k / 210 + 1) * 48 := by
    calc
      candidates.card ≤ (Finset.Icc 0 (k / 210)).card * 48 := by
        refine Finset.card_biUnion_le_card_mul _ _ 48 ?_
        intro q hq
        calc
          ((residues.image fun r => 210 * q + r).card) ≤ residues.card :=
            Finset.card_image_le
          _ = 48 := hres_card
      _ = (k / 210 + 1) * 48 := by
        rw [Nat.card_Icc]
        omega
  have hbase_card : base.card ≤ candidates.card + 4 := by
    dsimp [base]
    calc
      (insert 2 (insert 3 (insert 5 (insert 7 candidates)))).card
          ≤ (insert 3 (insert 5 (insert 7 candidates))).card + 1 :=
        Finset.card_insert_le 2 _
      _ ≤ ((insert 5 (insert 7 candidates)).card + 1) + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le 3 _) 1
      _ ≤ (((insert 7 candidates).card + 1) + 1) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_insert_le 5 _) 1) 1
      _ ≤ (((candidates.card + 1) + 1) + 1) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le 7 _) 1) 1) 1
      _ = candidates.card + 4 := by omega
  calc
    (k + 1).primesBelow.card ≤ base.card := Finset.card_le_card hsubset
    _ ≤ candidates.card + 4 := hbase_card
    _ ≤ (k / 210 + 1) * 48 + 4 := Nat.add_le_add_right hcand_card 4
    _ ≤ k / 4 := by omega

lemma pow_le_ascFactorial (m k : ℕ) : m ^ k ≤ m.ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.ascFactorial_succ, pow_succ]
      calc
        m ^ k * m ≤ m.ascFactorial k * (m + k) := Nat.mul_le_mul ih (Nat.le_add_right m k)
        _ = (m + k) * m.ascFactorial k := by ring

lemma ascFactorial_eq_factorial_mul_choose_start {m k : ℕ} (hm : 0 < m) :
    m.ascFactorial k = k.factorial * Nat.choose (m + k - 1) k := by
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm)
  have hm_add : m - 1 + k = m + k - 1 := by omega
  simpa [hm_sub, hm_add] using Nat.ascFactorial_eq_factorial_mul_choose (m - 1) k

lemma choose_inequality_of_prime_count_bound {m k r : ℕ}
    (hk : 0 < k) (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r)
    (hlarge : k.factorial * (m + k - 1) ^ r < m ^ k) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  let s := (k + 1).primesBelow.card
  have hm_pos : 0 < m := by omega
  have hN_pos : 0 < m + k - 1 := by omega
  have hpow_le : (m + k - 1) ^ s ≤ (m + k - 1) ^ r :=
    Nat.pow_le_pow_right hN_pos (by simpa [s] using hr_count)
  have hchoose_eq := ascFactorial_eq_factorial_mul_choose_start (m := m) (k := k) hm_pos
  have hmul_lt_choose :
      k.factorial * (m + k - 1) ^ s < k.factorial * Nat.choose (m + k - 1) k := by
    calc
      k.factorial * (m + k - 1) ^ s ≤ k.factorial * (m + k - 1) ^ r :=
        Nat.mul_le_mul_left _ hpow_le
      _ < m ^ k := hlarge
      _ ≤ m.ascFactorial k := pow_le_ascFactorial m k
      _ = k.factorial * Nat.choose (m + k - 1) k := hchoose_eq
  exact Nat.lt_of_mul_lt_mul_left hmul_lt_choose

theorem sylvester_schur_of_prime_count_bound
    (n i r : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ r)
    (hlarge : i.factorial * n ^ r < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_pos : 0 < i := hi
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn_pos : 0 < n := by omega
  have hm : i < n - i + 1 := by omega
  have hN_eq : n - i + 1 + i - 1 = n := by omega
  have hlarge' :
      i.factorial * (n - i + 1 + i - 1) ^ r < (n - i + 1) ^ i := by
    simpa [hN_eq] using hlarge
  have hineq_m := choose_inequality_of_prime_count_bound (m := n - i + 1) (k := i) (r := r)
    hi_pos hm hr_count hlarge'
  have hineq :
      n ^ (i + 1).primesBelow.card < Nat.choose n i := by
    simpa [hN_eq] using hineq_m
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count_direct hi_le_n hn_pos hineq

theorem sylvester_schur_of_half_prime_count_bound
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i.factorial * n ^ (i / 2) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_prime_count_bound n i (i / 2) (by omega) hi_half
    (primesBelow_succ_card_le_half hi) hlarge

theorem sylvester_schur_of_power_gap
    (n i r : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ r)
    (hgap : i ^ i * n ^ r < n ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn_pos : 0 < n := by omega
  by_contra hno
  have hsmall :
      ∀ p : ℕ, p.Prime → p ∣ Nat.choose n i → p < i + 1 := by
    intro p hp hp_choose
    by_contra hnot
    have hip : i < p := by omega
    exact hno ⟨p, hp, hip, hp_choose⟩
  have hchoose_le_count :
      Nat.choose n i ≤ n ^ (i + 1).primesBelow.card :=
    choose_le_pow_primesBelow_card_of_prime_factors_below hi_le_n hn_pos hsmall
  have hchoose_le : Nat.choose n i ≤ n ^ r :=
    hchoose_le_count.trans (Nat.pow_le_pow_right hn_pos hr_count)
  have hlower : n ^ i ≤ i ^ i * Nat.choose n i :=
    pow_le_pow_mul_choose n i hi_le_n
  have hupper : i ^ i * Nat.choose n i ≤ i ^ i * n ^ r :=
    Nat.mul_le_mul_left _ hchoose_le
  exact (not_lt_of_ge (hlower.trans hupper)) hgap

lemma choose_le_pow_sqrt_mul_primorial_third_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk_half : k ≤ n / 2)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ Nat.choose n k) :
    Nat.choose n k ≤ n ^ n.sqrt * primorial (n / 3) := by
  classical
  have hk_le_n : k ≤ n := le_trans hk_half (Nat.div_le_self n 2)
  let S : Finset ℕ := (Finset.range (n + 1)).filter fun p => p.Prime
  let small : Finset ℕ := S.filter fun p => p ≤ n.sqrt
  let medium : Finset ℕ := S.filter fun p => ¬ p ≤ n.sqrt
  let supportedMedium : Finset ℕ := medium.filter fun p => p ≤ n / 3
  let f := fun p : ℕ => p ^ (Nat.choose n k).factorization p
  have hchoose_prod : Nat.choose n k = ∏ p ∈ S, f p := by
    symm
    calc
      ∏ p ∈ S, f p = ∏ p ∈ Finset.range (n + 1), f p := by
        dsimp [S]
        exact Finset.prod_filter_of_ne fun p _ hp_ne_one => by
          by_contra hp_not_prime
          exact hp_ne_one (by simp [f, Nat.factorization_eq_zero_of_not_prime _ hp_not_prime])
      _ = Nat.choose n k := Nat.prod_pow_factorization_choose n k hk_le_n
  have hsmall_card : small.card ≤ n.sqrt := by
    have hsubset : small ⊆ Finset.Icc 1 n.sqrt := by
      intro p hp
      rw [Finset.mem_Icc]
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hple : p ≤ n.sqrt := (Finset.mem_filter.mp hp).2
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      exact ⟨hp_prime.one_lt.le, hple⟩
    have hcard := Finset.card_le_card hsubset
    have hIcc : (Finset.Icc 1 n.sqrt).card = n.sqrt := by
      rw [Nat.card_Icc]
      omega
    simpa [hIcc] using hcard
  have hsmall_le : ∏ p ∈ small, f p ≤ n ^ n.sqrt := by
    calc
      ∏ p ∈ small, f p ≤ ∏ _p ∈ small, n := by
        refine Finset.prod_le_prod' ?_
        intro p _hp
        exact Nat.pow_factorization_choose_le hn
      _ = n ^ small.card := by rw [Finset.prod_const]
      _ ≤ n ^ n.sqrt := Nat.pow_le_pow_right hn hsmall_card
  have hmedium_eq_supported : ∏ p ∈ medium, f p = ∏ p ∈ supportedMedium, f p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hp_medium hp_not_supported
    have hp_not_third : ¬ p ≤ n / 3 := by
      intro hp_third
      exact hp_not_supported (Finset.mem_filter.mpr ⟨hp_medium, hp_third⟩)
    have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
    have hp_not_small : ¬ p ≤ n.sqrt := (Finset.mem_filter.mp hp_medium).2
    have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
    by_cases hkp : k < p
    · have hfac : (Nat.choose n k).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (hno p hp_prime hkp)
      simp [f, hfac]
    · have hpk : p ≤ k := Nat.le_of_not_gt hkp
      have hpnk : p ≤ n - k := by omega
      have hp_ne_two : p ≠ 2 := by
        intro hp_two
        subst p
        have h4n : 4 ≤ n := by omega
        have hsqrt : 2 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa using h4n)
        exact hp_not_small hsqrt
      have hn_lt_3p : n < 3 * p := by
        have hp_gt_third : n / 3 < p := Nat.lt_of_not_ge hp_not_third
        rwa [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3), mul_comm] at hp_gt_third
      have hfac : (Nat.choose n k).factorization p = 0 :=
        Nat.factorization_choose_of_lt_three_mul hp_ne_two hpk hpnk hn_lt_3p
      simp [f, hfac]
  have hmedium_le : ∏ p ∈ medium, f p ≤ primorial (n / 3) := by
    have hsupp_le : ∏ p ∈ supportedMedium, f p ≤ ∏ p ∈ supportedMedium, p := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      have hp_medium : p ∈ medium := (Finset.mem_filter.mp hp).1
      have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
      have hp_not_small : ¬ p ≤ n.sqrt := (Finset.mem_filter.mp hp_medium).2
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      have hp_large : n < p ^ 2 := Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hp_not_small)
      have hfac_le : (Nat.choose n k).factorization p ≤ 1 :=
        Nat.factorization_choose_le_one hp_large
      exact (Nat.pow_le_pow_right hp_prime.one_lt.le hfac_le).trans_eq (by rw [pow_one])
    have hsupp_subset :
        supportedMedium ⊆ (Finset.range (n / 3 + 1)).filter fun p => p.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range]
      have hp_medium : p ∈ medium := (Finset.mem_filter.mp hp).1
      have hp_third : p ≤ n / 3 := (Finset.mem_filter.mp hp).2
      have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      exact ⟨Nat.lt_succ_iff.mpr hp_third, hp_prime⟩
    have hprimorial :
        ∏ p ∈ supportedMedium, p ≤ primorial (n / 3) := by
      simpa [primorial] using
        (Finset.prod_le_prod_of_subset_of_one_le' (f := fun p : ℕ => p) hsupp_subset
          (fun p hp hp_not => by
            have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
            exact hp_prime.one_lt.le))
    calc
      ∏ p ∈ medium, f p = ∏ p ∈ supportedMedium, f p := hmedium_eq_supported
      _ ≤ ∏ p ∈ supportedMedium, p := hsupp_le
      _ ≤ primorial (n / 3) := hprimorial
  calc
    Nat.choose n k = ∏ p ∈ S, f p := hchoose_prod
    _ = (∏ p ∈ small, f p) * ∏ p ∈ medium, f p := by
      dsimp [small, medium]
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ ≤ n ^ n.sqrt * primorial (n / 3) := Nat.mul_le_mul hsmall_le hmedium_le

lemma choose_le_pow_sqrt_mul_primorial_index_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk_half : k ≤ n / 2)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ Nat.choose n k) :
    Nat.choose n k ≤ n ^ n.sqrt * primorial k := by
  classical
  have hk_le_n : k ≤ n := le_trans hk_half (Nat.div_le_self n 2)
  let S : Finset ℕ := (Finset.range (n + 1)).filter fun p => p.Prime
  let small : Finset ℕ := S.filter fun p => p ≤ n.sqrt
  let medium : Finset ℕ := S.filter fun p => ¬ p ≤ n.sqrt
  let supportedMedium : Finset ℕ := medium.filter fun p => p ≤ k
  let f := fun p : ℕ => p ^ (Nat.choose n k).factorization p
  have hchoose_prod : Nat.choose n k = ∏ p ∈ S, f p := by
    symm
    calc
      ∏ p ∈ S, f p = ∏ p ∈ Finset.range (n + 1), f p := by
        dsimp [S]
        exact Finset.prod_filter_of_ne fun p _ hp_ne_one => by
          by_contra hp_not_prime
          exact hp_ne_one (by simp [f, Nat.factorization_eq_zero_of_not_prime _ hp_not_prime])
      _ = Nat.choose n k := Nat.prod_pow_factorization_choose n k hk_le_n
  have hsmall_card : small.card ≤ n.sqrt := by
    have hsubset : small ⊆ Finset.Icc 1 n.sqrt := by
      intro p hp
      rw [Finset.mem_Icc]
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hple : p ≤ n.sqrt := (Finset.mem_filter.mp hp).2
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      exact ⟨hp_prime.one_lt.le, hple⟩
    have hcard := Finset.card_le_card hsubset
    have hIcc : (Finset.Icc 1 n.sqrt).card = n.sqrt := by
      rw [Nat.card_Icc]
      omega
    simpa [hIcc] using hcard
  have hsmall_le : ∏ p ∈ small, f p ≤ n ^ n.sqrt := by
    calc
      ∏ p ∈ small, f p ≤ ∏ _p ∈ small, n := by
        refine Finset.prod_le_prod' ?_
        intro p _hp
        exact Nat.pow_factorization_choose_le hn
      _ = n ^ small.card := by rw [Finset.prod_const]
      _ ≤ n ^ n.sqrt := Nat.pow_le_pow_right hn hsmall_card
  have hmedium_eq_supported : ∏ p ∈ medium, f p = ∏ p ∈ supportedMedium, f p := by
    symm
    refine Finset.prod_subset (Finset.filter_subset _ _) ?_
    intro p hp_medium hp_not_supported
    have hp_not_le_k : ¬ p ≤ k := by
      intro hp_le_k
      exact hp_not_supported (Finset.mem_filter.mpr ⟨hp_medium, hp_le_k⟩)
    have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
    have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
    have hkp : k < p := Nat.lt_of_not_ge hp_not_le_k
    have hfac : (Nat.choose n k).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (hno p hp_prime hkp)
    simp [f, hfac]
  have hmedium_le : ∏ p ∈ medium, f p ≤ primorial k := by
    have hsupp_le : ∏ p ∈ supportedMedium, f p ≤ ∏ p ∈ supportedMedium, p := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      have hp_medium : p ∈ medium := (Finset.mem_filter.mp hp).1
      have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
      have hp_not_small : ¬ p ≤ n.sqrt := (Finset.mem_filter.mp hp_medium).2
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      have hp_large : n < p ^ 2 := Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hp_not_small)
      have hfac_le : (Nat.choose n k).factorization p ≤ 1 :=
        Nat.factorization_choose_le_one hp_large
      exact (Nat.pow_le_pow_right hp_prime.one_lt.le hfac_le).trans_eq (by rw [pow_one])
    have hsupp_subset :
        supportedMedium ⊆ (Finset.range (k + 1)).filter fun p => p.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range]
      have hp_medium : p ∈ medium := (Finset.mem_filter.mp hp).1
      have hp_le_k : p ≤ k := (Finset.mem_filter.mp hp).2
      have hpS : p ∈ S := (Finset.mem_filter.mp hp_medium).1
      have hp_prime : p.Prime := (Finset.mem_filter.mp hpS).2
      exact ⟨Nat.lt_succ_iff.mpr hp_le_k, hp_prime⟩
    have hprimorial :
        ∏ p ∈ supportedMedium, p ≤ primorial k := by
      simpa [primorial] using
        (Finset.prod_le_prod_of_subset_of_one_le' (f := fun p : ℕ => p) hsupp_subset
          (fun p hp hp_not => by
            have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
            exact hp_prime.one_lt.le))
    calc
      ∏ p ∈ medium, f p = ∏ p ∈ supportedMedium, f p := hmedium_eq_supported
      _ ≤ ∏ p ∈ supportedMedium, p := hsupp_le
      _ ≤ primorial k := hprimorial
  calc
    Nat.choose n k = ∏ p ∈ S, f p := hchoose_prod
    _ = (∏ p ∈ small, f p) * ∏ p ∈ medium, f p := by
      dsimp [small, medium]
      rw [Finset.prod_filter_mul_prod_filter_not]
    _ ≤ n ^ n.sqrt * primorial k := Nat.mul_le_mul hsmall_le hmedium_le

lemma centralBinom_le_choose_of_half {n i : ℕ} (hi_half : i ≤ n / 2) :
    i.centralBinom ≤ Nat.choose n i := by
  have htwice : 2 * i ≤ n := by omega
  simpa [Nat.centralBinom] using Nat.choose_le_choose i htwice

lemma pow_mul_ascFactorial_le_pow_mul_ascFactorial_of_twice_le
    {n i : ℕ} (htwice : 2 * i ≤ n) :
    n ^ i * (i + 1).ascFactorial i ≤
      (2 * i) ^ i * (n - i + 1).ascFactorial i := by
  rw [Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_prod_range]
  calc
    n ^ i * (∏ t ∈ Finset.range i, (i + 1 + t))
        = (∏ _t ∈ Finset.range i, n) *
            ∏ t ∈ Finset.range i, (i + 1 + t) := by
          rw [Finset.prod_const, Finset.card_range]
    _ = ∏ t ∈ Finset.range i, (n * (i + 1 + t)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ ∏ t ∈ Finset.range i, ((2 * i) * (n - i + 1 + t)) := by
          refine Finset.prod_le_prod' ?_
          intro t ht
          rw [Finset.mem_range] at ht
          have hni : i ≤ n := by omega
          zify [hni] at *
          nlinarith [htwice, ht]
    _ = (∏ _t ∈ Finset.range i, (2 * i)) *
          ∏ t ∈ Finset.range i, (n - i + 1 + t) := by
          rw [Finset.prod_mul_distrib]
    _ = (2 * i) ^ i * ∏ t ∈ Finset.range i, (n - i + 1 + t) := by
          rw [Finset.prod_const, Finset.card_range]

lemma pow_mul_centralBinom_le_pow_mul_choose_of_half
    {n i : ℕ} (hi_half : i ≤ n / 2) :
    n ^ i * i.centralBinom ≤ (2 * i) ^ i * Nat.choose n i := by
  have htwice : 2 * i ≤ n := by omega
  have hm_pos : 0 < n - i + 1 := by omega
  have htop : n - i + 1 + i - 1 = n := by omega
  have hratio :=
    pow_mul_ascFactorial_le_pow_mul_ascFactorial_of_twice_le (n := n) (i := i) htwice
  refine Nat.le_of_mul_le_mul_left ?_ i.factorial_pos
  calc
    i.factorial * (n ^ i * i.centralBinom)
        = n ^ i * (i.factorial * i.centralBinom) := by ring
    _ = n ^ i * (i + 1).ascFactorial i := by
          rw [Nat.centralBinom, Nat.ascFactorial_eq_factorial_mul_choose, two_mul]
    _ ≤ (2 * i) ^ i * (n - i + 1).ascFactorial i := hratio
    _ = (2 * i) ^ i * (i.factorial * Nat.choose n i) := by
          rw [ascFactorial_eq_factorial_mul_choose_start (m := n - i + 1) (k := i) hm_pos,
            htop]
    _ = i.factorial * ((2 * i) ^ i * Nat.choose n i) := by ring

theorem sylvester_schur_of_central_primorial_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * (n ^ n.sqrt * primorial (n / 3)) < 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_contra hno_exists
  have hno : ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.choose n i := by
    intro p hp hip hp_choose
    exact hno_exists ⟨p, hp, hip, hp_choose⟩
  have hn : 0 < n := by omega
  have hupper :
      Nat.choose n i ≤ n ^ n.sqrt * primorial (n / 3) :=
    choose_le_pow_sqrt_mul_primorial_third_of_no_large_prime hn hi_half hno
  have hcentral_le : i.centralBinom ≤ Nat.choose n i :=
    centralBinom_le_choose_of_half hi_half
  have hlower : 4 ^ i < i * Nat.choose n i :=
    (Nat.four_pow_lt_mul_centralBinom i hi).trans_le
      (Nat.mul_le_mul_left i hcentral_le)
  have hupper_mul :
      i * Nat.choose n i ≤ i * (n ^ n.sqrt * primorial (n / 3)) :=
    Nat.mul_le_mul_left i hupper
  exact (not_lt_of_ge (hlower.trans_le hupper_mul).le) hgap

theorem sylvester_schur_of_central_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hprimorial : primorial (n / 3) ≤ 4 ^ (n / 3) :=
    primorial_le_4_pow (n / 3)
  have hgap' : i * (n ^ n.sqrt * primorial (n / 3)) < 4 ^ i := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left i (Nat.mul_le_mul_left (n ^ n.sqrt) hprimorial)) hgap
  exact sylvester_schur_of_central_primorial_gap n i hi hi_half hgap'

section FiveHalvesCentralGap

open Real

lemma central_gap_of_le_five_halves {n i : ℕ} (hi_large : 4410 ≤ i)
    (hi_half : i ≤ n / 2) (hn_le : 2 * n ≤ 5 * i) :
    i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i := by
  let B : ℝ := (5 : ℝ) / 2 * i
  have hn_pos : 0 < n := by omega
  have hn_real_le : (n : ℝ) ≤ B := by
    dsimp [B]
    nlinarith [show (2 : ℝ) * n ≤ (5 : ℝ) * i by exact_mod_cast hn_le]
  have hbase_ge_one : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith [show (1 : ℝ) ≤ i by exact_mod_cast (by omega : 1 ≤ i)]
  have hn_pow_le : (n : ℝ) ^ n.sqrt ≤ B ^ √B := by
    calc
      (n : ℝ) ^ n.sqrt = (n : ℝ) ^ (n.sqrt : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ √(n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Nat.succ_le_of_lt hn_pos)) Real.nat_sqrt_le_real_sqrt
      _ ≤ B ^ √(n : ℝ) :=
        Real.rpow_le_rpow (by positivity) hn_real_le (Real.sqrt_nonneg _)
      _ ≤ B ^ √B :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge_one (Real.sqrt_le_sqrt hn_real_le)
  have hdiv_le : ((n / 3 : ℕ) : ℝ) ≤ B / 3 := by
    calc
      ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := Nat.cast_div_le
      _ ≤ B / 3 := by gcongr
  have hfour_le : (4 : ℝ) ^ (n / 3) ≤ 4 ^ (B / 3) := by
    calc
      (4 : ℝ) ^ (n / 3) = (4 : ℝ) ^ ((n / 3 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ 4 ^ (B / 3) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv_le
  have hrealB : (i : ℝ) * B ^ √B * 4 ^ (B / 3) < 4 ^ (i : ℝ) := by
    simpa [B] using
      real_central_gap_five_halves (x := (i : ℝ)) (by exact_mod_cast hi_large)
  have hcast : ((i * (n ^ n.sqrt * 4 ^ (n / 3))) : ℝ) < ((4 ^ i) : ℝ) := by
    calc
      (i : ℝ) * ((n : ℝ) ^ n.sqrt * (4 : ℝ) ^ (n / 3))
          ≤ (i : ℝ) * (B ^ √B * 4 ^ (B / 3)) := by
            gcongr
      _ = (i : ℝ) * B ^ √B * 4 ^ (B / 3) := by ring
      _ < 4 ^ (i : ℝ) := hrealB
      _ = (4 : ℝ) ^ i := by rw [Real.rpow_natCast]
  exact_mod_cast hcast

theorem sylvester_schur_of_central_five_halves
    (n i : ℕ) (hi_large : 4410 ≤ i) (hi_half : i ≤ n / 2)
    (hn_le : 2 * n ≤ 5 * i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_central_gap n i (by omega) hi_half
    (central_gap_of_le_five_halves hi_large hi_half hn_le)

end FiveHalvesCentralGap

section ScaledPowerDerivativeGap

open Real

lemma scaled_power_gap_of_deriv_bound {n i : ℕ} (hi_large : 4840 ≤ i)
    (hi_half : i ≤ n / 2) (hn_lower : 5 * i ≤ 2 * n)
    (hderiv : ∀ z ∈ Set.Icc (((5 : ℝ) / 2) * i) n,
      √z * (2 + log z) ≤ 2 * (i : ℝ)) :
    i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i := by
  have hi_pos_nat : 0 < i := by omega
  have hn_pos_nat : 0 < n := by omega
  have hx_large : (4840 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi_large
  have hy_lower : (5 : ℝ) / 2 * (i : ℝ) ≤ (n : ℝ) := by
    nlinarith [show (5 : ℝ) * i ≤ 2 * (n : ℝ) by exact_mod_cast hn_lower]
  have hreal :=
    real_scaled_power_of_deriv_bound (x := (i : ℝ)) (y := (n : ℝ))
      hx_large hy_lower hderiv
  have hpow_le : (n : ℝ) ^ n.sqrt ≤ (n : ℝ) ^ √(n : ℝ) := by
    calc
      (n : ℝ) ^ n.sqrt = (n : ℝ) ^ (n.sqrt : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (n : ℝ) ^ √(n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (Nat.succ_le_of_lt hn_pos_nat)) Real.nat_sqrt_le_real_sqrt
  have hreal_nat_sqrt :
      (i : ℝ) * (n : ℝ) ^ n.sqrt < ((n : ℝ) / (2 * (i : ℝ))) ^ (i : ℝ) := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow_le (by positivity)) hreal
  have hmul_pos : 0 < (2 * (i : ℝ)) ^ i := pow_pos (by positivity) i
  have hreal_scaled :
      (i : ℝ) * ((2 * i : ℕ) ^ i * (n ^ n.sqrt : ℕ)) < (n : ℝ) ^ i := by
    calc
      (i : ℝ) * ((2 * i : ℕ) ^ i * (n ^ n.sqrt : ℕ))
          = (2 * (i : ℝ)) ^ i * ((i : ℝ) * (n : ℝ) ^ n.sqrt) := by
            norm_num [mul_assoc, mul_comm, mul_left_comm]
      _ < (2 * (i : ℝ)) ^ i * (((n : ℝ) / (2 * (i : ℝ))) ^ (i : ℝ)) :=
            mul_lt_mul_of_pos_left hreal_nat_sqrt hmul_pos
      _ = (n : ℝ) ^ i := by
            rw [← Real.rpow_natCast]
            rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * (i : ℝ))
              (by positivity : 0 ≤ (n : ℝ) / (2 * (i : ℝ)))]
            have hbase : (2 * (i : ℝ)) * ((n : ℝ) / (2 * (i : ℝ))) = (n : ℝ) := by
              field_simp [(by positivity : (2 * (i : ℝ)) ≠ 0)]
            rw [hbase, Real.rpow_natCast]
  exact_mod_cast hreal_scaled

end ScaledPowerDerivativeGap

theorem sylvester_schur_of_factorial_primorial_gap
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i.factorial * (n ^ n.sqrt * primorial i) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_contra hno_exists
  have hno : ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.choose n i := by
    intro p hp hip hp_choose
    exact hno_exists ⟨p, hp, hip, hp_choose⟩
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hn : 0 < n := by omega
  have hm_pos : 0 < n - i + 1 := by omega
  have hupper :
      Nat.choose n i ≤ n ^ n.sqrt * primorial i :=
    choose_le_pow_sqrt_mul_primorial_index_of_no_large_prime hn hi_half hno
  have htop : n - i + 1 + i - 1 = n := by omega
  have hasc_choose :
      (n - i + 1).ascFactorial i = i.factorial * Nat.choose n i := by
    simpa [htop] using ascFactorial_eq_factorial_mul_choose_start
      (m := n - i + 1) (k := i) hm_pos
  have hlower :
      (n - i + 1) ^ i ≤ i.factorial * Nat.choose n i := by
    simpa [hasc_choose] using pow_le_ascFactorial (n - i + 1) i
  have hupper_mul :
      i.factorial * Nat.choose n i ≤ i.factorial * (n ^ n.sqrt * primorial i) :=
    Nat.mul_le_mul_left i.factorial hupper
  exact (not_lt_of_ge (hlower.trans hupper_mul)) hgap

theorem sylvester_schur_of_factorial_gap
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i.factorial * (n ^ n.sqrt * 4 ^ i) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hprimorial : primorial i ≤ 4 ^ i := primorial_le_4_pow i
  have hgap' : i.factorial * (n ^ n.sqrt * primorial i) < (n - i + 1) ^ i := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left i.factorial
        (Nat.mul_le_mul_left (n ^ n.sqrt) hprimorial)) hgap
  exact sylvester_schur_of_factorial_primorial_gap n i hi hi_half hgap'

theorem sylvester_schur_of_scaled_central_primorial_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * (n ^ n.sqrt * primorial i)) < n ^ i * 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_contra hno_exists
  have hno : ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.choose n i := by
    intro p hp hip hp_choose
    exact hno_exists ⟨p, hp, hip, hp_choose⟩
  have hn : 0 < n := by omega
  have hupper :
      Nat.choose n i ≤ n ^ n.sqrt * primorial i :=
    choose_le_pow_sqrt_mul_primorial_index_of_no_large_prime hn hi_half hno
  have hscaled_lower :
      n ^ i * 4 ^ i < i * ((2 * i) ^ i * Nat.choose n i) := by
    calc
      n ^ i * 4 ^ i < n ^ i * (i * i.centralBinom) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.four_pow_lt_mul_centralBinom i hi)
          (Nat.pow_pos (a := n) (n := i) hn)
      _ = i * (n ^ i * i.centralBinom) := by ring
      _ ≤ i * ((2 * i) ^ i * Nat.choose n i) :=
        Nat.mul_le_mul_left i (pow_mul_centralBinom_le_pow_mul_choose_of_half hi_half)
  have hscaled_upper :
      i * ((2 * i) ^ i * Nat.choose n i) ≤
        i * ((2 * i) ^ i * (n ^ n.sqrt * primorial i)) := by
    exact Nat.mul_le_mul_left i (Nat.mul_le_mul_left ((2 * i) ^ i) hupper)
  exact (not_lt_of_ge (hscaled_lower.trans_le hscaled_upper).le) hgap

theorem sylvester_schur_of_scaled_central_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i)) < n ^ i * 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hprimorial : primorial i ≤ 4 ^ i := primorial_le_4_pow i
  have hgap' :
      i * ((2 * i) ^ i * (n ^ n.sqrt * primorial i)) < n ^ i * 4 ^ i := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_left i
        (Nat.mul_le_mul_left ((2 * i) ^ i)
          (Nat.mul_le_mul_left (n ^ n.sqrt) hprimorial))) hgap
  exact sylvester_schur_of_scaled_central_primorial_gap n i hi hi_half hgap'

theorem sylvester_schur_of_scaled_central_power_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hgap' :
      i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i)) < n ^ i * 4 ^ i := by
    calc
      i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i))
          = (i * ((2 * i) ^ i * n ^ n.sqrt)) * 4 ^ i := by ring
      _ < n ^ i * 4 ^ i :=
          Nat.mul_lt_mul_of_pos_right hgap
            (Nat.pow_pos (a := 4) (n := i) (by norm_num))
  exact sylvester_schur_of_scaled_central_gap n i hi hi_half hgap'

section ScaledPowerDerivativeCriterion

open Real

theorem sylvester_schur_of_scaled_power_deriv_bound
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2)
    (hn_lower : 5 * i ≤ 2 * n)
    (hderiv : ∀ z ∈ Set.Icc (((5 : ℝ) / 2) * i) n,
      √z * (2 + log z) ≤ 2 * (i : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_scaled_central_power_gap n i (by omega) hi_half
    (scaled_power_gap_of_deriv_bound hi_large hi_half hn_lower hderiv)

lemma scaled_power_gap_of_four_thirds_window {n i : ℕ} (hi_large : 4840 ≤ i)
    (hi_half : i ≤ n / 2) (hn_lower : 5 * i ≤ 2 * n) (hn_upper : n ^ 3 ≤ i ^ 4) :
    i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i := by
  exact scaled_power_gap_of_deriv_bound (n := n) (i := i) (by omega) hi_half hn_lower (by
    intro z hz
    have hz_pos : 0 < z := by
      have hi_pos : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
      nlinarith [hz.1, hi_pos]
    have hz_nonneg : 0 ≤ z := le_of_lt hz_pos
    have hz_cube_le_n : z ^ (3 : ℕ) ≤ (n : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hz_nonneg hz.2 3
    have hn_cube : (n : ℝ) ^ (3 : ℕ) ≤ (i : ℝ) ^ (4 : ℕ) := by
      exact_mod_cast hn_upper
    exact real_deriv_bound_four_thirds (x := (i : ℝ)) (y := z)
      (by exact_mod_cast hi_large) hz_pos (hz_cube_le_n.trans hn_cube))

theorem sylvester_schur_of_four_thirds_window
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2)
    (hn_lower : 5 * i ≤ 2 * n) (hn_upper : n ^ 3 ≤ i ^ 4) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_scaled_central_power_gap n i (by omega) hi_half
    (scaled_power_gap_of_four_thirds_window hi_large hi_half hn_lower hn_upper)

end ScaledPowerDerivativeCriterion

lemma pow_mul_pow_half_lt_pow_of_sq_lt {n i : ℕ} (hi : 0 < i) (hlarge : i ^ 2 < n) :
    i ^ i * n ^ (i / 2) < n ^ i := by
  let r := i / 2
  let d := i - r
  have hd_pos : 0 < d := by
    dsimp [d, r]
    omega
  have hi_exp_le : i ≤ 2 * d := by
    dsimp [d, r]
    omega
  have hi_pow_lt : i ^ i < n ^ d := by
    calc
      i ^ i ≤ i ^ (2 * d) := Nat.pow_le_pow_right hi hi_exp_le
      _ = (i ^ 2) ^ d := by rw [pow_mul]
      _ < n ^ d := Nat.pow_lt_pow_left hlarge hd_pos.ne'
  calc
    i ^ i * n ^ (i / 2) = i ^ i * n ^ r := by rfl
    _ < n ^ d * n ^ r :=
      Nat.mul_lt_mul_of_pos_right hi_pow_lt (Nat.pow_pos (a := n) (n := r) (by omega))
    _ = n ^ (d + r) := by rw [← pow_add]
    _ = n ^ i := by
      congr 1
      dsimp [d, r]
      omega

lemma pow_mul_pow_third_lt_pow_of_cube_lt_sq {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hlarge : i ^ 3 < n ^ 2) :
    i ^ i * n ^ (i / 3) < n ^ i := by
  let q := i / 3
  have hn_pos : 0 < n := lt_trans hi hin
  have hmod_lt : i % 3 < 3 := Nat.mod_lt i (by norm_num)
  have hdivmod : 3 * (i / 3) + i % 3 = i := Nat.div_add_mod i 3
  have hi_pow_lt : i ^ i < n ^ (i - q) := by
    interval_cases hmod : i % 3
    · have hi_eq : i = 3 * q := by
        dsimp [q] at *
        omega
      have hq_pos : 0 < q := by omega
      calc
        i ^ i = (i ^ 3) ^ q := by
          rw [hi_eq, pow_mul]
        _ < (n ^ 2) ^ q := Nat.pow_lt_pow_left hlarge hq_pos.ne'
        _ = n ^ (2 * q) := by rw [pow_mul]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 3 * q + 1 := by
        dsimp [q] at *
        omega
      have hcube_le : (i ^ 3) ^ q ≤ (n ^ 2) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      calc
        i ^ i = (i ^ 3) ^ q * i := by
          rw [hi_eq, pow_add, pow_mul, pow_one]
        _ ≤ (n ^ 2) ^ q * i := Nat.mul_le_mul_right _ hcube_le
        _ < (n ^ 2) ^ q * n :=
          Nat.mul_lt_mul_of_pos_left hin
            (Nat.pow_pos (a := n ^ 2) (n := q) (Nat.pow_pos (a := n) (n := 2) hn_pos))
        _ = n ^ (2 * q + 1) := by
          rw [← pow_mul, ← pow_succ]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 3 * q + 2 := by
        dsimp [q] at *
        omega
      have hcube_le : (i ^ 3) ^ q ≤ (n ^ 2) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      have hsquare_lt : i ^ 2 < n ^ 2 :=
        Nat.pow_lt_pow_left hin (by norm_num)
      calc
        i ^ i = (i ^ 3) ^ q * i ^ 2 := by
          rw [hi_eq, pow_add, pow_mul]
        _ ≤ (n ^ 2) ^ q * i ^ 2 := Nat.mul_le_mul_right _ hcube_le
        _ < (n ^ 2) ^ q * n ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hsquare_lt
            (Nat.pow_pos (a := n ^ 2) (n := q) (Nat.pow_pos (a := n) (n := 2) hn_pos))
        _ = n ^ (2 * q + 2) := by
          rw [← pow_mul, ← pow_add]
        _ = n ^ (i - q) := by
          congr 1
          omega
  calc
    i ^ i * n ^ (i / 3) = i ^ i * n ^ q := by rfl
    _ < n ^ (i - q) * n ^ q :=
      Nat.mul_lt_mul_of_pos_right hi_pow_lt (Nat.pow_pos (a := n) (n := q) hn_pos)
    _ = n ^ (i - q + q) := by rw [← pow_add]
    _ = n ^ i := by
      congr 1
      dsimp [q]
      omega

theorem sylvester_schur_of_third_prime_count_bound
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ i / 3)
    (hlarge : i ^ 3 < n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_power_gap n i (i / 3) hi hi_half hr_count
    (pow_mul_pow_third_lt_pow_of_cube_lt_sq (by omega) (by omega) hlarge)

theorem sylvester_schur_of_cube_lt_square
    (n i : ℕ) (hi : 49 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 3 < n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_third_prime_count_bound n i (by omega) hi_half
    (primesBelow_succ_card_le_third hi) hlarge

lemma pow_mul_pow_fourth_lt_pow_of_fourth_lt_cube {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hlarge : i ^ 4 < n ^ 3) :
    i ^ i * n ^ (i / 4) < n ^ i := by
  let q := i / 4
  have hn_pos : 0 < n := lt_trans hi hin
  have hmod_lt : i % 4 < 4 := Nat.mod_lt i (by norm_num)
  have hdivmod : 4 * (i / 4) + i % 4 = i := Nat.div_add_mod i 4
  have hi_pow_lt : i ^ i < n ^ (i - q) := by
    interval_cases hmod : i % 4
    · have hi_eq : i = 4 * q := by
        dsimp [q] at *
        omega
      have hq_pos : 0 < q := by omega
      calc
        i ^ i = (i ^ 4) ^ q := by
          rw [hi_eq, pow_mul]
        _ < (n ^ 3) ^ q := Nat.pow_lt_pow_left hlarge hq_pos.ne'
        _ = n ^ (3 * q) := by rw [pow_mul]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 4 * q + 1 := by
        dsimp [q] at *
        omega
      have hfour_le : (i ^ 4) ^ q ≤ (n ^ 3) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      calc
        i ^ i = (i ^ 4) ^ q * i := by
          rw [hi_eq, pow_add, pow_mul, pow_one]
        _ ≤ (n ^ 3) ^ q * i := Nat.mul_le_mul_right _ hfour_le
        _ < (n ^ 3) ^ q * n :=
          Nat.mul_lt_mul_of_pos_left hin
            (Nat.pow_pos (a := n ^ 3) (n := q) (Nat.pow_pos (a := n) (n := 3) hn_pos))
        _ = n ^ (3 * q + 1) := by
          rw [← pow_mul, ← pow_succ]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 4 * q + 2 := by
        dsimp [q] at *
        omega
      have hfour_le : (i ^ 4) ^ q ≤ (n ^ 3) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      have hsquare_lt : i ^ 2 < n ^ 2 :=
        Nat.pow_lt_pow_left hin (by norm_num)
      calc
        i ^ i = (i ^ 4) ^ q * i ^ 2 := by
          rw [hi_eq, pow_add, pow_mul]
        _ ≤ (n ^ 3) ^ q * i ^ 2 := Nat.mul_le_mul_right _ hfour_le
        _ < (n ^ 3) ^ q * n ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hsquare_lt
            (Nat.pow_pos (a := n ^ 3) (n := q) (Nat.pow_pos (a := n) (n := 3) hn_pos))
        _ = n ^ (3 * q + 2) := by
          rw [← pow_mul, ← pow_add]
        _ = n ^ (i - q) := by
          congr 1
          omega
    · have hi_eq : i = 4 * q + 3 := by
        dsimp [q] at *
        omega
      have hfour_le : (i ^ 4) ^ q ≤ (n ^ 3) ^ q :=
        Nat.pow_le_pow_left hlarge.le q
      have hcube_lt : i ^ 3 < n ^ 3 :=
        Nat.pow_lt_pow_left hin (by norm_num)
      calc
        i ^ i = (i ^ 4) ^ q * i ^ 3 := by
          rw [hi_eq, pow_add, pow_mul]
        _ ≤ (n ^ 3) ^ q * i ^ 3 := Nat.mul_le_mul_right _ hfour_le
        _ < (n ^ 3) ^ q * n ^ 3 :=
          Nat.mul_lt_mul_of_pos_left hcube_lt
            (Nat.pow_pos (a := n ^ 3) (n := q) (Nat.pow_pos (a := n) (n := 3) hn_pos))
        _ = n ^ (3 * q + 3) := by
          rw [← pow_mul, ← pow_add]
        _ = n ^ (i - q) := by
          congr 1
          omega
  calc
    i ^ i * n ^ (i / 4) = i ^ i * n ^ q := by rfl
    _ < n ^ (i - q) * n ^ q :=
      Nat.mul_lt_mul_of_pos_right hi_pow_lt (Nat.pow_pos (a := n) (n := q) hn_pos)
    _ = n ^ (i - q + q) := by rw [← pow_add]
    _ = n ^ i := by
      congr 1
      dsimp [q]
      omega

theorem sylvester_schur_of_fourth_prime_count_bound
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ i / 4)
    (hlarge : i ^ 4 < n ^ 3) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_power_gap n i (i / 4) hi hi_half hr_count
    (pow_mul_pow_fourth_lt_pow_of_fourth_lt_cube (by omega) (by omega) hlarge)

theorem sylvester_schur_of_fourth_lt_cube
    (n i : ℕ) (hi : 2500 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 4 < n ^ 3) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_fourth_prime_count_bound n i (by omega) hi_half
    (primesBelow_succ_card_le_fourth hi) hlarge

theorem sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_cases hcentral : 2 * n ≤ 5 * i
  · exact sylvester_schur_of_central_five_halves n i (by omega) hi_half hcentral
  · have hn_lower : 5 * i ≤ 2 * n := by omega
    by_cases htop : i ^ 4 < n ^ 3
    · exact sylvester_schur_of_fourth_lt_cube n i (by omega) hi_half htop
    · exact sylvester_schur_of_four_thirds_window n i hi_large hi_half hn_lower
        (Nat.le_of_not_gt htop)

theorem sylvester_schur_of_superquadratic_top
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2) (hlarge : i ^ 2 < n) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_power_gap n i (i / 2) (by omega) hi_half
    (primesBelow_succ_card_le_half hi)
    (pow_mul_pow_half_lt_pow_of_sq_lt (by omega) hlarge)

lemma factorial_mul_pow_half_lt_of_quadratic_large {n i : ℕ} (hi : 8 ≤ i)
    (hi_half : i ≤ n / 2) (hm_large : 4 * i ^ 2 ≤ n - i + 1) :
    i.factorial * n ^ (i / 2) < (n - i + 1) ^ i := by
  let m := n - i + 1
  let r := i / 2
  let d := i - r
  have hi_pos : 0 < i := by omega
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hn_le : n ≤ 2 * m := by
    dsimp [m]
    omega
  have hbase : 4 * i ^ 2 ≤ m := by simpa [m] using hm_large
  have hfac : i.factorial ≤ i ^ i := Nat.factorial_le_pow i
  have hn_pow : n ^ r ≤ (2 * m) ^ r := Nat.pow_le_pow_left hn_le r
  have hleft_le : i.factorial * n ^ r ≤ i ^ i * (2 * m) ^ r :=
    Nat.mul_le_mul hfac hn_pow
  have hleft_le' : i.factorial * n ^ r ≤ i ^ i * 2 ^ r * m ^ r := by
    calc
      i.factorial * n ^ r ≤ i ^ i * (2 * m) ^ r := hleft_le
      _ = i ^ i * (2 ^ r * m ^ r) := by rw [mul_pow]
      _ = i ^ i * 2 ^ r * m ^ r := by ring
  have h_i_exp : i ≤ 2 * d := by
    dsimp [d, r]
    omega
  have h_r_exp : r < 2 * d := by
    dsimp [d, r]
    omega
  have hprod_lt : i ^ i * 2 ^ r < i ^ (2 * d) * 2 ^ (2 * d) := by
    calc
      i ^ i * 2 ^ r ≤ i ^ (2 * d) * 2 ^ r :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hi_pos h_i_exp)
      _ < i ^ (2 * d) * 2 ^ (2 * d) :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) h_r_exp)
          (Nat.pow_pos (a := i) (n := 2 * d) hi_pos)
  have hbase_expand : i ^ (2 * d) * 2 ^ (2 * d) = (4 * i ^ 2) ^ d := by
    rw [mul_pow, show 4 = 2 ^ 2 by norm_num, pow_mul, pow_mul]
    ring
  have hmd : i ^ i * 2 ^ r < m ^ d := by
    calc
      i ^ i * 2 ^ r < i ^ (2 * d) * 2 ^ (2 * d) := hprod_lt
      _ = (4 * i ^ 2) ^ d := hbase_expand
      _ ≤ m ^ d := Nat.pow_le_pow_left hbase d
  calc
    i.factorial * n ^ (i / 2) = i.factorial * n ^ r := by rfl
    _ ≤ i ^ i * 2 ^ r * m ^ r := hleft_le'
    _ < m ^ d * m ^ r :=
      Nat.mul_lt_mul_of_pos_right hmd (Nat.pow_pos (a := m) (n := r) hm_pos)
    _ = m ^ (d + r) := by rw [← pow_add]
    _ = m ^ i := by
      congr 1
      dsimp [d, r]
      omega
    _ = (n - i + 1) ^ i := by rfl

theorem sylvester_schur_of_quadratic_large
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hm_large : 4 * i ^ 2 ≤ n - i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  exact sylvester_schur_of_half_prime_count_bound n i hi hi_half
    (factorial_mul_pow_half_lt_of_quadratic_large hi hi_half hm_large)

theorem sylvester_schur_of_large_n {n i : ℕ} (hi : 1 < i) (hi_half : i ≤ n / 2)
    (hlarge : i.factorial * 2 ^ (i - 1) < n - i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  let m := n - i + 1
  have hi_one : 1 ≤ i := by omega
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hn_le : n ≤ 2 * m := by
    dsimp [m]
    omega
  have hlarge' : i.factorial * n ^ (i - 1) < m ^ i := by
    calc
      i.factorial * n ^ (i - 1) ≤ i.factorial * (2 * m) ^ (i - 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn_le (i - 1))
      _ = (i.factorial * 2 ^ (i - 1)) * m ^ (i - 1) := by
        rw [mul_pow]
        ring
      _ < m * m ^ (i - 1) :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (a := m) (n := i - 1) hm_pos)
      _ = m ^ (i - 1 + 1) := by
        rw [pow_succ]
        ring
      _ = m ^ i := by
        rw [Nat.sub_add_cancel hi_one]
  exact sylvester_schur_of_prime_count_bound n i (i - 1) hi_one hi_half
    (primesBelow_succ_card_le_pred i) (by simpa [m] using hlarge')

lemma choose_inequality_of_large_start_with_prime_count_bound {m k r : ℕ}
    (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r) (hrk : r < k)
    (hlarge : k.factorial * 2 ^ r < m ^ (k - r)) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  have hm_pos : 0 < m := by omega
  have hN_le : m + k - 1 ≤ 2 * m := by omega
  have hlarge' : k.factorial * (m + k - 1) ^ r < m ^ k := by
    calc
      k.factorial * (m + k - 1) ^ r ≤ k.factorial * (2 * m) ^ r :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN_le r)
      _ = (k.factorial * 2 ^ r) * m ^ r := by
          rw [mul_pow]
          ring
      _ < m ^ (k - r) * m ^ r :=
        Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (a := m) (n := r) hm_pos)
      _ = m ^ k := by
        rw [← pow_add]
        congr 1
        omega
  exact choose_inequality_of_prime_count_bound (by omega) hm hr_count hlarge'

lemma choose_inequality_of_large_start {m k : ℕ} (hk : 1 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k - 1) < m) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  have hlarge' : k.factorial * 2 ^ (k - 1) < m ^ (k - (k - 1)) := by
    simpa [show k - (k - 1) = 1 by omega] using hlarge
  exact choose_inequality_of_large_start_with_prime_count_bound (m := m) (k := k) (r := k - 1)
    hm (primesBelow_succ_card_le_pred k) (by omega) hlarge'

theorem sylvester_schur_interval_of_large_start {m k : ℕ} (hk : 1 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k - 1) < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := k)
    (by omega) hm (choose_inequality_of_large_start hk hm hlarge)

theorem sylvester_schur_interval_of_large_start_with_prime_count_bound {m k r : ℕ}
    (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r) (hrk : r < k)
    (hlarge : k.factorial * 2 ^ r < m ^ (k - r)) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := k)
    (by omega) hm
    (choose_inequality_of_large_start_with_prime_count_bound hm hr_count hrk hlarge)

lemma choose_inequality_of_large_start_half_bound {m k : ℕ} (hk : 2 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k / 2 + 1) < m ^ (k - (k / 2 + 1))) :
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k := by
  exact choose_inequality_of_large_start_with_prime_count_bound (m := m) (k := k)
    (r := k / 2 + 1) hm (primesBelow_succ_card_le_half_add_one k) (by omega) hlarge

theorem sylvester_schur_interval_of_large_start_half_bound {m k : ℕ} (hk : 2 < k)
    (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k / 2 + 1) < m ^ (k - (k / 2 + 1))) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := k)
    (by omega) hm (choose_inequality_of_large_start_half_bound hk hm hlarge)

theorem sylvester_schur_interval_of_small_start
    (hsmall : SylvesterSchurSmallStart) : SylvesterSchurInterval := by
  intro m k hk hm
  by_cases hk_one : k = 1
  · subst hk_one
    exact sylvester_schur_interval_one (m := m) hm
  · have hk_gt_one : 1 < k := by omega
    by_cases hlarge : k.factorial * 2 ^ (k - 1) < m
    · exact sylvester_schur_interval_of_large_start hk_gt_one hm hlarge
    · exact hsmall hk_gt_one hm (Nat.le_of_not_gt hlarge)

lemma sylvester_schur_interval_five {m : ℕ} (hm : 5 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 5) ∧ p.Prime ∧ 5 < p ∧ p ∣ j := by
  by_cases hle : 12 ≤ m
  · have hineq0 : (12 + 5 - 1) ^ (5 + 1).primesBelow.card < Nat.choose (12 + 5 - 1) 5 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 5) (m₀ := 12) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 5)
      (by omega) hm hineq
  · have hlt : m < 12 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_le_five {m k : ℕ} (hk : 0 < k) (hk5 : k ≤ 5) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)

lemma sylvester_schur_interval_threshold_five :
    ∃ m₀ : ℕ, 5 < m₀ ∧
      (m₀ + 5 - 1) ^ (5 + 1).primesBelow.card < Nat.choose (m₀ + 5 - 1) 5 ∧
      ∀ m : ℕ, 5 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 5) ∧ p.Prime ∧ 5 < p ∧ p ∣ j := by
  refine ⟨12, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_five hm

lemma sylvester_schur_interval_threshold_le_five {k : ℕ} (hk : 0 < k) (hk5 : k ≤ 5) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_four (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_four (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_four (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_four (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_five

lemma sylvester_schur_interval_six {m : ℕ} (hm : 6 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 6) ∧ p.Prime ∧ 6 < p ∧ p ∣ j := by
  by_cases hle : 9 ≤ m
  · have hineq0 : (9 + 6 - 1) ^ (6 + 1).primesBelow.card < Nat.choose (9 + 6 - 1) 6 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 6) (m₀ := 9) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 6)
      (by omega) hm hineq
  · have hlt : m < 9 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨7, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_threshold_six :
    ∃ m₀ : ℕ, 6 < m₀ ∧
      (m₀ + 6 - 1) ^ (6 + 1).primesBelow.card < Nat.choose (m₀ + 6 - 1) 6 ∧
      ∀ m : ℕ, 6 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 6) ∧ p.Prime ∧ 6 < p ∧ p ∣ j := by
  refine ⟨9, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_six hm

lemma sylvester_schur_interval_le_six {m k : ℕ} (hk : 0 < k) (hk6 : k ≤ 6) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_six {k : ℕ} (hk : 0 < k) (hk6 : k ≤ 6) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_five (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_five (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_five (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_five (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_five (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_six

lemma sylvester_schur_interval_seven {m : ℕ} (hm : 7 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 7) ∧ p.Prime ∧ 7 < p ∧ p ∣ j := by
  by_cases hle : 18 ≤ m
  · have hineq0 : (18 + 7 - 1) ^ (7 + 1).primesBelow.card < Nat.choose (18 + 7 - 1) 7 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 7) (m₀ := 18) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 7)
      (by omega) hm hineq
  · have hlt : m < 18 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_threshold_seven :
    ∃ m₀ : ℕ, 7 < m₀ ∧
      (m₀ + 7 - 1) ^ (7 + 1).primesBelow.card < Nat.choose (m₀ + 7 - 1) 7 ∧
      ∀ m : ℕ, 7 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 7) ∧ p.Prime ∧ 7 < p ∧ p ∣ j := by
  refine ⟨18, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_seven hm

lemma sylvester_schur_interval_le_seven {m k : ℕ} (hk : 0 < k) (hk7 : k ≤ 7) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)
  · exact sylvester_schur_interval_seven (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_seven {k : ℕ} (hk : 0 < k) (hk7 : k ≤ 7) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_six (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_six (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_six (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_six (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_six (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_six (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_seven

lemma sylvester_schur_interval_eight {m : ℕ} (hm : 8 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 8) ∧ p.Prime ∧ 8 < p ∧ p ∣ j := by
  by_cases hle : 14 ≤ m
  · have hineq0 : (14 + 8 - 1) ^ (8 + 1).primesBelow.card < Nat.choose (14 + 8 - 1) 8 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 8) (m₀ := 14) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 8)
      (by omega) hm hineq
  · have hlt : m < 14 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_threshold_eight :
    ∃ m₀ : ℕ, 8 < m₀ ∧
      (m₀ + 8 - 1) ^ (8 + 1).primesBelow.card < Nat.choose (m₀ + 8 - 1) 8 ∧
      ∀ m : ℕ, 8 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 8) ∧ p.Prime ∧ 8 < p ∧ p ∣ j := by
  refine ⟨14, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_eight hm

lemma sylvester_schur_interval_le_eight {m k : ℕ} (hk : 0 < k) (hk8 : k ≤ 8) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)
  · exact sylvester_schur_interval_seven (m := m) (by omega)
  · exact sylvester_schur_interval_eight (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_eight {k : ℕ} (hk : 0 < k) (hk8 : k ≤ 8) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_seven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_eight

lemma sylvester_schur_interval_nine {m : ℕ} (hm : 9 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 9) ∧ p.Prime ∧ 9 < p ∧ p ∣ j := by
  by_cases hle : 12 ≤ m
  · have hineq0 : (12 + 9 - 1) ^ (9 + 1).primesBelow.card < Nat.choose (12 + 9 - 1) 9 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 9) (m₀ := 12) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 9)
      (by omega) hm hineq
  · have hlt : m < 12 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 11, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_threshold_nine :
    ∃ m₀ : ℕ, 9 < m₀ ∧
      (m₀ + 9 - 1) ^ (9 + 1).primesBelow.card < Nat.choose (m₀ + 9 - 1) 9 ∧
      ∀ m : ℕ, 9 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 9) ∧ p.Prime ∧ 9 < p ∧ p ∣ j := by
  refine ⟨12, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_nine hm

lemma sylvester_schur_interval_ten {m : ℕ} (hm : 10 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 10) ∧ p.Prime ∧ 10 < p ∧ p ∣ j := by
  have hineq0 : (11 + 10 - 1) ^ (10 + 1).primesBelow.card < Nat.choose (11 + 10 - 1) 10 := by
    decide
  have hineq := choose_inequality_of_ge_start (k := 10) (m₀ := 11) (m := m)
    (by omega) (by omega) (by omega) hineq0
  exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 10)
    (by omega) hm hineq

lemma sylvester_schur_interval_threshold_ten :
    ∃ m₀ : ℕ, 10 < m₀ ∧
      (m₀ + 10 - 1) ^ (10 + 1).primesBelow.card < Nat.choose (m₀ + 10 - 1) 10 ∧
      ∀ m : ℕ, 10 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 10) ∧ p.Prime ∧ 10 < p ∧ p ∣ j := by
  refine ⟨11, by omega, by decide, ?_⟩
  intro m hm hlt
  omega

lemma sylvester_schur_interval_le_ten {m k : ℕ} (hk : 0 < k) (hk10 : k ≤ 10) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)
  · exact sylvester_schur_interval_seven (m := m) (by omega)
  · exact sylvester_schur_interval_eight (m := m) (by omega)
  · exact sylvester_schur_interval_nine (m := m) (by omega)
  · exact sylvester_schur_interval_ten (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_ten {k : ℕ} (hk : 0 < k) (hk10 : k ≤ 10) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eight (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_nine
  · exact sylvester_schur_interval_threshold_ten

lemma sylvester_schur_interval_eleven {m : ℕ} (hm : 11 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 11) ∧ p.Prime ∧ 11 < p ∧ p ∣ j := by
  by_cases hle : 18 ≤ m
  · have hineq0 : (18 + 11 - 1) ^ (11 + 1).primesBelow.card < Nat.choose (18 + 11 - 1) 11 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 11) (m₀ := 18) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 11)
      (by omega) hm hineq
  · have hlt : m < 18 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_threshold_eleven :
    ∃ m₀ : ℕ, 11 < m₀ ∧
      (m₀ + 11 - 1) ^ (11 + 1).primesBelow.card < Nat.choose (m₀ + 11 - 1) 11 ∧
      ∀ m : ℕ, 11 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 11) ∧ p.Prime ∧ 11 < p ∧ p ∣ j := by
  refine ⟨18, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_eleven hm

lemma sylvester_schur_interval_le_eleven {m k : ℕ} (hk : 0 < k) (hk11 : k ≤ 11)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)
  · exact sylvester_schur_interval_seven (m := m) (by omega)
  · exact sylvester_schur_interval_eight (m := m) (by omega)
  · exact sylvester_schur_interval_nine (m := m) (by omega)
  · exact sylvester_schur_interval_ten (m := m) (by omega)
  · exact sylvester_schur_interval_eleven (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_eleven {k : ℕ} (hk : 0 < k) (hk11 : k ≤ 11) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_ten (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_eleven

lemma sylvester_schur_interval_twelve {m : ℕ} (hm : 12 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 12) ∧ p.Prime ∧ 12 < p ∧ p ∣ j := by
  by_cases hle : 16 ≤ m
  · have hineq0 : (16 + 12 - 1) ^ (12 + 1).primesBelow.card < Nat.choose (16 + 12 - 1) 12 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 12) (m₀ := 16) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 12)
      (by omega) hm hineq
  · have hlt : m < 16 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact ⟨13, 13, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨17, 17, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma sylvester_schur_interval_threshold_twelve :
    ∃ m₀ : ℕ, 12 < m₀ ∧
      (m₀ + 12 - 1) ^ (12 + 1).primesBelow.card < Nat.choose (m₀ + 12 - 1) 12 ∧
      ∀ m : ℕ, 12 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 12) ∧ p.Prime ∧ 12 < p ∧ p ∣ j := by
  refine ⟨16, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_twelve hm

lemma sylvester_schur_interval_le_twelve {m k : ℕ} (hk : 0 < k) (hk12 : k ≤ 12)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_one (m := m) (by omega)
  · exact sylvester_schur_interval_two (m := m) (by omega)
  · exact sylvester_schur_interval_three (m := m) (by omega)
  · exact sylvester_schur_interval_four (m := m) (by omega)
  · exact sylvester_schur_interval_five (m := m) (by omega)
  · exact sylvester_schur_interval_six (m := m) (by omega)
  · exact sylvester_schur_interval_seven (m := m) (by omega)
  · exact sylvester_schur_interval_eight (m := m) (by omega)
  · exact sylvester_schur_interval_nine (m := m) (by omega)
  · exact sylvester_schur_interval_ten (m := m) (by omega)
  · exact sylvester_schur_interval_eleven (m := m) (by omega)
  · exact sylvester_schur_interval_twelve (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_twelve {k : ℕ} (hk : 0 < k) (hk12 : k ≤ 12) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  interval_cases k
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_le_eleven (by omega) (by omega)
  · exact sylvester_schur_interval_threshold_twelve

lemma sylvester_schur_interval_prime_witness {m k p : ℕ}
    (hlo : m ≤ p) (hhi : p < m + k) (hp : p.Prime) (hkp : k < p) :
    ∃ j q : ℕ, j ∈ Set.Ico m (m + k) ∧ q.Prime ∧ k < q ∧ q ∣ j :=
  ⟨p, p, ⟨hlo, hhi⟩, hp, hkp, dvd_rfl⟩

lemma sylvester_schur_interval_thirteen {m : ℕ} (hm : 13 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 13) ∧ p.Prime ∧ 13 < p ∧ p ∣ j := by
  by_cases hle : 24 ≤ m
  · have hineq0 : (24 + 13 - 1) ^ (13 + 1).primesBelow.card < Nat.choose (24 + 13 - 1) 13 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 13) (m₀ := 24) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 13)
      (by omega) hm hineq
  · have hlt : m < 24 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_thirteen :
    ∃ m₀ : ℕ, 13 < m₀ ∧
      (m₀ + 13 - 1) ^ (13 + 1).primesBelow.card < Nat.choose (m₀ + 13 - 1) 13 ∧
      ∀ m : ℕ, 13 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 13) ∧ p.Prime ∧ 13 < p ∧ p ∣ j := by
  refine ⟨24, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_thirteen hm

lemma sylvester_schur_interval_fourteen {m : ℕ} (hm : 14 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 14) ∧ p.Prime ∧ 14 < p ∧ p ∣ j := by
  by_cases hle : 22 ≤ m
  · have hineq0 : (22 + 14 - 1) ^ (14 + 1).primesBelow.card < Nat.choose (22 + 14 - 1) 14 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 14) (m₀ := 22) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 14)
      (by omega) hm hineq
  · have hlt : m < 22 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_fourteen :
    ∃ m₀ : ℕ, 14 < m₀ ∧
      (m₀ + 14 - 1) ^ (14 + 1).primesBelow.card < Nat.choose (m₀ + 14 - 1) 14 ∧
      ∀ m : ℕ, 14 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 14) ∧ p.Prime ∧ 14 < p ∧ p ∣ j := by
  refine ⟨22, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_fourteen hm

lemma sylvester_schur_interval_fifteen {m : ℕ} (hm : 15 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 15) ∧ p.Prime ∧ 15 < p ∧ p ∣ j := by
  by_cases hle : 20 ≤ m
  · have hineq0 : (20 + 15 - 1) ^ (15 + 1).primesBelow.card < Nat.choose (20 + 15 - 1) 15 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 15) (m₀ := 20) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 15)
      (by omega) hm hineq
  · have hlt : m < 20 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_fifteen :
    ∃ m₀ : ℕ, 15 < m₀ ∧
      (m₀ + 15 - 1) ^ (15 + 1).primesBelow.card < Nat.choose (m₀ + 15 - 1) 15 ∧
      ∀ m : ℕ, 15 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 15) ∧ p.Prime ∧ 15 < p ∧ p ∣ j := by
  refine ⟨20, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_fifteen hm

lemma sylvester_schur_interval_sixteen {m : ℕ} (hm : 16 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 16) ∧ p.Prime ∧ 16 < p ∧ p ∣ j := by
  by_cases hle : 19 ≤ m
  · have hineq0 : (19 + 16 - 1) ^ (16 + 1).primesBelow.card < Nat.choose (19 + 16 - 1) 16 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 16) (m₀ := 19) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 16)
      (by omega) hm hineq
  · have hlt : m < 19 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_sixteen :
    ∃ m₀ : ℕ, 16 < m₀ ∧
      (m₀ + 16 - 1) ^ (16 + 1).primesBelow.card < Nat.choose (m₀ + 16 - 1) 16 ∧
      ∀ m : ℕ, 16 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 16) ∧ p.Prime ∧ 16 < p ∧ p ∣ j := by
  refine ⟨19, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_sixteen hm

lemma sylvester_schur_interval_le_sixteen {m k : ℕ} (hk : 0 < k) (hk16 : k ≤ 16)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk12 : k ≤ 12
  · exact sylvester_schur_interval_le_twelve hk hk12 hm
  · interval_cases k
    · exact sylvester_schur_interval_thirteen (m := m) (by omega)
    · exact sylvester_schur_interval_fourteen (m := m) (by omega)
    · exact sylvester_schur_interval_fifteen (m := m) (by omega)
    · exact sylvester_schur_interval_sixteen (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_sixteen {k : ℕ} (hk : 0 < k) (hk16 : k ≤ 16) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk12 : k ≤ 12
  · exact sylvester_schur_interval_threshold_le_twelve hk hk12
  · interval_cases k
    · exact sylvester_schur_interval_threshold_thirteen
    · exact sylvester_schur_interval_threshold_fourteen
    · exact sylvester_schur_interval_threshold_fifteen
    · exact sylvester_schur_interval_threshold_sixteen

lemma sylvester_schur_interval_seventeen {m : ℕ} (hm : 17 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 17) ∧ p.Prime ∧ 17 < p ∧ p ∣ j := by
  by_cases hle : 26 ≤ m
  · have hineq0 : (26 + 17 - 1) ^ (17 + 1).primesBelow.card < Nat.choose (26 + 17 - 1) 17 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 17) (m₀ := 26) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 17)
      (by omega) hm hineq
  · have hlt : m < 26 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_seventeen :
    ∃ m₀ : ℕ, 17 < m₀ ∧
      (m₀ + 17 - 1) ^ (17 + 1).primesBelow.card < Nat.choose (m₀ + 17 - 1) 17 ∧
      ∀ m : ℕ, 17 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 17) ∧ p.Prime ∧ 17 < p ∧ p ∣ j := by
  refine ⟨26, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_seventeen hm

lemma sylvester_schur_interval_eighteen {m : ℕ} (hm : 18 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 18) ∧ p.Prime ∧ 18 < p ∧ p ∣ j := by
  by_cases hle : 24 ≤ m
  · have hineq0 : (24 + 18 - 1) ^ (18 + 1).primesBelow.card < Nat.choose (24 + 18 - 1) 18 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 18) (m₀ := 24) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 18)
      (by omega) hm hineq
  · have hlt : m < 24 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_eighteen :
    ∃ m₀ : ℕ, 18 < m₀ ∧
      (m₀ + 18 - 1) ^ (18 + 1).primesBelow.card < Nat.choose (m₀ + 18 - 1) 18 ∧
      ∀ m : ℕ, 18 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 18) ∧ p.Prime ∧ 18 < p ∧ p ∣ j := by
  refine ⟨24, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_eighteen hm

lemma sylvester_schur_interval_nineteen {m : ℕ} (hm : 19 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 19) ∧ p.Prime ∧ 19 < p ∧ p ∣ j := by
  by_cases hle : 33 ≤ m
  · have hineq0 : (33 + 19 - 1) ^ (19 + 1).primesBelow.card < Nat.choose (33 + 19 - 1) 19 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 19) (m₀ := 33) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 19)
      (by omega) hm hineq
  · have hlt : m < 33 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_nineteen :
    ∃ m₀ : ℕ, 19 < m₀ ∧
      (m₀ + 19 - 1) ^ (19 + 1).primesBelow.card < Nat.choose (m₀ + 19 - 1) 19 ∧
      ∀ m : ℕ, 19 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 19) ∧ p.Prime ∧ 19 < p ∧ p ∣ j := by
  refine ⟨33, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_nineteen hm

lemma sylvester_schur_interval_twenty {m : ℕ} (hm : 20 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 20) ∧ p.Prime ∧ 20 < p ∧ p ∣ j := by
  by_cases hle : 31 ≤ m
  · have hineq0 : (31 + 20 - 1) ^ (20 + 1).primesBelow.card < Nat.choose (31 + 20 - 1) 20 := by
      decide
    have hineq := choose_inequality_of_ge_start (k := 20) (m₀ := 31) (m := m)
      (by omega) (by omega) hle hineq0
    exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 20)
      (by omega) hm hineq
  · have hlt : m < 31 := Nat.lt_of_not_ge hle
    interval_cases m
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma sylvester_schur_interval_threshold_twenty :
    ∃ m₀ : ℕ, 20 < m₀ ∧
      (m₀ + 20 - 1) ^ (20 + 1).primesBelow.card < Nat.choose (m₀ + 20 - 1) 20 ∧
      ∀ m : ℕ, 20 < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + 20) ∧ p.Prime ∧ 20 < p ∧ p ∣ j := by
  refine ⟨31, by omega, by decide, ?_⟩
  intro m hm hlt
  exact sylvester_schur_interval_twenty hm

lemma sylvester_schur_interval_le_twenty {m k : ℕ} (hk : 0 < k) (hk20 : k ≤ 20)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk16 : k ≤ 16
  · exact sylvester_schur_interval_le_sixteen hk hk16 hm
  · interval_cases k
    · exact sylvester_schur_interval_seventeen (m := m) (by omega)
    · exact sylvester_schur_interval_eighteen (m := m) (by omega)
    · exact sylvester_schur_interval_nineteen (m := m) (by omega)
    · exact sylvester_schur_interval_twenty (m := m) (by omega)

lemma sylvester_schur_interval_threshold_le_twenty {k : ℕ} (hk : 0 < k) (hk20 : k ≤ 20) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk16 : k ≤ 16
  · exact sylvester_schur_interval_threshold_le_sixteen hk hk16
  · interval_cases k
    · exact sylvester_schur_interval_threshold_seventeen
    · exact sylvester_schur_interval_threshold_eighteen
    · exact sylvester_schur_interval_threshold_nineteen
    · exact sylvester_schur_interval_threshold_twenty

lemma sylvester_schur_interval_le_forty_eight {m k : ℕ} (hk : 0 < k) (hk48 : k ≤ 48)
    (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j := by
  by_cases hk20 : k ≤ 20
  · exact sylvester_schur_interval_le_twenty hk hk20 hm
  · interval_cases k
    · by_cases hle : 29 ≤ m
      · have hineq0 : (29 + 21 - 1) ^ (21 + 1).primesBelow.card < Nat.choose (29 + 21 - 1) 21 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 21) (m₀ := 29) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 21)
          (by omega) hm hineq
      · have hlt : m < 29 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 28 ≤ m
      · have hineq0 : (28 + 22 - 1) ^ (22 + 1).primesBelow.card < Nat.choose (28 + 22 - 1) 22 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 22) (m₀ := 28) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 22)
          (by omega) hm hineq
      · have hlt : m < 28 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 23) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 36 ≤ m
      · have hineq0 : (36 + 23 - 1) ^ (23 + 1).primesBelow.card < Nat.choose (36 + 23 - 1) 23 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 23) (m₀ := 36) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 23)
          (by omega) hm hineq
      · have hlt : m < 36 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 34 ≤ m
      · have hineq0 : (34 + 24 - 1) ^ (24 + 1).primesBelow.card < Nat.choose (34 + 24 - 1) 24 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 24) (m₀ := 34) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 24)
          (by omega) hm hineq
      · have hlt : m < 34 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 32 ≤ m
      · have hineq0 : (32 + 25 - 1) ^ (25 + 1).primesBelow.card < Nat.choose (32 + 25 - 1) 25 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 25) (m₀ := 32) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 25)
          (by omega) hm hineq
      · have hlt : m < 32 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 31 ≤ m
      · have hineq0 : (31 + 26 - 1) ^ (26 + 1).primesBelow.card < Nat.choose (31 + 26 - 1) 26 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 26) (m₀ := 31) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 26)
          (by omega) hm hineq
      · have hlt : m < 31 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 30 ≤ m
      · have hineq0 : (30 + 27 - 1) ^ (27 + 1).primesBelow.card < Nat.choose (30 + 27 - 1) 27 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 27) (m₀ := 30) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 27)
          (by omega) hm hineq
      · have hlt : m < 30 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 29) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 29 ≤ m
      · have hineq0 : (29 + 28 - 1) ^ (28 + 1).primesBelow.card < Nat.choose (29 + 28 - 1) 28 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 28) (m₀ := 29) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 28)
          (by omega) hm hineq
      · have hlt : m < 29 := Nat.lt_of_not_ge hle
        omega
    · by_cases hle : 36 ≤ m
      · have hineq0 : (36 + 29 - 1) ^ (29 + 1).primesBelow.card < Nat.choose (36 + 29 - 1) 29 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 29) (m₀ := 36) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 29)
          (by omega) hm hineq
      · have hlt : m < 36 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 35 ≤ m
      · have hineq0 : (35 + 30 - 1) ^ (30 + 1).primesBelow.card < Nat.choose (35 + 30 - 1) 30 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 30) (m₀ := 35) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 30)
          (by omega) hm hineq
      · have hlt : m < 35 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 31) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 43 ≤ m
      · have hineq0 : (43 + 31 - 1) ^ (31 + 1).primesBelow.card < Nat.choose (43 + 31 - 1) 31 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 31) (m₀ := 43) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 31)
          (by omega) hm hineq
      · have hlt : m < 43 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 41 ≤ m
      · have hineq0 : (41 + 32 - 1) ^ (32 + 1).primesBelow.card < Nat.choose (41 + 32 - 1) 32 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 32) (m₀ := 41) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 32)
          (by omega) hm hineq
      · have hlt : m < 41 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 40 ≤ m
      · have hineq0 : (40 + 33 - 1) ^ (33 + 1).primesBelow.card < Nat.choose (40 + 33 - 1) 33 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 33) (m₀ := 40) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 33)
          (by omega) hm hineq
      · have hlt : m < 40 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 39 ≤ m
      · have hineq0 : (39 + 34 - 1) ^ (34 + 1).primesBelow.card < Nat.choose (39 + 34 - 1) 34 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 34) (m₀ := 39) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 34)
          (by omega) hm hineq
      · have hlt : m < 39 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 38 ≤ m
      · have hineq0 : (38 + 35 - 1) ^ (35 + 1).primesBelow.card < Nat.choose (38 + 35 - 1) 35 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 35) (m₀ := 38) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 35)
          (by omega) hm hineq
      · have hlt : m < 38 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 37) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 37 ≤ m
      · have hineq0 : (37 + 36 - 1) ^ (36 + 1).primesBelow.card < Nat.choose (37 + 36 - 1) 36 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 36) (m₀ := 37) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 36)
          (by omega) hm hineq
      · have hlt : m < 37 := Nat.lt_of_not_ge hle
        omega
    · by_cases hle : 44 ≤ m
      · have hineq0 : (44 + 37 - 1) ^ (37 + 1).primesBelow.card < Nat.choose (44 + 37 - 1) 37 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 37) (m₀ := 44) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 37)
          (by omega) hm hineq
      · have hlt : m < 44 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 43 ≤ m
      · have hineq0 : (43 + 38 - 1) ^ (38 + 1).primesBelow.card < Nat.choose (43 + 38 - 1) 38 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 38) (m₀ := 43) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 38)
          (by omega) hm hineq
      · have hlt : m < 43 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 42 ≤ m
      · have hineq0 : (42 + 39 - 1) ^ (39 + 1).primesBelow.card < Nat.choose (42 + 39 - 1) 39 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 39) (m₀ := 42) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 39)
          (by omega) hm hineq
      · have hlt : m < 42 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 41 ≤ m
      · have hineq0 : (41 + 40 - 1) ^ (40 + 1).primesBelow.card < Nat.choose (41 + 40 - 1) 40 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 40) (m₀ := 41) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 40)
          (by omega) hm hineq
      · have hlt : m < 41 := Nat.lt_of_not_ge hle
        omega
    · by_cases hle : 48 ≤ m
      · have hineq0 : (48 + 41 - 1) ^ (41 + 1).primesBelow.card < Nat.choose (48 + 41 - 1) 41 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 41) (m₀ := 48) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 41)
          (by omega) hm hineq
      · have hlt : m < 48 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 47 ≤ m
      · have hineq0 : (47 + 42 - 1) ^ (42 + 1).primesBelow.card < Nat.choose (47 + 42 - 1) 42 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 42) (m₀ := 47) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 42)
          (by omega) hm hineq
      · have hlt : m < 47 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 43) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 55 ≤ m
      · have hineq0 : (55 + 43 - 1) ^ (43 + 1).primesBelow.card < Nat.choose (55 + 43 - 1) 43 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 43) (m₀ := 55) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 43)
          (by omega) hm hineq
      · have hlt : m < 55 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 54 ≤ m
      · have hineq0 : (54 + 44 - 1) ^ (44 + 1).primesBelow.card < Nat.choose (54 + 44 - 1) 44 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 44) (m₀ := 54) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 44)
          (by omega) hm hineq
      · have hlt : m < 54 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 53 ≤ m
      · have hineq0 : (53 + 45 - 1) ^ (45 + 1).primesBelow.card < Nat.choose (53 + 45 - 1) 45 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 45) (m₀ := 53) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 45)
          (by omega) hm hineq
      · have hlt : m < 53 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 51 ≤ m
      · have hineq0 : (51 + 46 - 1) ^ (46 + 1).primesBelow.card < Nat.choose (51 + 46 - 1) 46 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 46) (m₀ := 51) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 46)
          (by omega) hm hineq
      · have hlt : m < 51 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 47) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 60 ≤ m
      · have hineq0 : (60 + 47 - 1) ^ (47 + 1).primesBelow.card < Nat.choose (60 + 47 - 1) 47 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 47) (m₀ := 60) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 47)
          (by omega) hm hineq
      · have hlt : m < 60 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · by_cases hle : 58 ≤ m
      · have hineq0 : (58 + 48 - 1) ^ (48 + 1).primesBelow.card < Nat.choose (58 + 48 - 1) 48 := by
          decide
        have hineq := choose_inequality_of_ge_start (k := 48) (m₀ := 58) (m := m)
          (by omega) (by omega) hle hineq0
        exact exists_large_prime_factor_of_choose_gt_pow_prime_count (m := m) (k := 48)
          (by omega) hm hineq
      · have hlt : m < 58 := Nat.lt_of_not_ge hle
        interval_cases m
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 53) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        · exact sylvester_schur_interval_prime_witness (p := 59) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem sylvester_schur_interval_of_threshold
    (hbase : SylvesterSchurIntervalThreshold) :
    SylvesterSchurInterval := by
  intro m k hk hm
  obtain ⟨m₀, hm₀, hineq₀, hbelow⟩ := hbase k hk
  by_cases hle : m₀ ≤ m
  · exact exists_large_prime_factor_of_choose_gt_pow_prime_count hk hm
      (choose_inequality_of_ge_start hk hm₀ hle hineq₀)
  · exact hbelow m hm (Nat.lt_of_not_ge hle)

lemma prime_dvd_choose_of_dvd_mem_interval
    {n i p j : ℕ} (hi_le_n : i ≤ n) (hp : p.Prime) (hip : i < p)
    (hj : j ∈ Set.Ico (n - i + 1) (n + 1)) (hpj : p ∣ j) :
    p ∣ Nat.choose n i := by
  have htop : n - i + 1 + i = n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun t => t + 1) (Nat.sub_add_cancel hi_le_n)
  have hj_dvd : j ∣ (n - i + 1).ascFactorial i := by
    have hhi : j < n - i + 1 + i := by simpa [htop] using hj.2
    exact dvd_ascFactorial_of_mem hj.1 hhi
  have hchoose :
      (n - i + 1).ascFactorial i = i.factorial * Nat.choose n i := by
    simpa [Nat.sub_add_cancel hi_le_n] using
      (Nat.ascFactorial_eq_factorial_mul_choose (n - i) i)
  have hp_dvd_mul : p ∣ i.factorial * Nat.choose n i := by
    exact hpj.trans (hchoose ▸ hj_dvd)
  exact (hp.dvd_mul.mp hp_dvd_mul).resolve_left
    (prime_not_dvd_factorial_of_lt hp hip)

theorem sylvester_schur_of_interval
    (hSS : SylvesterSchurInterval)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_pos : 0 < i := hi
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hm : i < n - i + 1 := by omega
  obtain ⟨j, p, hj, hp, hip, hpj⟩ := hSS hi_pos hm
  have htop : n - i + 1 + i = n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun t => t + 1) (Nat.sub_add_cancel hi_le_n)
  have hj' : j ∈ Set.Ico (n - i + 1) (n + 1) := by
    simpa [htop] using hj
  exact ⟨p, hp, hip, prime_dvd_choose_of_dvd_mem_interval hi_le_n hp hip hj' hpj⟩

theorem sylvester_schur_of_index_le_twenty
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) (hi20 : i ≤ 20) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_pos : 0 < i := hi
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hm : i < n - i + 1 := by omega
  obtain ⟨j, p, hj, hp, hip, hpj⟩ :=
    sylvester_schur_interval_le_twenty hi_pos hi20 hm
  have htop : n - i + 1 + i = n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun t => t + 1) (Nat.sub_add_cancel hi_le_n)
  have hj' : j ∈ Set.Ico (n - i + 1) (n + 1) := by
    simpa [htop] using hj
  exact ⟨p, hp, hip, prime_dvd_choose_of_dvd_mem_interval hi_le_n hp hip hj' hpj⟩

theorem sylvester_schur_of_index_le_forty_eight
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) (hi48 : i ≤ 48) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  have hi_pos : 0 < i := hi
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hm : i < n - i + 1 := by omega
  obtain ⟨j, p, hj, hp, hip, hpj⟩ :=
    sylvester_schur_interval_le_forty_eight hi_pos hi48 hm
  have htop : n - i + 1 + i = n + 1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun t => t + 1) (Nat.sub_add_cancel hi_le_n)
  have hj' : j ∈ Set.Ico (n - i + 1) (n + 1) := by
    simpa [htop] using hj
  exact ⟨p, hp, hip, prime_dvd_choose_of_dvd_mem_interval hi_le_n hp hip hj' hpj⟩

theorem sylvester_schur_of_prime_in_top_interval
    (n i : ℕ) (hi_half : i ≤ n / 2)
    (hprime : ∃ p : ℕ, p.Prime ∧ n - i < p ∧ p ≤ n) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  obtain ⟨p, hp, hnp, hpn⟩ := hprime
  have hi_le_n : i ≤ n := le_trans hi_half (Nat.div_le_self n 2)
  have hip : i < p := by omega
  have hp_mem : p ∈ Set.Ico (n - i + 1) (n + 1) := by
    constructor <;> omega
  exact ⟨p, hp, hip, prime_dvd_choose_of_dvd_mem_interval hi_le_n hp hip hp_mem dvd_rfl⟩

theorem sylvester_schur_of_twice
    (n i : ℕ) (hi : 1 ≤ i) (hn : n = 2 * i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  obtain ⟨p, hp, hip, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul i (by omega)
  exact sylvester_schur_of_prime_in_top_interval n i (by omega)
    ⟨p, hp, by omega, by omega⟩

theorem sylvester_schur_of_twice_add_one
    (n i : ℕ) (hi : 1 ≤ i) (hn : n = 2 * i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (i + 1) (by omega)
  have hip : i < p := by omega
  have hp_ne_top : p ≠ 2 * (i + 1) := by
    intro htop
    have hp_ne_two : p ≠ 2 := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
    have hp_even : Even p := by
      rw [htop]
      exact even_two_mul (i + 1)
    exact (Nat.not_even_iff_odd.mpr hp_odd) hp_even
  have hp_le_n : p ≤ n := by omega
  exact sylvester_schur_of_prime_in_top_interval n i (by omega)
    ⟨p, hp, by omega, hp_le_n⟩

/-- A finite prime-gap certificate for the small residual range. -/
lemma exists_prime_sub_49_le_of_le_600 (n : ℕ) (hlo : 98 ≤ n) (hhi : n ≤ 600) :
    ∃ p : ℕ, p.Prime ∧ n - 49 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 145
  · exact ⟨97, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 187
  · exact ⟨139, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 229
  · exact ⟨181, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 277
  · exact ⟨229, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 325
  · exact ⟨277, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 365
  · exact ⟨317, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 407
  · exact ⟨359, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 449
  · exact ⟨401, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 497
  · exact ⟨449, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 539
  · exact ⟨491, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 571
  · exact ⟨523, by norm_num, by omega, by omega⟩
  · exact ⟨571, by norm_num, by omega, by omega⟩

-- Prime-gap certificates, chunked to keep proof search local.
set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_0 (n : ℕ) (hlo : 144 ≤ n) (hhi : n ≤ 2500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 210
  · exact ⟨139, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 282
  · exact ⟨211, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 354
  · exact ⟨283, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 424
  · exact ⟨353, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 492
  · exact ⟨421, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 562
  · exact ⟨491, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 634
  · exact ⟨563, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 702
  · exact ⟨631, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 772
  · exact ⟨701, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 844
  · exact ⟨773, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 910
  · exact ⟨839, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 982
  · exact ⟨911, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 1054
  · exact ⟨983, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 1122
  · exact ⟨1051, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 1194
  · exact ⟨1123, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 1264
  · exact ⟨1193, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 1330
  · exact ⟨1259, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 1398
  · exact ⟨1327, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 1470
  · exact ⟨1399, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 1542
  · exact ⟨1471, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 1614
  · exact ⟨1543, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 1684
  · exact ⟨1613, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 1740
  · exact ⟨1669, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 1812
  · exact ⟨1741, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 1882
  · exact ⟨1811, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 1950
  · exact ⟨1879, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 2022
  · exact ⟨1951, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 2088
  · exact ⟨2017, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 2160
  · exact ⟨2089, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 2232
  · exact ⟨2161, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 2292
  · exact ⟨2221, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 2364
  · exact ⟨2293, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 2428
  · exact ⟨2357, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 2494
  · exact ⟨2423, by norm_num, by omega, by omega⟩
  · exact ⟨2477, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_1 (n : ℕ) (hlo : 2501 ≤ n) (hhi : n ≤ 5000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 2548
  · exact ⟨2477, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 2620
  · exact ⟨2549, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 2692
  · exact ⟨2621, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 2764
  · exact ⟨2693, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 2824
  · exact ⟨2753, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 2890
  · exact ⟨2819, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 2958
  · exact ⟨2887, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 3028
  · exact ⟨2957, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 3094
  · exact ⟨3023, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 3160
  · exact ⟨3089, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 3208
  · exact ⟨3137, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 3280
  · exact ⟨3209, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 3342
  · exact ⟨3271, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 3414
  · exact ⟨3343, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 3484
  · exact ⟨3413, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 3540
  · exact ⟨3469, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 3612
  · exact ⟨3541, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 3684
  · exact ⟨3613, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 3748
  · exact ⟨3677, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 3810
  · exact ⟨3739, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 3874
  · exact ⟨3803, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 3934
  · exact ⟨3863, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 4002
  · exact ⟨3931, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 4074
  · exact ⟨4003, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 4144
  · exact ⟨4073, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 4210
  · exact ⟨4139, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 4282
  · exact ⟨4211, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 4354
  · exact ⟨4283, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 4420
  · exact ⟨4349, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 4492
  · exact ⟨4421, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 4564
  · exact ⟨4493, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 4632
  · exact ⟨4561, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 4692
  · exact ⟨4621, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 4762
  · exact ⟨4691, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 4830
  · exact ⟨4759, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 4902
  · exact ⟨4831, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 4974
  · exact ⟨4903, by norm_num, by omega, by omega⟩
  · exact ⟨4973, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_2 (n : ℕ) (hlo : 5001 ≤ n) (hhi : n ≤ 7500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 5070
  · exact ⟨4999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 5130
  · exact ⟨5059, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 5190
  · exact ⟨5119, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 5260
  · exact ⟨5189, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 5332
  · exact ⟨5261, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 5404
  · exact ⟨5333, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 5470
  · exact ⟨5399, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 5542
  · exact ⟨5471, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 5602
  · exact ⟨5531, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 5662
  · exact ⟨5591, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 5730
  · exact ⟨5659, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 5788
  · exact ⟨5717, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 5854
  · exact ⟨5783, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 5922
  · exact ⟨5851, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 5994
  · exact ⟨5923, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 6058
  · exact ⟨5987, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 6124
  · exact ⟨6053, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 6192
  · exact ⟨6121, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 6244
  · exact ⟨6173, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 6300
  · exact ⟨6229, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 6372
  · exact ⟨6301, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 6444
  · exact ⟨6373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 6498
  · exact ⟨6427, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 6562
  · exact ⟨6491, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 6634
  · exact ⟨6563, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 6690
  · exact ⟨6619, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 6762
  · exact ⟨6691, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 6834
  · exact ⟨6763, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 6904
  · exact ⟨6833, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 6970
  · exact ⟨6899, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 7042
  · exact ⟨6971, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 7114
  · exact ⟨7043, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 7180
  · exact ⟨7109, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 7248
  · exact ⟨7177, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 7318
  · exact ⟨7247, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 7380
  · exact ⟨7309, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 7440
  · exact ⟨7369, by norm_num, by omega, by omega⟩
  · exact ⟨7433, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_3 (n : ℕ) (hlo : 7501 ≤ n) (hhi : n ≤ 10000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 7570
  · exact ⟨7499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 7632
  · exact ⟨7561, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 7692
  · exact ⟨7621, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 7762
  · exact ⟨7691, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 7830
  · exact ⟨7759, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 7900
  · exact ⟨7829, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 7972
  · exact ⟨7901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 8034
  · exact ⟨7963, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 8088
  · exact ⟨8017, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 8160
  · exact ⟨8089, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 8232
  · exact ⟨8161, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 8304
  · exact ⟨8233, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 8368
  · exact ⟨8297, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 8440
  · exact ⟨8369, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 8502
  · exact ⟨8431, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 8572
  · exact ⟨8501, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 8644
  · exact ⟨8573, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 8712
  · exact ⟨8641, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 8784
  · exact ⟨8713, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 8854
  · exact ⟨8783, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 8920
  · exact ⟨8849, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 8964
  · exact ⟨8893, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 9034
  · exact ⟨8963, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 9100
  · exact ⟨9029, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 9162
  · exact ⟨9091, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 9232
  · exact ⟨9161, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 9298
  · exact ⟨9227, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 9364
  · exact ⟨9293, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 9420
  · exact ⟨9349, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 9492
  · exact ⟨9421, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 9562
  · exact ⟨9491, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 9622
  · exact ⟨9551, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 9694
  · exact ⟨9623, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 9760
  · exact ⟨9689, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 9820
  · exact ⟨9749, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 9888
  · exact ⟨9817, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 9958
  · exact ⟨9887, by norm_num, by omega, by omega⟩
  · exact ⟨9949, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_4 (n : ℕ) (hlo : 10001 ≤ n) (hhi : n ≤ 12500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 10044
  · exact ⟨9973, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 10110
  · exact ⟨10039, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 10182
  · exact ⟨10111, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 10252
  · exact ⟨10181, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 10324
  · exact ⟨10253, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 10392
  · exact ⟨10321, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 10462
  · exact ⟨10391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 10534
  · exact ⟨10463, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 10602
  · exact ⟨10531, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 10672
  · exact ⟨10601, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 10738
  · exact ⟨10667, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 10810
  · exact ⟨10739, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 10870
  · exact ⟨10799, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 10938
  · exact ⟨10867, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 11010
  · exact ⟨10939, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 11074
  · exact ⟨11003, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 11142
  · exact ⟨11071, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 11202
  · exact ⟨11131, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 11268
  · exact ⟨11197, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 11332
  · exact ⟨11261, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 11400
  · exact ⟨11329, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 11470
  · exact ⟨11399, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 11542
  · exact ⟨11471, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 11598
  · exact ⟨11527, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 11668
  · exact ⟨11597, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 11728
  · exact ⟨11657, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 11790
  · exact ⟨11719, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 11860
  · exact ⟨11789, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 11910
  · exact ⟨11839, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 11980
  · exact ⟨11909, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 12052
  · exact ⟨11981, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 12120
  · exact ⟨12049, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 12190
  · exact ⟨12119, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 12234
  · exact ⟨12163, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 12298
  · exact ⟨12227, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 12360
  · exact ⟨12289, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 12418
  · exact ⟨12347, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 12484
  · exact ⟨12413, by norm_num, by omega, by omega⟩
  · exact ⟨12479, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_5 (n : ℕ) (hlo : 12501 ≤ n) (hhi : n ≤ 15000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 12568
  · exact ⟨12497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 12640
  · exact ⟨12569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 12712
  · exact ⟨12641, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 12784
  · exact ⟨12713, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 12852
  · exact ⟨12781, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 12924
  · exact ⟨12853, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 12994
  · exact ⟨12923, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 13054
  · exact ⟨12983, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 13120
  · exact ⟨13049, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 13192
  · exact ⟨13121, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 13258
  · exact ⟨13187, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 13330
  · exact ⟨13259, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 13402
  · exact ⟨13331, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 13470
  · exact ⟨13399, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 13540
  · exact ⟨13469, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 13608
  · exact ⟨13537, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 13668
  · exact ⟨13597, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 13740
  · exact ⟨13669, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 13800
  · exact ⟨13729, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 13870
  · exact ⟨13799, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 13930
  · exact ⟨13859, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 14002
  · exact ⟨13931, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 14070
  · exact ⟨13999, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 14142
  · exact ⟨14071, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 14214
  · exact ⟨14143, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 14278
  · exact ⟨14207, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 14322
  · exact ⟨14251, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 14394
  · exact ⟨14323, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 14460
  · exact ⟨14389, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 14532
  · exact ⟨14461, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 14604
  · exact ⟨14533, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 14664
  · exact ⟨14593, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 14728
  · exact ⟨14657, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 14794
  · exact ⟨14723, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 14854
  · exact ⟨14783, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 14922
  · exact ⟨14851, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 14994
  · exact ⟨14923, by norm_num, by omega, by omega⟩
  · exact ⟨14983, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_6 (n : ℕ) (hlo : 15001 ≤ n) (hhi : n ≤ 17500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 15054
  · exact ⟨14983, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 15124
  · exact ⟨15053, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 15192
  · exact ⟨15121, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 15264
  · exact ⟨15193, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 15334
  · exact ⟨15263, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 15402
  · exact ⟨15331, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 15472
  · exact ⟨15401, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 15544
  · exact ⟨15473, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 15612
  · exact ⟨15541, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 15678
  · exact ⟨15607, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 15750
  · exact ⟨15679, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 15820
  · exact ⟨15749, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 15888
  · exact ⟨15817, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 15960
  · exact ⟨15889, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 16030
  · exact ⟨15959, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 16078
  · exact ⟨16007, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 16144
  · exact ⟨16073, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 16212
  · exact ⟨16141, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 16264
  · exact ⟨16193, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 16324
  · exact ⟨16253, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 16390
  · exact ⟨16319, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 16452
  · exact ⟨16381, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 16524
  · exact ⟨16453, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 16590
  · exact ⟨16519, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 16644
  · exact ⟨16573, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 16704
  · exact ⟨16633, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 16774
  · exact ⟨16703, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 16834
  · exact ⟨16763, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 16902
  · exact ⟨16831, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 16974
  · exact ⟨16903, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 17034
  · exact ⟨16963, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 17104
  · exact ⟨17033, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 17170
  · exact ⟨17099, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 17238
  · exact ⟨17167, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 17310
  · exact ⟨17239, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 17370
  · exact ⟨17299, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 17430
  · exact ⟨17359, by norm_num, by omega, by omega⟩
  · exact ⟨17431, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_7 (n : ℕ) (hlo : 17501 ≤ n) (hhi : n ≤ 20000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 17568
  · exact ⟨17497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 17640
  · exact ⟨17569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 17698
  · exact ⟨17627, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 17754
  · exact ⟨17683, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 17820
  · exact ⟨17749, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 17878
  · exact ⟨17807, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 17934
  · exact ⟨17863, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 18000
  · exact ⟨17929, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 18060
  · exact ⟨17989, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 18132
  · exact ⟨18061, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 18204
  · exact ⟨18133, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 18270
  · exact ⟨18199, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 18340
  · exact ⟨18269, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 18412
  · exact ⟨18341, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 18484
  · exact ⟨18413, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 18552
  · exact ⟨18481, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 18624
  · exact ⟨18553, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 18688
  · exact ⟨18617, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 18750
  · exact ⟨18679, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 18820
  · exact ⟨18749, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 18874
  · exact ⟨18803, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 18940
  · exact ⟨18869, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 18990
  · exact ⟨18919, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 19050
  · exact ⟨18979, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 19122
  · exact ⟨19051, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 19192
  · exact ⟨19121, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 19254
  · exact ⟨19183, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 19320
  · exact ⟨19249, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 19390
  · exact ⟨19319, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 19462
  · exact ⟨19391, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 19534
  · exact ⟨19463, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 19602
  · exact ⟨19531, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 19674
  · exact ⟨19603, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 19732
  · exact ⟨19661, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 19798
  · exact ⟨19727, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 19864
  · exact ⟨19793, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 19932
  · exact ⟨19861, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 19998
  · exact ⟨19927, by norm_num, by omega, by omega⟩
  · exact ⟨19997, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_8 (n : ℕ) (hlo : 20001 ≤ n) (hhi : n ≤ 22500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 20068
  · exact ⟨19997, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 20134
  · exact ⟨20063, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 20200
  · exact ⟨20129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 20272
  · exact ⟨20201, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 20340
  · exact ⟨20269, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 20412
  · exact ⟨20341, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 20482
  · exact ⟨20411, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 20554
  · exact ⟨20483, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 20622
  · exact ⟨20551, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 20682
  · exact ⟨20611, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 20752
  · exact ⟨20681, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 20824
  · exact ⟨20753, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 20880
  · exact ⟨20809, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 20950
  · exact ⟨20879, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 21018
  · exact ⟨20947, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 21090
  · exact ⟨21019, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 21160
  · exact ⟨21089, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 21228
  · exact ⟨21157, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 21298
  · exact ⟨21227, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 21354
  · exact ⟨21283, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 21418
  · exact ⟨21347, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 21490
  · exact ⟨21419, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 21562
  · exact ⟨21491, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 21634
  · exact ⟨21563, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 21688
  · exact ⟨21617, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 21754
  · exact ⟨21683, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 21822
  · exact ⟨21751, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 21892
  · exact ⟨21821, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 21964
  · exact ⟨21893, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 22032
  · exact ⟨21961, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 22102
  · exact ⟨22031, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 22164
  · exact ⟨22093, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 22230
  · exact ⟨22159, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 22300
  · exact ⟨22229, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 22362
  · exact ⟨22291, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 22420
  · exact ⟨22349, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 22480
  · exact ⟨22409, by norm_num, by omega, by omega⟩
  · exact ⟨22481, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_9 (n : ℕ) (hlo : 22501 ≤ n) (hhi : n ≤ 25000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 22572
  · exact ⟨22501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 22644
  · exact ⟨22573, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 22714
  · exact ⟨22643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 22780
  · exact ⟨22709, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 22848
  · exact ⟨22777, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 22888
  · exact ⟨22817, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 22948
  · exact ⟨22877, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 23014
  · exact ⟨22943, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 23082
  · exact ⟨23011, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 23152
  · exact ⟨23081, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 23214
  · exact ⟨23143, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 23280
  · exact ⟨23209, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 23350
  · exact ⟨23279, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 23410
  · exact ⟨23339, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 23470
  · exact ⟨23399, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 23530
  · exact ⟨23459, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 23602
  · exact ⟨23531, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 23674
  · exact ⟨23603, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 23742
  · exact ⟨23671, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 23814
  · exact ⟨23743, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 23884
  · exact ⟨23813, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 23950
  · exact ⟨23879, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 24000
  · exact ⟨23929, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 24072
  · exact ⟨24001, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 24142
  · exact ⟨24071, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 24208
  · exact ⟨24137, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 24274
  · exact ⟨24203, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 24322
  · exact ⟨24251, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 24388
  · exact ⟨24317, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 24450
  · exact ⟨24379, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 24514
  · exact ⟨24443, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 24580
  · exact ⟨24509, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 24642
  · exact ⟨24571, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 24702
  · exact ⟨24631, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 24768
  · exact ⟨24697, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 24838
  · exact ⟨24767, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 24892
  · exact ⟨24821, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 24960
  · exact ⟨24889, by norm_num, by omega, by omega⟩
  · exact ⟨24953, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_10 (n : ℕ) (hlo : 25001 ≤ n) (hhi : n ≤ 27500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 25060
  · exact ⟨24989, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 25128
  · exact ⟨25057, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 25198
  · exact ⟨25127, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 25260
  · exact ⟨25189, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 25332
  · exact ⟨25261, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 25392
  · exact ⟨25321, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 25462
  · exact ⟨25391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 25534
  · exact ⟨25463, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 25594
  · exact ⟨25523, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 25660
  · exact ⟨25589, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 25728
  · exact ⟨25657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 25788
  · exact ⟨25717, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 25842
  · exact ⟨25771, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 25912
  · exact ⟨25841, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 25984
  · exact ⟨25913, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 26052
  · exact ⟨25981, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 26124
  · exact ⟨26053, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 26190
  · exact ⟨26119, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 26260
  · exact ⟨26189, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 26332
  · exact ⟨26261, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 26392
  · exact ⟨26321, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 26464
  · exact ⟨26393, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 26530
  · exact ⟨26459, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 26584
  · exact ⟨26513, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 26644
  · exact ⟨26573, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 26712
  · exact ⟨26641, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 26784
  · exact ⟨26713, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 26854
  · exact ⟨26783, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 26920
  · exact ⟨26849, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 26992
  · exact ⟨26921, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 27064
  · exact ⟨26993, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 27132
  · exact ⟨27061, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 27198
  · exact ⟨27127, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 27268
  · exact ⟨27197, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 27330
  · exact ⟨27259, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 27400
  · exact ⟨27329, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 27468
  · exact ⟨27397, by norm_num, by omega, by omega⟩
  · exact ⟨27457, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_11 (n : ℕ) (hlo : 27501 ≤ n) (hhi : n ≤ 30000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 27558
  · exact ⟨27487, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 27622
  · exact ⟨27551, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 27688
  · exact ⟨27617, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 27760
  · exact ⟨27689, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 27822
  · exact ⟨27751, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 27894
  · exact ⟨27823, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 27964
  · exact ⟨27893, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 28032
  · exact ⟨27961, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 28102
  · exact ⟨28031, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 28170
  · exact ⟨28099, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 28234
  · exact ⟨28163, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 28300
  · exact ⟨28229, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 28368
  · exact ⟨28297, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 28422
  · exact ⟨28351, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 28482
  · exact ⟨28411, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 28548
  · exact ⟨28477, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 28620
  · exact ⟨28549, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 28692
  · exact ⟨28621, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 28758
  · exact ⟨28687, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 28830
  · exact ⟨28759, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 28888
  · exact ⟨28817, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 28950
  · exact ⟨28879, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 29020
  · exact ⟨28949, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 29092
  · exact ⟨29021, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 29148
  · exact ⟨29077, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 29218
  · exact ⟨29147, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 29280
  · exact ⟨29209, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 29340
  · exact ⟨29269, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 29410
  · exact ⟨29339, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 29482
  · exact ⟨29411, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 29554
  · exact ⟨29483, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 29608
  · exact ⟨29537, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 29670
  · exact ⟨29599, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 29742
  · exact ⟨29671, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 29812
  · exact ⟨29741, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 29874
  · exact ⟨29803, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 29944
  · exact ⟨29873, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 29998
  · exact ⟨29927, by norm_num, by omega, by omega⟩
  · exact ⟨29989, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_12 (n : ℕ) (hlo : 30001 ≤ n) (hhi : n ≤ 32500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 30060
  · exact ⟨29989, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 30130
  · exact ⟨30059, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 30190
  · exact ⟨30119, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 30258
  · exact ⟨30187, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 30330
  · exact ⟨30259, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 30394
  · exact ⟨30323, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 30462
  · exact ⟨30391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 30520
  · exact ⟨30449, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 30588
  · exact ⟨30517, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 30648
  · exact ⟨30577, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 30720
  · exact ⟨30649, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 30784
  · exact ⟨30713, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 30852
  · exact ⟨30781, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 30924
  · exact ⟨30853, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 30982
  · exact ⟨30911, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 31054
  · exact ⟨30983, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 31122
  · exact ⟨31051, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 31194
  · exact ⟨31123, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 31264
  · exact ⟨31193, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 31330
  · exact ⟨31259, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 31398
  · exact ⟨31327, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 31468
  · exact ⟨31397, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 31540
  · exact ⟨31469, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 31612
  · exact ⟨31541, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 31678
  · exact ⟨31607, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 31738
  · exact ⟨31667, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 31800
  · exact ⟨31729, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 31870
  · exact ⟨31799, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 31930
  · exact ⟨31859, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 31978
  · exact ⟨31907, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 32044
  · exact ⟨31973, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 32100
  · exact ⟨32029, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 32170
  · exact ⟨32099, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 32230
  · exact ⟨32159, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 32284
  · exact ⟨32213, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 32332
  · exact ⟨32261, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 32398
  · exact ⟨32327, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 32452
  · exact ⟨32381, by norm_num, by omega, by omega⟩
  · exact ⟨32443, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_13 (n : ℕ) (hlo : 32501 ≤ n) (hhi : n ≤ 35000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 32568
  · exact ⟨32497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 32640
  · exact ⟨32569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 32704
  · exact ⟨32633, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 32764
  · exact ⟨32693, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 32820
  · exact ⟨32749, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 32874
  · exact ⟨32803, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 32940
  · exact ⟨32869, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 33012
  · exact ⟨32941, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 33084
  · exact ⟨33013, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 33154
  · exact ⟨33083, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 33222
  · exact ⟨33151, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 33294
  · exact ⟨33223, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 33360
  · exact ⟨33289, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 33430
  · exact ⟨33359, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 33498
  · exact ⟨33427, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 33564
  · exact ⟨33493, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 33634
  · exact ⟨33563, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 33700
  · exact ⟨33629, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 33750
  · exact ⟨33679, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 33822
  · exact ⟨33751, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 33882
  · exact ⟨33811, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 33942
  · exact ⟨33871, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 34012
  · exact ⟨33941, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 34068
  · exact ⟨33997, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 34132
  · exact ⟨34061, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 34200
  · exact ⟨34129, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 34254
  · exact ⟨34183, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 34324
  · exact ⟨34253, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 34390
  · exact ⟨34319, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 34452
  · exact ⟨34381, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 34510
  · exact ⟨34439, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 34582
  · exact ⟨34511, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 34654
  · exact ⟨34583, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 34722
  · exact ⟨34651, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 34792
  · exact ⟨34721, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 34852
  · exact ⟨34781, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 34920
  · exact ⟨34849, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 34990
  · exact ⟨34919, by norm_num, by omega, by omega⟩
  · exact ⟨34981, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_14 (n : ℕ) (hlo : 35001 ≤ n) (hhi : n ≤ 37500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 35052
  · exact ⟨34981, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 35124
  · exact ⟨35053, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 35188
  · exact ⟨35117, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 35242
  · exact ⟨35171, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 35298
  · exact ⟨35227, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 35362
  · exact ⟨35291, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 35434
  · exact ⟨35363, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 35494
  · exact ⟨35423, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 35562
  · exact ⟨35491, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 35614
  · exact ⟨35543, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 35674
  · exact ⟨35603, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 35742
  · exact ⟨35671, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 35802
  · exact ⟨35731, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 35874
  · exact ⟨35803, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 35940
  · exact ⟨35869, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 36004
  · exact ⟨35933, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 36070
  · exact ⟨35999, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 36138
  · exact ⟨36067, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 36208
  · exact ⟨36137, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 36280
  · exact ⟨36209, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 36348
  · exact ⟨36277, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 36414
  · exact ⟨36343, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 36460
  · exact ⟨36389, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 36528
  · exact ⟨36457, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 36600
  · exact ⟨36529, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 36670
  · exact ⟨36599, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 36742
  · exact ⟨36671, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 36810
  · exact ⟨36739, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 36880
  · exact ⟨36809, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 36948
  · exact ⟨36877, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 37018
  · exact ⟨36947, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 37090
  · exact ⟨37019, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 37158
  · exact ⟨37087, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 37230
  · exact ⟨37159, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 37294
  · exact ⟨37223, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 37348
  · exact ⟨37277, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 37410
  · exact ⟨37339, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 37480
  · exact ⟨37409, by norm_num, by omega, by omega⟩
  · exact ⟨37463, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_15 (n : ℕ) (hlo : 37501 ≤ n) (hhi : n ≤ 40000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 37572
  · exact ⟨37501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 37644
  · exact ⟨37573, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 37714
  · exact ⟨37643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 37770
  · exact ⟨37699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 37818
  · exact ⟨37747, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 37884
  · exact ⟨37813, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 37950
  · exact ⟨37879, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 38022
  · exact ⟨37951, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 38082
  · exact ⟨38011, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 38154
  · exact ⟨38083, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 38224
  · exact ⟨38153, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 38290
  · exact ⟨38219, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 38358
  · exact ⟨38287, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 38422
  · exact ⟨38351, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 38464
  · exact ⟨38393, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 38532
  · exact ⟨38461, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 38572
  · exact ⟨38501, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 38640
  · exact ⟨38569, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 38710
  · exact ⟨38639, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 38782
  · exact ⟨38711, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 38854
  · exact ⟨38783, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 38922
  · exact ⟨38851, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 38994
  · exact ⟨38923, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 39064
  · exact ⟨38993, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 39118
  · exact ⟨39047, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 39190
  · exact ⟨39119, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 39262
  · exact ⟨39191, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 39322
  · exact ⟨39251, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 39394
  · exact ⟨39323, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 39454
  · exact ⟨39383, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 39522
  · exact ⟨39451, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 39592
  · exact ⟨39521, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 39652
  · exact ⟨39581, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 39702
  · exact ⟨39631, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 39774
  · exact ⟨39703, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 39840
  · exact ⟨39769, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 39912
  · exact ⟨39841, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 39972
  · exact ⟨39901, by norm_num, by omega, by omega⟩
  · exact ⟨39971, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_16 (n : ℕ) (hlo : 40001 ≤ n) (hhi : n ≤ 42500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 40060
  · exact ⟨39989, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 40110
  · exact ⟨40039, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 40182
  · exact ⟨40111, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 40248
  · exact ⟨40177, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 40312
  · exact ⟨40241, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 40360
  · exact ⟨40289, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 40432
  · exact ⟨40361, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 40504
  · exact ⟨40433, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 40570
  · exact ⟨40499, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 40630
  · exact ⟨40559, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 40698
  · exact ⟨40627, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 40770
  · exact ⟨40699, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 40842
  · exact ⟨40771, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 40912
  · exact ⟨40841, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 40974
  · exact ⟨40903, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 41044
  · exact ⟨40973, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 41110
  · exact ⟨41039, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 41152
  · exact ⟨41081, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 41220
  · exact ⟨41149, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 41292
  · exact ⟨41221, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 41352
  · exact ⟨41281, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 41422
  · exact ⟨41351, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 41484
  · exact ⟨41413, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 41550
  · exact ⟨41479, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 41620
  · exact ⟨41549, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 41692
  · exact ⟨41621, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 41758
  · exact ⟨41687, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 41830
  · exact ⟨41759, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 41884
  · exact ⟨41813, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 41950
  · exact ⟨41879, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 42018
  · exact ⟨41947, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 42090
  · exact ⟨42019, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 42160
  · exact ⟨42089, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 42228
  · exact ⟨42157, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 42298
  · exact ⟨42227, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 42370
  · exact ⟨42299, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 42430
  · exact ⟨42359, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 42480
  · exact ⟨42409, by norm_num, by omega, by omega⟩
  · exact ⟨42473, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_17 (n : ℕ) (hlo : 42501 ≤ n) (hhi : n ≤ 45000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 42570
  · exact ⟨42499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 42642
  · exact ⟨42571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 42714
  · exact ⟨42643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 42780
  · exact ⟨42709, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 42844
  · exact ⟨42773, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 42912
  · exact ⟨42841, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 42972
  · exact ⟨42901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 43038
  · exact ⟨42967, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 43108
  · exact ⟨43037, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 43174
  · exact ⟨43103, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 43230
  · exact ⟨43159, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 43294
  · exact ⟨43223, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 43362
  · exact ⟨43291, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 43402
  · exact ⟨43331, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 43474
  · exact ⟨43403, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 43528
  · exact ⟨43457, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 43588
  · exact ⟨43517, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 43650
  · exact ⟨43579, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 43722
  · exact ⟨43651, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 43792
  · exact ⟨43721, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 43864
  · exact ⟨43793, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 43924
  · exact ⟨43853, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 43984
  · exact ⟨43913, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 44044
  · exact ⟨43973, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 44112
  · exact ⟨44041, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 44182
  · exact ⟨44111, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 44250
  · exact ⟨44179, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 44320
  · exact ⟨44249, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 44364
  · exact ⟨44293, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 44428
  · exact ⟨44357, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 44488
  · exact ⟨44417, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 44554
  · exact ⟨44483, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 44620
  · exact ⟨44549, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 44692
  · exact ⟨44621, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 44758
  · exact ⟨44687, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 44824
  · exact ⟨44753, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 44890
  · exact ⟨44819, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 44958
  · exact ⟨44887, by norm_num, by omega, by omega⟩
  · exact ⟨44959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_18 (n : ℕ) (hlo : 45001 ≤ n) (hhi : n ≤ 47500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 45058
  · exact ⟨44987, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 45124
  · exact ⟨45053, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 45192
  · exact ⟨45121, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 45262
  · exact ⟨45191, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 45334
  · exact ⟨45263, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 45400
  · exact ⟨45329, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 45460
  · exact ⟨45389, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 45510
  · exact ⟨45439, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 45574
  · exact ⟨45503, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 45640
  · exact ⟨45569, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 45712
  · exact ⟨45641, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 45778
  · exact ⟨45707, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 45850
  · exact ⟨45779, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 45912
  · exact ⟨45841, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 45964
  · exact ⟨45893, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 46030
  · exact ⟨45959, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 46098
  · exact ⟨46027, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 46170
  · exact ⟨46099, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 46242
  · exact ⟨46171, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 46308
  · exact ⟨46237, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 46380
  · exact ⟨46309, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 46452
  · exact ⟨46381, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 46522
  · exact ⟨46451, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 46594
  · exact ⟨46523, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 46662
  · exact ⟨46591, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 46734
  · exact ⟨46663, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 46798
  · exact ⟨46727, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 46842
  · exact ⟨46771, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 46902
  · exact ⟨46831, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 46972
  · exact ⟨46901, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 47028
  · exact ⟨46957, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 47088
  · exact ⟨47017, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 47158
  · exact ⟨47087, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 47220
  · exact ⟨47149, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 47292
  · exact ⟨47221, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 47364
  · exact ⟨47293, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 47434
  · exact ⟨47363, by norm_num, by omega, by omega⟩
  · exact ⟨47431, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_19 (n : ℕ) (hlo : 47501 ≤ n) (hhi : n ≤ 50000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 47572
  · exact ⟨47501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 47640
  · exact ⟨47569, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 47710
  · exact ⟨47639, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 47782
  · exact ⟨47711, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 47850
  · exact ⟨47779, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 47914
  · exact ⟨47843, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 47982
  · exact ⟨47911, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 48052
  · exact ⟨47981, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 48120
  · exact ⟨48049, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 48192
  · exact ⟨48121, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 48264
  · exact ⟨48193, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 48330
  · exact ⟨48259, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 48384
  · exact ⟨48313, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 48454
  · exact ⟨48383, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 48520
  · exact ⟨48449, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 48568
  · exact ⟨48497, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 48634
  · exact ⟨48563, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 48694
  · exact ⟨48623, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 48750
  · exact ⟨48679, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 48822
  · exact ⟨48751, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 48894
  · exact ⟨48823, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 48960
  · exact ⟨48889, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 49024
  · exact ⟨48953, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 49090
  · exact ⟨49019, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 49152
  · exact ⟨49081, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 49210
  · exact ⟨49139, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 49282
  · exact ⟨49211, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 49350
  · exact ⟨49279, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 49410
  · exact ⟨49339, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 49482
  · exact ⟨49411, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 49552
  · exact ⟨49481, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 49620
  · exact ⟨49549, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 49684
  · exact ⟨49613, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 49752
  · exact ⟨49681, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 49818
  · exact ⟨49747, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 49882
  · exact ⟨49811, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 49948
  · exact ⟨49877, by norm_num, by omega, by omega⟩
  · exact ⟨49943, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_20 (n : ℕ) (hlo : 50001 ≤ n) (hhi : n ≤ 52500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 50070
  · exact ⟨49999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 50140
  · exact ⟨50069, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 50202
  · exact ⟨50131, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 50248
  · exact ⟨50177, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 50302
  · exact ⟨50231, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 50362
  · exact ⟨50291, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 50434
  · exact ⟨50363, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 50494
  · exact ⟨50423, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 50532
  · exact ⟨50461, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 50598
  · exact ⟨50527, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 50670
  · exact ⟨50599, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 50742
  · exact ⟨50671, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 50812
  · exact ⟨50741, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 50860
  · exact ⟨50789, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 50928
  · exact ⟨50857, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 51000
  · exact ⟨50929, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 51072
  · exact ⟨51001, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 51142
  · exact ⟨51071, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 51208
  · exact ⟨51137, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 51274
  · exact ⟨51203, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 51334
  · exact ⟨51263, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 51400
  · exact ⟨51329, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 51454
  · exact ⟨51383, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 51520
  · exact ⟨51449, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 51592
  · exact ⟨51521, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 51664
  · exact ⟨51593, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 51730
  · exact ⟨51659, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 51792
  · exact ⟨51721, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 51858
  · exact ⟨51787, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 51930
  · exact ⟨51859, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 52000
  · exact ⟨51929, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 52062
  · exact ⟨51991, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 52128
  · exact ⟨52057, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 52198
  · exact ⟨52127, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 52260
  · exact ⟨52189, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 52330
  · exact ⟨52259, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 52392
  · exact ⟨52321, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 52462
  · exact ⟨52391, by norm_num, by omega, by omega⟩
  · exact ⟨52457, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_21 (n : ℕ) (hlo : 52501 ≤ n) (hhi : n ≤ 55000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 52572
  · exact ⟨52501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 52642
  · exact ⟨52571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 52710
  · exact ⟨52639, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 52782
  · exact ⟨52711, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 52854
  · exact ⟨52783, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 52908
  · exact ⟨52837, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 52974
  · exact ⟨52903, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 53044
  · exact ⟨52973, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 53088
  · exact ⟨53017, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 53160
  · exact ⟨53089, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 53232
  · exact ⟨53161, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 53304
  · exact ⟨53233, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 53370
  · exact ⟨53299, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 53430
  · exact ⟨53359, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 53490
  · exact ⟨53419, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 53550
  · exact ⟨53479, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 53622
  · exact ⟨53551, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 53694
  · exact ⟨53623, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 53764
  · exact ⟨53693, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 53830
  · exact ⟨53759, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 53902
  · exact ⟨53831, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 53970
  · exact ⟨53899, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 54030
  · exact ⟨53959, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 54084
  · exact ⟨54013, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 54154
  · exact ⟨54083, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 54222
  · exact ⟨54151, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 54288
  · exact ⟨54217, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 54358
  · exact ⟨54287, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 54418
  · exact ⟨54347, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 54490
  · exact ⟨54419, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 54540
  · exact ⟨54469, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 54612
  · exact ⟨54541, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 54672
  · exact ⟨54601, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 54744
  · exact ⟨54673, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 54798
  · exact ⟨54727, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 54870
  · exact ⟨54799, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 54940
  · exact ⟨54869, by norm_num, by omega, by omega⟩
  · exact ⟨54941, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_22 (n : ℕ) (hlo : 55001 ≤ n) (hhi : n ≤ 57500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 55072
  · exact ⟨55001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 55144
  · exact ⟨55073, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 55198
  · exact ⟨55127, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 55242
  · exact ⟨55171, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 55314
  · exact ⟨55243, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 55384
  · exact ⟨55313, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 55452
  · exact ⟨55381, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 55512
  · exact ⟨55441, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 55582
  · exact ⟨55511, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 55650
  · exact ⟨55579, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 55710
  · exact ⟨55639, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 55782
  · exact ⟨55711, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 55834
  · exact ⟨55763, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 55900
  · exact ⟨55829, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 55972
  · exact ⟨55901, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 56038
  · exact ⟨55967, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 56110
  · exact ⟨56039, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 56172
  · exact ⟨56101, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 56242
  · exact ⟨56171, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 56310
  · exact ⟨56239, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 56382
  · exact ⟨56311, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 56454
  · exact ⟨56383, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 56524
  · exact ⟨56453, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 56590
  · exact ⟨56519, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 56662
  · exact ⟨56591, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 56734
  · exact ⟨56663, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 56802
  · exact ⟨56731, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 56854
  · exact ⟨56783, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 56914
  · exact ⟨56843, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 56982
  · exact ⟨56911, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 57054
  · exact ⟨56983, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 57118
  · exact ⟨57047, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 57190
  · exact ⟨57119, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 57262
  · exact ⟨57191, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 57330
  · exact ⟨57259, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 57402
  · exact ⟨57331, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 57468
  · exact ⟨57397, by norm_num, by omega, by omega⟩
  · exact ⟨57467, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_23 (n : ℕ) (hlo : 57501 ≤ n) (hhi : n ≤ 60000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 57564
  · exact ⟨57493, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 57630
  · exact ⟨57559, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 57672
  · exact ⟨57601, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 57738
  · exact ⟨57667, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 57808
  · exact ⟨57737, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 57880
  · exact ⟨57809, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 57952
  · exact ⟨57881, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 58018
  · exact ⟨57947, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 58084
  · exact ⟨58013, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 58144
  · exact ⟨58073, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 58200
  · exact ⟨58129, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 58270
  · exact ⟨58199, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 58342
  · exact ⟨58271, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 58408
  · exact ⟨58337, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 58474
  · exact ⟨58403, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 58524
  · exact ⟨58453, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 58582
  · exact ⟨58511, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 58650
  · exact ⟨58579, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 58702
  · exact ⟨58631, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 58770
  · exact ⟨58699, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 58842
  · exact ⟨58771, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 58902
  · exact ⟨58831, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 58972
  · exact ⟨58901, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 59038
  · exact ⟨58967, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 59100
  · exact ⟨59029, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 59164
  · exact ⟨59093, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 59230
  · exact ⟨59159, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 59292
  · exact ⟨59221, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 59352
  · exact ⟨59281, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 59422
  · exact ⟨59351, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 59490
  · exact ⟨59419, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 59544
  · exact ⟨59473, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 59610
  · exact ⟨59539, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 59682
  · exact ⟨59611, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 59742
  · exact ⟨59671, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 59814
  · exact ⟨59743, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 59880
  · exact ⟨59809, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 59950
  · exact ⟨59879, by norm_num, by omega, by omega⟩
  · exact ⟨59951, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_24 (n : ℕ) (hlo : 60001 ≤ n) (hhi : n ≤ 62500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 60070
  · exact ⟨59999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 60112
  · exact ⟨60041, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 60178
  · exact ⟨60107, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 60240
  · exact ⟨60169, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 60294
  · exact ⟨60223, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 60364
  · exact ⟨60293, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 60424
  · exact ⟨60353, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 60484
  · exact ⟨60413, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 60528
  · exact ⟨60457, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 60598
  · exact ⟨60527, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 60660
  · exact ⟨60589, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 60732
  · exact ⟨60661, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 60804
  · exact ⟨60733, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 60864
  · exact ⟨60793, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 60930
  · exact ⟨60859, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 60994
  · exact ⟨60923, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 61032
  · exact ⟨60961, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 61102
  · exact ⟨61031, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 61170
  · exact ⟨61099, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 61240
  · exact ⟨61169, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 61302
  · exact ⟨61231, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 61368
  · exact ⟨61297, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 61434
  · exact ⟨61363, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 61488
  · exact ⟨61417, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 61558
  · exact ⟨61487, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 61630
  · exact ⟨61559, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 61702
  · exact ⟨61631, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 61774
  · exact ⟨61703, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 61828
  · exact ⟨61757, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 61890
  · exact ⟨61819, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 61950
  · exact ⟨61879, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 62020
  · exact ⟨61949, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 62088
  · exact ⟨62017, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 62152
  · exact ⟨62081, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 62214
  · exact ⟨62143, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 62284
  · exact ⟨62213, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 62344
  · exact ⟨62273, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 62398
  · exact ⟨62327, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 62454
  · exact ⟨62383, by norm_num, by omega, by omega⟩
  by_cases h39 : n ≤ 62494
  · exact ⟨62423, by norm_num, by omega, by omega⟩
  · exact ⟨62483, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_25 (n : ℕ) (hlo : 62501 ≤ n) (hhi : n ≤ 65000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 62572
  · exact ⟨62501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 62634
  · exact ⟨62563, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 62704
  · exact ⟨62633, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 62772
  · exact ⟨62701, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 62844
  · exact ⟨62773, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 62898
  · exact ⟨62827, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 62968
  · exact ⟨62897, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 63040
  · exact ⟨62969, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 63102
  · exact ⟨63031, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 63174
  · exact ⟨63103, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 63220
  · exact ⟨63149, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 63282
  · exact ⟨63211, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 63352
  · exact ⟨63281, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 63424
  · exact ⟨63353, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 63492
  · exact ⟨63421, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 63564
  · exact ⟨63493, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 63630
  · exact ⟨63559, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 63700
  · exact ⟨63629, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 63768
  · exact ⟨63697, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 63832
  · exact ⟨63761, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 63894
  · exact ⟨63823, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 63934
  · exact ⟨63863, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 64000
  · exact ⟨63929, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 64068
  · exact ⟨63997, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 64138
  · exact ⟨64067, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 64194
  · exact ⟨64123, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 64260
  · exact ⟨64189, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 64308
  · exact ⟨64237, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 64374
  · exact ⟨64303, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 64444
  · exact ⟨64373, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 64510
  · exact ⟨64439, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 64570
  · exact ⟨64499, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 64638
  · exact ⟨64567, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 64704
  · exact ⟨64633, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 64764
  · exact ⟨64693, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 64834
  · exact ⟨64763, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 64888
  · exact ⟨64817, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 64950
  · exact ⟨64879, by norm_num, by omega, by omega⟩
  · exact ⟨64951, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_26 (n : ℕ) (hlo : 65001 ≤ n) (hhi : n ≤ 67500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 65068
  · exact ⟨64997, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 65134
  · exact ⟨65063, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 65200
  · exact ⟨65129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 65254
  · exact ⟨65183, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 65310
  · exact ⟨65239, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 65380
  · exact ⟨65309, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 65452
  · exact ⟨65381, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 65520
  · exact ⟨65449, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 65592
  · exact ⟨65521, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 65658
  · exact ⟨65587, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 65728
  · exact ⟨65657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 65800
  · exact ⟨65729, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 65860
  · exact ⟨65789, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 65922
  · exact ⟨65851, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 65992
  · exact ⟨65921, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 66064
  · exact ⟨65993, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 66118
  · exact ⟨66047, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 66180
  · exact ⟨66109, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 66250
  · exact ⟨66179, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 66310
  · exact ⟨66239, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 66372
  · exact ⟨66301, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 66444
  · exact ⟨66373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 66502
  · exact ⟨66431, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 66570
  · exact ⟨66499, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 66642
  · exact ⟨66571, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 66714
  · exact ⟨66643, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 66784
  · exact ⟨66713, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 66834
  · exact ⟨66763, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 66892
  · exact ⟨66821, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 66960
  · exact ⟨66889, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 67030
  · exact ⟨66959, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 67092
  · exact ⟨67021, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 67150
  · exact ⟨67079, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 67212
  · exact ⟨67141, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 67284
  · exact ⟨67213, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 67344
  · exact ⟨67273, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 67414
  · exact ⟨67343, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 67482
  · exact ⟨67411, by norm_num, by omega, by omega⟩
  · exact ⟨67481, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_27 (n : ℕ) (hlo : 67501 ≤ n) (hhi : n ≤ 70000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 67570
  · exact ⟨67499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 67638
  · exact ⟨67567, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 67702
  · exact ⟨67631, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 67770
  · exact ⟨67699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 67834
  · exact ⟨67763, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 67900
  · exact ⟨67829, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 67972
  · exact ⟨67901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 68038
  · exact ⟨67967, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 68094
  · exact ⟨68023, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 68158
  · exact ⟨68087, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 68218
  · exact ⟨68147, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 68290
  · exact ⟨68219, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 68352
  · exact ⟨68281, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 68422
  · exact ⟨68351, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 68470
  · exact ⟨68399, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 68520
  · exact ⟨68449, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 68592
  · exact ⟨68521, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 68652
  · exact ⟨68581, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 68710
  · exact ⟨68639, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 68782
  · exact ⟨68711, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 68848
  · exact ⟨68777, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 68892
  · exact ⟨68821, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 68962
  · exact ⟨68891, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 69034
  · exact ⟨68963, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 69102
  · exact ⟨69031, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 69144
  · exact ⟨69073, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 69214
  · exact ⟨69143, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 69274
  · exact ⟨69203, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 69334
  · exact ⟨69263, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 69388
  · exact ⟨69317, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 69460
  · exact ⟨69389, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 69528
  · exact ⟨69457, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 69570
  · exact ⟨69499, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 69628
  · exact ⟨69557, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 69694
  · exact ⟨69623, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 69762
  · exact ⟨69691, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 69834
  · exact ⟨69763, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 69904
  · exact ⟨69833, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 69970
  · exact ⟨69899, by norm_num, by omega, by omega⟩
  · exact ⟨69959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_28 (n : ℕ) (hlo : 70001 ≤ n) (hhi : n ≤ 72500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 70072
  · exact ⟨70001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 70138
  · exact ⟨70067, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 70210
  · exact ⟨70139, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 70278
  · exact ⟨70207, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 70342
  · exact ⟨70271, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 70398
  · exact ⟨70327, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 70464
  · exact ⟨70393, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 70530
  · exact ⟨70459, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 70600
  · exact ⟨70529, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 70660
  · exact ⟨70589, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 70728
  · exact ⟨70657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 70800
  · exact ⟨70729, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 70864
  · exact ⟨70793, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 70924
  · exact ⟨70853, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 70992
  · exact ⟨70921, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 71062
  · exact ⟨70991, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 71130
  · exact ⟨71059, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 71200
  · exact ⟨71129, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 71262
  · exact ⟨71191, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 71334
  · exact ⟨71263, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 71404
  · exact ⟨71333, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 71470
  · exact ⟨71399, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 71542
  · exact ⟨71471, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 71608
  · exact ⟨71537, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 71668
  · exact ⟨71597, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 71734
  · exact ⟨71663, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 71790
  · exact ⟨71719, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 71860
  · exact ⟨71789, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 71932
  · exact ⟨71861, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 72004
  · exact ⟨71933, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 72070
  · exact ⟨71999, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 72124
  · exact ⟨72053, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 72180
  · exact ⟨72109, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 72244
  · exact ⟨72173, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 72300
  · exact ⟨72229, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 72358
  · exact ⟨72287, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 72424
  · exact ⟨72353, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 72492
  · exact ⟨72421, by norm_num, by omega, by omega⟩
  · exact ⟨72493, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_29 (n : ℕ) (hlo : 72501 ≤ n) (hhi : n ≤ 75000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 72568
  · exact ⟨72497, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 72630
  · exact ⟨72559, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 72694
  · exact ⟨72623, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 72760
  · exact ⟨72689, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 72810
  · exact ⟨72739, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 72868
  · exact ⟨72797, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 72940
  · exact ⟨72869, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 73008
  · exact ⟨72937, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 73080
  · exact ⟨73009, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 73150
  · exact ⟨73079, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 73212
  · exact ⟨73141, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 73260
  · exact ⟨73189, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 73330
  · exact ⟨73259, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 73402
  · exact ⟨73331, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 73458
  · exact ⟨73387, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 73530
  · exact ⟨73459, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 73600
  · exact ⟨73529, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 73668
  · exact ⟨73597, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 73722
  · exact ⟨73651, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 73792
  · exact ⟨73721, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 73854
  · exact ⟨73783, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 73920
  · exact ⟨73849, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 73978
  · exact ⟨73907, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 74044
  · exact ⟨73973, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 74098
  · exact ⟨74027, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 74170
  · exact ⟨74099, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 74238
  · exact ⟨74167, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 74302
  · exact ⟨74231, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 74368
  · exact ⟨74297, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 74434
  · exact ⟨74363, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 74490
  · exact ⟨74419, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 74560
  · exact ⟨74489, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 74632
  · exact ⟨74561, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 74694
  · exact ⟨74623, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 74758
  · exact ⟨74687, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 74830
  · exact ⟨74759, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 74902
  · exact ⟨74831, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 74974
  · exact ⟨74903, by norm_num, by omega, by omega⟩
  · exact ⟨74959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_30 (n : ℕ) (hlo : 75001 ≤ n) (hhi : n ≤ 77500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 75030
  · exact ⟨74959, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 75100
  · exact ⟨75029, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 75154
  · exact ⟨75083, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 75220
  · exact ⟨75149, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 75288
  · exact ⟨75217, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 75360
  · exact ⟨75289, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 75424
  · exact ⟨75353, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 75478
  · exact ⟨75407, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 75550
  · exact ⟨75479, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 75612
  · exact ⟨75541, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 75682
  · exact ⟨75611, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 75754
  · exact ⟨75683, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 75814
  · exact ⟨75743, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 75868
  · exact ⟨75797, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 75940
  · exact ⟨75869, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 76012
  · exact ⟨75941, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 76074
  · exact ⟨76003, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 76110
  · exact ⟨76039, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 76174
  · exact ⟨76103, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 76234
  · exact ⟨76163, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 76302
  · exact ⟨76231, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 76374
  · exact ⟨76303, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 76440
  · exact ⟨76369, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 76512
  · exact ⟨76441, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 76582
  · exact ⟨76511, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 76650
  · exact ⟨76579, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 76722
  · exact ⟨76651, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 76788
  · exact ⟨76717, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 76852
  · exact ⟨76781, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 76918
  · exact ⟨76847, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 76990
  · exact ⟨76919, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 77062
  · exact ⟨76991, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 77118
  · exact ⟨77047, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 77172
  · exact ⟨77101, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 77242
  · exact ⟨77171, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 77314
  · exact ⟨77243, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 77362
  · exact ⟨77291, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 77430
  · exact ⟨77359, by norm_num, by omega, by omega⟩
  · exact ⟨77431, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_31 (n : ℕ) (hlo : 77501 ≤ n) (hhi : n ≤ 80000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 77562
  · exact ⟨77491, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 77634
  · exact ⟨77563, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 77692
  · exact ⟨77621, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 77760
  · exact ⟨77689, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 77832
  · exact ⟨77761, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 77884
  · exact ⟨77813, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 77938
  · exact ⟨77867, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 78004
  · exact ⟨77933, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 78070
  · exact ⟨77999, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 78130
  · exact ⟨78059, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 78192
  · exact ⟨78121, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 78264
  · exact ⟨78193, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 78330
  · exact ⟨78259, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 78388
  · exact ⟨78317, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 78438
  · exact ⟨78367, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 78510
  · exact ⟨78439, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 78582
  · exact ⟨78511, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 78654
  · exact ⟨78583, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 78724
  · exact ⟨78653, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 78792
  · exact ⟨78721, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 78862
  · exact ⟨78791, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 78928
  · exact ⟨78857, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 79000
  · exact ⟨78929, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 79060
  · exact ⟨78989, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 79114
  · exact ⟨79043, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 79182
  · exact ⟨79111, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 79252
  · exact ⟨79181, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 79312
  · exact ⟨79241, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 79380
  · exact ⟨79309, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 79450
  · exact ⟨79379, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 79522
  · exact ⟨79451, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 79564
  · exact ⟨79493, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 79632
  · exact ⟨79561, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 79704
  · exact ⟨79633, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 79770
  · exact ⟨79699, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 79840
  · exact ⟨79769, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 79912
  · exact ⟨79841, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 79978
  · exact ⟨79907, by norm_num, by omega, by omega⟩
  · exact ⟨79979, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_32 (n : ℕ) (hlo : 80001 ≤ n) (hhi : n ≤ 82500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 80070
  · exact ⟨79999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 80142
  · exact ⟨80071, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 80212
  · exact ⟨80141, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 80280
  · exact ⟨80209, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 80350
  · exact ⟨80279, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 80418
  · exact ⟨80347, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 80478
  · exact ⟨80407, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 80544
  · exact ⟨80473, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 80608
  · exact ⟨80537, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 80674
  · exact ⟨80603, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 80742
  · exact ⟨80671, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 80808
  · exact ⟨80737, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 80880
  · exact ⟨80809, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 80934
  · exact ⟨80863, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 81004
  · exact ⟨80933, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 81072
  · exact ⟨81001, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 81142
  · exact ⟨81071, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 81202
  · exact ⟨81131, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 81274
  · exact ⟨81203, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 81310
  · exact ⟨81239, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 81378
  · exact ⟨81307, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 81444
  · exact ⟨81373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 81510
  · exact ⟨81439, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 81580
  · exact ⟨81509, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 81640
  · exact ⟨81569, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 81708
  · exact ⟨81637, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 81778
  · exact ⟨81707, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 81844
  · exact ⟨81773, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 81910
  · exact ⟨81839, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 81972
  · exact ⟨81901, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 82044
  · exact ⟨81973, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 82110
  · exact ⟨82039, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 82144
  · exact ⟨82073, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 82212
  · exact ⟨82141, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 82278
  · exact ⟨82207, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 82350
  · exact ⟨82279, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 82422
  · exact ⟨82351, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 82492
  · exact ⟨82421, by norm_num, by omega, by omega⟩
  · exact ⟨82493, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_33 (n : ℕ) (hlo : 82501 ≤ n) (hhi : n ≤ 85000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 82570
  · exact ⟨82499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 82642
  · exact ⟨82571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 82704
  · exact ⟨82633, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 82770
  · exact ⟨82699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 82834
  · exact ⟨82763, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 82884
  · exact ⟨82813, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 82954
  · exact ⟨82883, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 83010
  · exact ⟨82939, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 83080
  · exact ⟨83009, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 83148
  · exact ⟨83077, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 83208
  · exact ⟨83137, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 83278
  · exact ⟨83207, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 83344
  · exact ⟨83273, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 83412
  · exact ⟨83341, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 83478
  · exact ⟨83407, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 83548
  · exact ⟨83477, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 83608
  · exact ⟨83537, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 83680
  · exact ⟨83609, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 83734
  · exact ⟨83663, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 83790
  · exact ⟨83719, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 83862
  · exact ⟨83791, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 83928
  · exact ⟨83857, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 83992
  · exact ⟨83921, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 84058
  · exact ⟨83987, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 84130
  · exact ⟨84059, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 84202
  · exact ⟨84131, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 84270
  · exact ⟨84199, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 84334
  · exact ⟨84263, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 84390
  · exact ⟨84319, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 84462
  · exact ⟨84391, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 84534
  · exact ⟨84463, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 84604
  · exact ⟨84533, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 84660
  · exact ⟨84589, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 84730
  · exact ⟨84659, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 84802
  · exact ⟨84731, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 84864
  · exact ⟨84793, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 84930
  · exact ⟨84859, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 84990
  · exact ⟨84919, by norm_num, by omega, by omega⟩
  · exact ⟨84991, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_34 (n : ℕ) (hlo : 85001 ≤ n) (hhi : n ≤ 87500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 85062
  · exact ⟨84991, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 85132
  · exact ⟨85061, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 85204
  · exact ⟨85133, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 85272
  · exact ⟨85201, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 85330
  · exact ⟨85259, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 85402
  · exact ⟨85331, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 85452
  · exact ⟨85381, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 85524
  · exact ⟨85453, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 85594
  · exact ⟨85523, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 85648
  · exact ⟨85577, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 85714
  · exact ⟨85643, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 85782
  · exact ⟨85711, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 85852
  · exact ⟨85781, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 85924
  · exact ⟨85853, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 85980
  · exact ⟨85909, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 86004
  · exact ⟨85933, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 86070
  · exact ⟨85999, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 86140
  · exact ⟨86069, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 86208
  · exact ⟨86137, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 86280
  · exact ⟨86209, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 86340
  · exact ⟨86269, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 86412
  · exact ⟨86341, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 86484
  · exact ⟨86413, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 86548
  · exact ⟨86477, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 86610
  · exact ⟨86539, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 86670
  · exact ⟨86599, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 86700
  · exact ⟨86629, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 86764
  · exact ⟨86693, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 86824
  · exact ⟨86753, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 86884
  · exact ⟨86813, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 86940
  · exact ⟨86869, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 87010
  · exact ⟨86939, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 87082
  · exact ⟨87011, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 87154
  · exact ⟨87083, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 87222
  · exact ⟨87151, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 87294
  · exact ⟨87223, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 87364
  · exact ⟨87293, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 87430
  · exact ⟨87359, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 87498
  · exact ⟨87427, by norm_num, by omega, by omega⟩
  · exact ⟨87491, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_35 (n : ℕ) (hlo : 87501 ≤ n) (hhi : n ≤ 90000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 87562
  · exact ⟨87491, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 87630
  · exact ⟨87559, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 87702
  · exact ⟨87631, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 87772
  · exact ⟨87701, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 87838
  · exact ⟨87767, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 87904
  · exact ⟨87833, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 87958
  · exact ⟨87887, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 88030
  · exact ⟨87959, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 88090
  · exact ⟨88019, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 88150
  · exact ⟨88079, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 88200
  · exact ⟨88129, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 88248
  · exact ⟨88177, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 88312
  · exact ⟨88241, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 88372
  · exact ⟨88301, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 88410
  · exact ⟨88339, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 88482
  · exact ⟨88411, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 88542
  · exact ⟨88471, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 88594
  · exact ⟨88523, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 88662
  · exact ⟨88591, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 88734
  · exact ⟨88663, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 88800
  · exact ⟨88729, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 88872
  · exact ⟨88801, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 88944
  · exact ⟨88873, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 89008
  · exact ⟨88937, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 89080
  · exact ⟨89009, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 89142
  · exact ⟨89071, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 89208
  · exact ⟨89137, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 89280
  · exact ⟨89209, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 89344
  · exact ⟨89273, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 89400
  · exact ⟨89329, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 89470
  · exact ⟨89399, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 89530
  · exact ⟨89459, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 89598
  · exact ⟨89527, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 89670
  · exact ⟨89599, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 89742
  · exact ⟨89671, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 89760
  · exact ⟨89689, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 89830
  · exact ⟨89759, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 89892
  · exact ⟨89821, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 89962
  · exact ⟨89891, by norm_num, by omega, by omega⟩
  · exact ⟨89963, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_36 (n : ℕ) (hlo : 90001 ≤ n) (hhi : n ≤ 92500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 90072
  · exact ⟨90001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 90144
  · exact ⟨90073, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 90198
  · exact ⟨90127, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 90270
  · exact ⟨90199, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 90342
  · exact ⟨90271, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 90384
  · exact ⟨90313, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 90450
  · exact ⟨90379, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 90510
  · exact ⟨90439, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 90582
  · exact ⟨90511, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 90654
  · exact ⟨90583, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 90718
  · exact ⟨90647, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 90780
  · exact ⟨90709, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 90820
  · exact ⟨90749, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 90892
  · exact ⟨90821, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 90958
  · exact ⟨90887, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 91018
  · exact ⟨90947, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 91090
  · exact ⟨91019, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 91152
  · exact ⟨91081, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 91224
  · exact ⟨91153, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 91270
  · exact ⟨91199, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 91324
  · exact ⟨91253, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 91380
  · exact ⟨91309, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 91452
  · exact ⟨91381, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 91524
  · exact ⟨91453, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 91584
  · exact ⟨91513, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 91654
  · exact ⟨91583, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 91710
  · exact ⟨91639, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 91782
  · exact ⟨91711, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 91852
  · exact ⟨91781, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 91912
  · exact ⟨91841, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 91980
  · exact ⟨91909, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 92040
  · exact ⟨91969, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 92112
  · exact ⟨92041, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 92182
  · exact ⟨92111, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 92250
  · exact ⟨92179, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 92322
  · exact ⟨92251, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 92388
  · exact ⟨92317, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 92458
  · exact ⟨92387, by norm_num, by omega, by omega⟩
  · exact ⟨92459, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_37 (n : ℕ) (hlo : 92501 ≤ n) (hhi : n ≤ 95000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 92560
  · exact ⟨92489, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 92628
  · exact ⟨92557, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 92698
  · exact ⟨92627, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 92770
  · exact ⟨92699, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 92838
  · exact ⟨92767, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 92902
  · exact ⟨92831, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 92970
  · exact ⟨92899, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 93030
  · exact ⟨92959, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 93072
  · exact ⟨93001, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 93130
  · exact ⟨93059, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 93202
  · exact ⟨93131, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 93270
  · exact ⟨93199, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 93334
  · exact ⟨93263, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 93400
  · exact ⟨93329, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 93454
  · exact ⟨93383, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 93498
  · exact ⟨93427, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 93568
  · exact ⟨93497, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 93634
  · exact ⟨93563, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 93700
  · exact ⟨93629, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 93772
  · exact ⟨93701, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 93834
  · exact ⟨93763, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 93898
  · exact ⟨93827, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 93964
  · exact ⟨93893, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 94020
  · exact ⟨93949, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 94080
  · exact ⟨94009, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 94150
  · exact ⟨94079, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 94222
  · exact ⟨94151, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 94290
  · exact ⟨94219, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 94362
  · exact ⟨94291, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 94422
  · exact ⟨94351, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 94492
  · exact ⟨94421, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 94554
  · exact ⟨94483, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 94618
  · exact ⟨94547, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 94684
  · exact ⟨94613, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 94722
  · exact ⟨94651, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 94794
  · exact ⟨94723, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 94864
  · exact ⟨94793, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 94920
  · exact ⟨94849, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 94978
  · exact ⟨94907, by norm_num, by omega, by omega⟩
  · exact ⟨94961, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_38 (n : ℕ) (hlo : 95001 ≤ n) (hhi : n ≤ 97500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 95070
  · exact ⟨94999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 95142
  · exact ⟨95071, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 95214
  · exact ⟨95143, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 95284
  · exact ⟨95213, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 95350
  · exact ⟨95279, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 95410
  · exact ⟨95339, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 95472
  · exact ⟨95401, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 95542
  · exact ⟨95471, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 95610
  · exact ⟨95539, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 95674
  · exact ⟨95603, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 95722
  · exact ⟨95651, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 95794
  · exact ⟨95723, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 95862
  · exact ⟨95791, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 95928
  · exact ⟨95857, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 96000
  · exact ⟨95929, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 96072
  · exact ⟨96001, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 96130
  · exact ⟨96059, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 96168
  · exact ⟨96097, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 96238
  · exact ⟨96167, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 96304
  · exact ⟨96233, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 96364
  · exact ⟨96293, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 96424
  · exact ⟨96353, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 96490
  · exact ⟨96419, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 96558
  · exact ⟨96487, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 96628
  · exact ⟨96557, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 96672
  · exact ⟨96601, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 96742
  · exact ⟨96671, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 96810
  · exact ⟨96739, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 96870
  · exact ⟨96799, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 96928
  · exact ⟨96857, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 96982
  · exact ⟨96911, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 97050
  · exact ⟨96979, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 97110
  · exact ⟨97039, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 97174
  · exact ⟨97103, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 97242
  · exact ⟨97171, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 97312
  · exact ⟨97241, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 97374
  · exact ⟨97303, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 97444
  · exact ⟨97373, by norm_num, by omega, by omega⟩
  · exact ⟨97441, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_39 (n : ℕ) (hlo : 97501 ≤ n) (hhi : n ≤ 100000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 97572
  · exact ⟨97501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 97642
  · exact ⟨97571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 97684
  · exact ⟨97613, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 97744
  · exact ⟨97673, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 97800
  · exact ⟨97729, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 97860
  · exact ⟨97789, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 97932
  · exact ⟨97861, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 98002
  · exact ⟨97931, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 98058
  · exact ⟨97987, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 98128
  · exact ⟨98057, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 98200
  · exact ⟨98129, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 98250
  · exact ⟨98179, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 98322
  · exact ⟨98251, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 98394
  · exact ⟨98323, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 98460
  · exact ⟨98389, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 98530
  · exact ⟨98459, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 98590
  · exact ⟨98519, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 98644
  · exact ⟨98573, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 98712
  · exact ⟨98641, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 98784
  · exact ⟨98713, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 98850
  · exact ⟨98779, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 98920
  · exact ⟨98849, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 98982
  · exact ⟨98911, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 99052
  · exact ⟨98981, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 99124
  · exact ⟨99053, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 99190
  · exact ⟨99119, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 99262
  · exact ⟨99191, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 99330
  · exact ⟨99259, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 99388
  · exact ⟨99317, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 99448
  · exact ⟨99377, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 99510
  · exact ⟨99439, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 99568
  · exact ⟨99497, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 99634
  · exact ⟨99563, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 99694
  · exact ⟨99623, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 99760
  · exact ⟨99689, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 99832
  · exact ⟨99761, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 99904
  · exact ⟨99833, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 99972
  · exact ⟨99901, by norm_num, by omega, by omega⟩
  · exact ⟨99971, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_40 (n : ℕ) (hlo : 100001 ≤ n) (hhi : n ≤ 102500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 100062
  · exact ⟨99991, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 100128
  · exact ⟨100057, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 100200
  · exact ⟨100129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 100264
  · exact ⟨100193, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 100308
  · exact ⟨100237, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 100368
  · exact ⟨100297, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 100434
  · exact ⟨100363, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 100488
  · exact ⟨100417, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 100554
  · exact ⟨100483, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 100620
  · exact ⟨100549, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 100692
  · exact ⟨100621, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 100764
  · exact ⟨100693, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 100818
  · exact ⟨100747, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 100882
  · exact ⟨100811, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 100924
  · exact ⟨100853, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 100984
  · exact ⟨100913, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 101052
  · exact ⟨100981, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 101122
  · exact ⟨101051, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 101190
  · exact ⟨101119, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 101254
  · exact ⟨101183, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 101292
  · exact ⟨101221, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 101364
  · exact ⟨101293, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 101434
  · exact ⟨101363, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 101500
  · exact ⟨101429, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 101572
  · exact ⟨101501, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 101644
  · exact ⟨101573, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 101712
  · exact ⟨101641, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 101772
  · exact ⟨101701, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 101842
  · exact ⟨101771, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 101910
  · exact ⟨101839, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 101962
  · exact ⟨101891, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 102034
  · exact ⟨101963, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 102102
  · exact ⟨102031, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 102174
  · exact ⟨102103, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 102232
  · exact ⟨102161, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 102304
  · exact ⟨102233, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 102372
  · exact ⟨102301, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 102438
  · exact ⟨102367, by norm_num, by omega, by omega⟩
  · exact ⟨102437, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_41 (n : ℕ) (hlo : 102501 ≤ n) (hhi : n ≤ 105000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 102570
  · exact ⟨102499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 102634
  · exact ⟨102563, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 102682
  · exact ⟨102611, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 102750
  · exact ⟨102679, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 102772
  · exact ⟨102701, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 102840
  · exact ⟨102769, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 102912
  · exact ⟨102841, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 102984
  · exact ⟨102913, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 103054
  · exact ⟨102983, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 103120
  · exact ⟨103049, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 103170
  · exact ⟨103099, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 103242
  · exact ⟨103171, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 103308
  · exact ⟨103237, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 103378
  · exact ⟨103307, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 103428
  · exact ⟨103357, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 103494
  · exact ⟨103423, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 103554
  · exact ⟨103483, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 103624
  · exact ⟨103553, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 103690
  · exact ⟨103619, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 103758
  · exact ⟨103687, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 103794
  · exact ⟨103723, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 103858
  · exact ⟨103787, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 103914
  · exact ⟨103843, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 103984
  · exact ⟨103913, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 104052
  · exact ⟨103981, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 104124
  · exact ⟨104053, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 104194
  · exact ⟨104123, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 104254
  · exact ⟨104183, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 104314
  · exact ⟨104243, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 104382
  · exact ⟨104311, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 104454
  · exact ⟨104383, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 104488
  · exact ⟨104417, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 104550
  · exact ⟨104479, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 104622
  · exact ⟨104551, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 104694
  · exact ⟨104623, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 104764
  · exact ⟨104693, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 104832
  · exact ⟨104761, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 104902
  · exact ⟨104831, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 104962
  · exact ⟨104891, by norm_num, by omega, by omega⟩
  · exact ⟨104959, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_42 (n : ℕ) (hlo : 105001 ≤ n) (hhi : n ≤ 107500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 105070
  · exact ⟨104999, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 105142
  · exact ⟨105071, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 105214
  · exact ⟨105143, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 105282
  · exact ⟨105211, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 105348
  · exact ⟨105277, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 105412
  · exact ⟨105341, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 105478
  · exact ⟨105407, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 105538
  · exact ⟨105467, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 105604
  · exact ⟨105533, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 105672
  · exact ⟨105601, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 105744
  · exact ⟨105673, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 105804
  · exact ⟨105733, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 105840
  · exact ⟨105769, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 105900
  · exact ⟨105829, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 105970
  · exact ⟨105899, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 106042
  · exact ⟨105971, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 106104
  · exact ⟨106033, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 106174
  · exact ⟨106103, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 106234
  · exact ⟨106163, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 106290
  · exact ⟨106219, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 106362
  · exact ⟨106291, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 106434
  · exact ⟨106363, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 106504
  · exact ⟨106433, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 106572
  · exact ⟨106501, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 106614
  · exact ⟨106543, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 106662
  · exact ⟨106591, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 106734
  · exact ⟨106663, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 106798
  · exact ⟨106727, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 106858
  · exact ⟨106787, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 106930
  · exact ⟨106859, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 106992
  · exact ⟨106921, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 107064
  · exact ⟨106993, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 107128
  · exact ⟨107057, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 107194
  · exact ⟨107123, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 107254
  · exact ⟨107183, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 107322
  · exact ⟨107251, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 107394
  · exact ⟨107323, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 107448
  · exact ⟨107377, by norm_num, by omega, by omega⟩
  · exact ⟨107449, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_43 (n : ℕ) (hlo : 107501 ≤ n) (hhi : n ≤ 110000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 107544
  · exact ⟨107473, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 107580
  · exact ⟨107509, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 107652
  · exact ⟨107581, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 107718
  · exact ⟨107647, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 107790
  · exact ⟨107719, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 107862
  · exact ⟨107791, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 107928
  · exact ⟨107857, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 107998
  · exact ⟨107927, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 108070
  · exact ⟨107999, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 108132
  · exact ⟨108061, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 108202
  · exact ⟨108131, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 108274
  · exact ⟨108203, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 108342
  · exact ⟨108271, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 108414
  · exact ⟨108343, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 108484
  · exact ⟨108413, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 108534
  · exact ⟨108463, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 108604
  · exact ⟨108533, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 108658
  · exact ⟨108587, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 108720
  · exact ⟨108649, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 108780
  · exact ⟨108709, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 108840
  · exact ⟨108769, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 108898
  · exact ⟨108827, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 108964
  · exact ⟨108893, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 109032
  · exact ⟨108961, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 109084
  · exact ⟨109013, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 109144
  · exact ⟨109073, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 109212
  · exact ⟨109141, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 109282
  · exact ⟨109211, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 109350
  · exact ⟨109279, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 109402
  · exact ⟨109331, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 109468
  · exact ⟨109397, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 109540
  · exact ⟨109469, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 109612
  · exact ⟨109541, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 109680
  · exact ⟨109609, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 109744
  · exact ⟨109673, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 109812
  · exact ⟨109741, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 109878
  · exact ⟨109807, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 109944
  · exact ⟨109873, by norm_num, by omega, by omega⟩
  · exact ⟨109943, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_44 (n : ℕ) (hlo : 110001 ≤ n) (hhi : n ≤ 112500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 110058
  · exact ⟨109987, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 110130
  · exact ⟨110059, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 110200
  · exact ⟨110129, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 110254
  · exact ⟨110183, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 110322
  · exact ⟨110251, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 110394
  · exact ⟨110323, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 110430
  · exact ⟨110359, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 110502
  · exact ⟨110431, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 110574
  · exact ⟨110503, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 110644
  · exact ⟨110573, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 110712
  · exact ⟨110641, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 110782
  · exact ⟨110711, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 110848
  · exact ⟨110777, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 110920
  · exact ⟨110849, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 110992
  · exact ⟨110921, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 111060
  · exact ⟨110989, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 111124
  · exact ⟨111053, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 111192
  · exact ⟨111121, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 111262
  · exact ⟨111191, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 111334
  · exact ⟨111263, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 111394
  · exact ⟨111323, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 111444
  · exact ⟨111373, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 111514
  · exact ⟨111443, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 111580
  · exact ⟨111509, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 111652
  · exact ⟨111581, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 111724
  · exact ⟨111653, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 111792
  · exact ⟨111721, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 111862
  · exact ⟨111791, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 111934
  · exact ⟨111863, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 111990
  · exact ⟨111919, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 112048
  · exact ⟨111977, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 112102
  · exact ⟨112031, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 112174
  · exact ⟨112103, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 112234
  · exact ⟨112163, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 112294
  · exact ⟨112223, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 112362
  · exact ⟨112291, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 112434
  · exact ⟨112363, by norm_num, by omega, by omega⟩
  · exact ⟨112429, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_45 (n : ℕ) (hlo : 112501 ≤ n) (hhi : n ≤ 115000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 112572
  · exact ⟨112501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 112644
  · exact ⟨112573, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 112714
  · exact ⟨112643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 112762
  · exact ⟨112691, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 112830
  · exact ⟨112759, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 112902
  · exact ⟨112831, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 112972
  · exact ⟨112901, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 113038
  · exact ⟨112967, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 113110
  · exact ⟨113039, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 113182
  · exact ⟨113111, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 113248
  · exact ⟨113177, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 113304
  · exact ⟨113233, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 113358
  · exact ⟨113287, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 113430
  · exact ⟨113359, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 113488
  · exact ⟨113417, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 113560
  · exact ⟨113489, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 113628
  · exact ⟨113557, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 113694
  · exact ⟨113623, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 113754
  · exact ⟨113683, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 113820
  · exact ⟨113749, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 113890
  · exact ⟨113819, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 113962
  · exact ⟨113891, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 114034
  · exact ⟨113963, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 114102
  · exact ⟨114031, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 114160
  · exact ⟨114089, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 114232
  · exact ⟨114161, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 114300
  · exact ⟨114229, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 114370
  · exact ⟨114299, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 114442
  · exact ⟨114371, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 114490
  · exact ⟨114419, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 114558
  · exact ⟨114487, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 114624
  · exact ⟨114553, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 114688
  · exact ⟨114617, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 114760
  · exact ⟨114689, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 114832
  · exact ⟨114761, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 114904
  · exact ⟨114833, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 114972
  · exact ⟨114901, by norm_num, by omega, by omega⟩
  · exact ⟨114973, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_46 (n : ℕ) (hlo : 115001 ≤ n) (hhi : n ≤ 117500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 115072
  · exact ⟨115001, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 115138
  · exact ⟨115067, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 115204
  · exact ⟨115133, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 115272
  · exact ⟨115201, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 115330
  · exact ⟨115259, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 115402
  · exact ⟨115331, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 115470
  · exact ⟨115399, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 115542
  · exact ⟨115471, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 115594
  · exact ⟨115523, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 115660
  · exact ⟨115589, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 115728
  · exact ⟨115657, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 115798
  · exact ⟨115727, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 115864
  · exact ⟨115793, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 115932
  · exact ⟨115861, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 116004
  · exact ⟨115933, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 116058
  · exact ⟨115987, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 116118
  · exact ⟨116047, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 116184
  · exact ⟨116113, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 116248
  · exact ⟨116177, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 116314
  · exact ⟨116243, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 116364
  · exact ⟨116293, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 116430
  · exact ⟨116359, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 116494
  · exact ⟨116423, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 116562
  · exact ⟨116491, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 116620
  · exact ⟨116549, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 116664
  · exact ⟨116593, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 116734
  · exact ⟨116663, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 116802
  · exact ⟨116731, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 116874
  · exact ⟨116803, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 116938
  · exact ⟨116867, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 117004
  · exact ⟨116933, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 117064
  · exact ⟨116993, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 117124
  · exact ⟨117053, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 117190
  · exact ⟨117119, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 117262
  · exact ⟨117191, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 117330
  · exact ⟨117259, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 117402
  · exact ⟨117331, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 117460
  · exact ⟨117389, by norm_num, by omega, by omega⟩
  · exact ⟨117443, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_47 (n : ℕ) (hlo : 117501 ≤ n) (hhi : n ≤ 120000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 117570
  · exact ⟨117499, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 117642
  · exact ⟨117571, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 117714
  · exact ⟨117643, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 117780
  · exact ⟨117709, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 117850
  · exact ⟨117779, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 117922
  · exact ⟨117851, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 117988
  · exact ⟨117917, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 118060
  · exact ⟨117989, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 118132
  · exact ⟨118061, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 118198
  · exact ⟨118127, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 118260
  · exact ⟨118189, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 118330
  · exact ⟨118259, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 118368
  · exact ⟨118297, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 118440
  · exact ⟨118369, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 118500
  · exact ⟨118429, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 118564
  · exact ⟨118493, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 118620
  · exact ⟨118549, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 118692
  · exact ⟨118621, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 118762
  · exact ⟨118691, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 118828
  · exact ⟨118757, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 118890
  · exact ⟨118819, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 118962
  · exact ⟨118891, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 119002
  · exact ⟨118931, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 119044
  · exact ⟨118973, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 119110
  · exact ⟨119039, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 119178
  · exact ⟨119107, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 119250
  · exact ⟨119179, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 119314
  · exact ⟨119243, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 119382
  · exact ⟨119311, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 119434
  · exact ⟨119363, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 119500
  · exact ⟨119429, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 119560
  · exact ⟨119489, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 119628
  · exact ⟨119557, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 119698
  · exact ⟨119627, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 119770
  · exact ⟨119699, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 119842
  · exact ⟨119771, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 119910
  · exact ⟨119839, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 119962
  · exact ⟨119891, by norm_num, by omega, by omega⟩
  · exact ⟨119963, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_48 (n : ℕ) (hlo : 120001 ≤ n) (hhi : n ≤ 122500) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 120064
  · exact ⟨119993, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 120120
  · exact ⟨120049, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 120192
  · exact ⟨120121, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 120264
  · exact ⟨120193, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 120318
  · exact ⟨120247, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 120390
  · exact ⟨120319, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 120462
  · exact ⟨120391, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 120502
  · exact ⟨120431, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 120574
  · exact ⟨120503, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 120640
  · exact ⟨120569, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 120712
  · exact ⟨120641, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 120784
  · exact ⟨120713, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 120850
  · exact ⟨120779, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 120922
  · exact ⟨120851, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 120990
  · exact ⟨120919, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 121048
  · exact ⟨120977, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 121110
  · exact ⟨121039, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 121152
  · exact ⟨121081, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 121222
  · exact ⟨121151, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 121260
  · exact ⟨121189, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 121330
  · exact ⟨121259, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 121398
  · exact ⟨121327, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 121450
  · exact ⟨121379, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 121518
  · exact ⟨121447, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 121578
  · exact ⟨121507, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 121650
  · exact ⟨121579, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 121708
  · exact ⟨121637, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 121768
  · exact ⟨121697, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 121834
  · exact ⟨121763, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 121860
  · exact ⟨121789, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 121924
  · exact ⟨121853, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 121992
  · exact ⟨121921, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 122064
  · exact ⟨121993, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 122124
  · exact ⟨122053, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 122188
  · exact ⟨122117, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 122244
  · exact ⟨122173, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 122302
  · exact ⟨122231, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 122370
  · exact ⟨122299, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 122434
  · exact ⟨122363, by norm_num, by omega, by omega⟩
  by_cases h39 : n ≤ 122472
  · exact ⟨122401, by norm_num, by omega, by omega⟩
  · exact ⟨122471, by norm_num, by omega, by omega⟩

set_option maxHeartbeats 800000 in
lemma exists_prime_sub_72_block_49 (n : ℕ) (hlo : 122501 ≤ n) (hhi : n ≤ 125000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 122572
  · exact ⟨122501, by norm_num, by omega, by omega⟩
  by_cases h1 : n ≤ 122632
  · exact ⟨122561, by norm_num, by omega, by omega⟩
  by_cases h2 : n ≤ 122682
  · exact ⟨122611, by norm_num, by omega, by omega⟩
  by_cases h3 : n ≤ 122734
  · exact ⟨122663, by norm_num, by omega, by omega⟩
  by_cases h4 : n ≤ 122790
  · exact ⟨122719, by norm_num, by omega, by omega⟩
  by_cases h5 : n ≤ 122860
  · exact ⟨122789, by norm_num, by omega, by omega⟩
  by_cases h6 : n ≤ 122932
  · exact ⟨122861, by norm_num, by omega, by omega⟩
  by_cases h7 : n ≤ 123000
  · exact ⟨122929, by norm_num, by omega, by omega⟩
  by_cases h8 : n ≤ 123072
  · exact ⟨123001, by norm_num, by omega, by omega⟩
  by_cases h9 : n ≤ 123130
  · exact ⟨123059, by norm_num, by omega, by omega⟩
  by_cases h10 : n ≤ 123198
  · exact ⟨123127, by norm_num, by omega, by omega⟩
  by_cases h11 : n ≤ 123262
  · exact ⟨123191, by norm_num, by omega, by omega⟩
  by_cases h12 : n ≤ 123330
  · exact ⟨123259, by norm_num, by omega, by omega⟩
  by_cases h13 : n ≤ 123394
  · exact ⟨123323, by norm_num, by omega, by omega⟩
  by_cases h14 : n ≤ 123450
  · exact ⟨123379, by norm_num, by omega, by omega⟩
  by_cases h15 : n ≤ 123520
  · exact ⟨123449, by norm_num, by omega, by omega⟩
  by_cases h16 : n ≤ 123588
  · exact ⟨123517, by norm_num, by omega, by omega⟩
  by_cases h17 : n ≤ 123654
  · exact ⟨123583, by norm_num, by omega, by omega⟩
  by_cases h18 : n ≤ 123724
  · exact ⟨123653, by norm_num, by omega, by omega⟩
  by_cases h19 : n ≤ 123790
  · exact ⟨123719, by norm_num, by omega, by omega⟩
  by_cases h20 : n ≤ 123862
  · exact ⟨123791, by norm_num, by omega, by omega⟩
  by_cases h21 : n ≤ 123934
  · exact ⟨123863, by norm_num, by omega, by omega⟩
  by_cases h22 : n ≤ 124002
  · exact ⟨123931, by norm_num, by omega, by omega⟩
  by_cases h23 : n ≤ 124072
  · exact ⟨124001, by norm_num, by omega, by omega⟩
  by_cases h24 : n ≤ 124138
  · exact ⟨124067, by norm_num, by omega, by omega⟩
  by_cases h25 : n ≤ 124210
  · exact ⟨124139, by norm_num, by omega, by omega⟩
  by_cases h26 : n ≤ 124270
  · exact ⟨124199, by norm_num, by omega, by omega⟩
  by_cases h27 : n ≤ 124320
  · exact ⟨124249, by norm_num, by omega, by omega⟩
  by_cases h28 : n ≤ 124380
  · exact ⟨124309, by norm_num, by omega, by omega⟩
  by_cases h29 : n ≤ 124438
  · exact ⟨124367, by norm_num, by omega, by omega⟩
  by_cases h30 : n ≤ 124504
  · exact ⟨124433, by norm_num, by omega, by omega⟩
  by_cases h31 : n ≤ 124564
  · exact ⟨124493, by norm_num, by omega, by omega⟩
  by_cases h32 : n ≤ 124632
  · exact ⟨124561, by norm_num, by omega, by omega⟩
  by_cases h33 : n ≤ 124704
  · exact ⟨124633, by norm_num, by omega, by omega⟩
  by_cases h34 : n ≤ 124774
  · exact ⟨124703, by norm_num, by omega, by omega⟩
  by_cases h35 : n ≤ 124842
  · exact ⟨124771, by norm_num, by omega, by omega⟩
  by_cases h36 : n ≤ 124894
  · exact ⟨124823, by norm_num, by omega, by omega⟩
  by_cases h37 : n ≤ 124924
  · exact ⟨124853, by norm_num, by omega, by omega⟩
  by_cases h38 : n ≤ 124990
  · exact ⟨124919, by norm_num, by omega, by omega⟩
  · exact ⟨124991, by norm_num, by omega, by omega⟩

lemma exists_prime_sub_72_le_of_le_125000 (n : ℕ) (hlo : 144 ≤ n)
    (hhi : n ≤ 125000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n := by
  by_cases h0 : n ≤ 2500
  · exact exists_prime_sub_72_block_0 n (by omega) h0
  by_cases h1 : n ≤ 5000
  · exact exists_prime_sub_72_block_1 n (by omega) h1
  by_cases h2 : n ≤ 7500
  · exact exists_prime_sub_72_block_2 n (by omega) h2
  by_cases h3 : n ≤ 10000
  · exact exists_prime_sub_72_block_3 n (by omega) h3
  by_cases h4 : n ≤ 12500
  · exact exists_prime_sub_72_block_4 n (by omega) h4
  by_cases h5 : n ≤ 15000
  · exact exists_prime_sub_72_block_5 n (by omega) h5
  by_cases h6 : n ≤ 17500
  · exact exists_prime_sub_72_block_6 n (by omega) h6
  by_cases h7 : n ≤ 20000
  · exact exists_prime_sub_72_block_7 n (by omega) h7
  by_cases h8 : n ≤ 22500
  · exact exists_prime_sub_72_block_8 n (by omega) h8
  by_cases h9 : n ≤ 25000
  · exact exists_prime_sub_72_block_9 n (by omega) h9
  by_cases h10 : n ≤ 27500
  · exact exists_prime_sub_72_block_10 n (by omega) h10
  by_cases h11 : n ≤ 30000
  · exact exists_prime_sub_72_block_11 n (by omega) h11
  by_cases h12 : n ≤ 32500
  · exact exists_prime_sub_72_block_12 n (by omega) h12
  by_cases h13 : n ≤ 35000
  · exact exists_prime_sub_72_block_13 n (by omega) h13
  by_cases h14 : n ≤ 37500
  · exact exists_prime_sub_72_block_14 n (by omega) h14
  by_cases h15 : n ≤ 40000
  · exact exists_prime_sub_72_block_15 n (by omega) h15
  by_cases h16 : n ≤ 42500
  · exact exists_prime_sub_72_block_16 n (by omega) h16
  by_cases h17 : n ≤ 45000
  · exact exists_prime_sub_72_block_17 n (by omega) h17
  by_cases h18 : n ≤ 47500
  · exact exists_prime_sub_72_block_18 n (by omega) h18
  by_cases h19 : n ≤ 50000
  · exact exists_prime_sub_72_block_19 n (by omega) h19
  by_cases h20 : n ≤ 52500
  · exact exists_prime_sub_72_block_20 n (by omega) h20
  by_cases h21 : n ≤ 55000
  · exact exists_prime_sub_72_block_21 n (by omega) h21
  by_cases h22 : n ≤ 57500
  · exact exists_prime_sub_72_block_22 n (by omega) h22
  by_cases h23 : n ≤ 60000
  · exact exists_prime_sub_72_block_23 n (by omega) h23
  by_cases h24 : n ≤ 62500
  · exact exists_prime_sub_72_block_24 n (by omega) h24
  by_cases h25 : n ≤ 65000
  · exact exists_prime_sub_72_block_25 n (by omega) h25
  by_cases h26 : n ≤ 67500
  · exact exists_prime_sub_72_block_26 n (by omega) h26
  by_cases h27 : n ≤ 70000
  · exact exists_prime_sub_72_block_27 n (by omega) h27
  by_cases h28 : n ≤ 72500
  · exact exists_prime_sub_72_block_28 n (by omega) h28
  by_cases h29 : n ≤ 75000
  · exact exists_prime_sub_72_block_29 n (by omega) h29
  by_cases h30 : n ≤ 77500
  · exact exists_prime_sub_72_block_30 n (by omega) h30
  by_cases h31 : n ≤ 80000
  · exact exists_prime_sub_72_block_31 n (by omega) h31
  by_cases h32 : n ≤ 82500
  · exact exists_prime_sub_72_block_32 n (by omega) h32
  by_cases h33 : n ≤ 85000
  · exact exists_prime_sub_72_block_33 n (by omega) h33
  by_cases h34 : n ≤ 87500
  · exact exists_prime_sub_72_block_34 n (by omega) h34
  by_cases h35 : n ≤ 90000
  · exact exists_prime_sub_72_block_35 n (by omega) h35
  by_cases h36 : n ≤ 92500
  · exact exists_prime_sub_72_block_36 n (by omega) h36
  by_cases h37 : n ≤ 95000
  · exact exists_prime_sub_72_block_37 n (by omega) h37
  by_cases h38 : n ≤ 97500
  · exact exists_prime_sub_72_block_38 n (by omega) h38
  by_cases h39 : n ≤ 100000
  · exact exists_prime_sub_72_block_39 n (by omega) h39
  by_cases h40 : n ≤ 102500
  · exact exists_prime_sub_72_block_40 n (by omega) h40
  by_cases h41 : n ≤ 105000
  · exact exists_prime_sub_72_block_41 n (by omega) h41
  by_cases h42 : n ≤ 107500
  · exact exists_prime_sub_72_block_42 n (by omega) h42
  by_cases h43 : n ≤ 110000
  · exact exists_prime_sub_72_block_43 n (by omega) h43
  by_cases h44 : n ≤ 112500
  · exact exists_prime_sub_72_block_44 n (by omega) h44
  by_cases h45 : n ≤ 115000
  · exact exists_prime_sub_72_block_45 n (by omega) h45
  by_cases h46 : n ≤ 117500
  · exact exists_prime_sub_72_block_46 n (by omega) h46
  by_cases h47 : n ≤ 120000
  · exact exists_prime_sub_72_block_47 n (by omega) h47
  by_cases h48 : n ≤ 122500
  · exact exists_prime_sub_72_block_48 n (by omega) h48
  · exact exists_prime_sub_72_block_49 n (by omega) hhi

lemma nat_le_600_of_sq_le_small {n i : ℕ} (hi49 : 49 ≤ i) (hi72 : i < 72)
    (hn_sq : n ^ 2 ≤ i ^ 3) : n ≤ 600 := by
  by_contra hnot
  have hn601 : 601 ≤ n := by omega
  have hn_sq_ge : 601 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn601 2
  have hi_le : i ^ 3 ≤ 71 ^ 3 := Nat.pow_le_pow_left (by omega : i ≤ 71) 3
  have hnum : 71 ^ 3 < 601 ^ 2 := by norm_num
  omega

lemma nat_le_125000_of_sq_le_index_lt_2500 {n i : ℕ} (hi2500 : i < 2500)
    (hn_sq : n ^ 2 ≤ i ^ 3) : n ≤ 125000 := by
  by_contra hnot
  have hn : 125001 ≤ n := by omega
  have hn_sq_ge : 125001 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have hi_le : i ^ 3 ≤ 2499 ^ 3 := Nat.pow_le_pow_left (by omega : i ≤ 2499) 3
  have hnum : 2499 ^ 3 < 125001 ^ 2 := by norm_num
  omega

lemma nat_le_125000_of_cube_le_index_lt_4840 {n i : ℕ} (hi4840 : i < 4840)
    (hn_cube : n ^ 3 ≤ i ^ 4) : n ≤ 125000 := by
  by_contra hnot
  have hn : 125001 ≤ n := by omega
  have hn_cube_ge : 125001 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  have hi_le : i ^ 4 ≤ 4839 ^ 4 := Nat.pow_le_pow_left (by omega : i ≤ 4839) 4
  have hnum : 4839 ^ 4 < 125001 ^ 3 := by norm_num
  omega

theorem sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty
    (n i : ℕ) (hi49 : 49 ≤ i) (hi_lt : i < 4840) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_cases hi72 : i < 72
  · by_cases hcube : i ^ 3 < n ^ 2
    · exact sylvester_schur_of_cube_lt_square n i hi49 hi_half hcube
    · have hn_sq : n ^ 2 ≤ i ^ 3 := Nat.le_of_not_gt hcube
      have hn_le : n ≤ 600 := nat_le_600_of_sq_le_small hi49 hi72 hn_sq
      obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_sub_49_le_of_le_600 n (by omega) hn_le
      exact sylvester_schur_of_prime_in_top_interval n i hi_half ⟨p, hp, by omega, hpn⟩
  · have hi72le : 72 ≤ i := by omega
    by_cases hi2500 : i < 2500
    · by_cases hcube : i ^ 3 < n ^ 2
      · exact sylvester_schur_of_cube_lt_square n i hi49 hi_half hcube
      · have hn_sq : n ^ 2 ≤ i ^ 3 := Nat.le_of_not_gt hcube
        have hn_le : n ≤ 125000 := nat_le_125000_of_sq_le_index_lt_2500 hi2500 hn_sq
        obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_sub_72_le_of_le_125000 n (by omega) hn_le
        exact sylvester_schur_of_prime_in_top_interval n i hi_half ⟨p, hp, by omega, hpn⟩
    · have hi2500le : 2500 ≤ i := by omega
      by_cases hfourth : i ^ 4 < n ^ 3
      · exact sylvester_schur_of_fourth_lt_cube n i hi2500le hi_half hfourth
      · have hn_cube : n ^ 3 ≤ i ^ 4 := Nat.le_of_not_gt hfourth
        have hn_le : n ≤ 125000 := nat_le_125000_of_cube_le_index_lt_4840 hi_lt hn_cube
        obtain ⟨p, hp, hnp, hpn⟩ := exists_prime_sub_72_le_of_le_125000 n (by omega) hn_le
        exact sylvester_schur_of_prime_in_top_interval n i hi_half ⟨p, hp, by omega, hpn⟩

theorem sylvester_schur
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  by_cases hi48 : i ≤ 48
  · exact sylvester_schur_of_index_le_forty_eight n i hi hi_half hi48
  by_cases hi4840 : 4840 ≤ i
  · exact sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty n i hi4840 hi_half
  exact sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty n i
    (by omega) (by omega) hi_half

theorem sylvester_schur_current_frontier
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hcovered :
      i ≤ 48 ∨ 4840 ≤ i ∨ 8 ≤ i ∧ i ^ 2 < n ∨ 49 ≤ i ∧ i ^ 3 < n ^ 2 ∨
        2500 ≤ i ∧ i ^ 4 < n ^ 3 ∨
        4410 ≤ i ∧ 2 * n ≤ 5 * i ∨
        4 ≤ i ∧ i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i ∨
        i.factorial * (n ^ n.sqrt * 4 ^ i) < (n - i + 1) ^ i ∨
        4 ≤ i ∧ i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i ∨
        4 ≤ i ∧ i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i)) < n ^ i * 4 ^ i ∨
        n = 2 * i ∨ n = 2 * i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i := by
  rcases hcovered with hi48 | hcovered
  · exact sylvester_schur_of_index_le_forty_eight n i hi hi_half hi48
  rcases hcovered with hi4840 | hcovered
  · exact sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty n i hi4840 hi_half
  rcases hcovered with ⟨hi8, hn_large⟩ | hcovered
  · exact sylvester_schur_of_superquadratic_top n i hi8 hi_half hn_large
  rcases hcovered with ⟨hi49, hn_large⟩ | hcovered
  · exact sylvester_schur_of_cube_lt_square n i hi49 hi_half hn_large
  rcases hcovered with ⟨hi2500, hn_large⟩ | hcovered
  · exact sylvester_schur_of_fourth_lt_cube n i hi2500 hi_half hn_large
  rcases hcovered with ⟨hi4410, hn_le⟩ | hcovered
  · exact sylvester_schur_of_central_five_halves n i hi4410 hi_half hn_le
  rcases hcovered with ⟨hi4, hgap⟩ | hcovered
  · exact sylvester_schur_of_central_gap n i hi4 hi_half hgap
  rcases hcovered with hgap | hcovered
  · exact sylvester_schur_of_factorial_gap n i hi hi_half hgap
  rcases hcovered with ⟨hi4, hgap⟩ | hcovered
  · exact sylvester_schur_of_scaled_central_power_gap n i hi4 hi_half hgap
  rcases hcovered with ⟨hi4, hgap⟩ | hn_twice | hn_twice_one
  · exact sylvester_schur_of_scaled_central_gap n i hi4 hi_half hgap
  · exact sylvester_schur_of_twice n i hi hn_twice
  · exact sylvester_schur_of_twice_add_one n i hi hn_twice_one

theorem sylvester_schur_of_interval_threshold
    (hthreshold : SylvesterSchurIntervalThreshold)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_interval (sylvester_schur_interval_of_threshold hthreshold) n i hi hi_half

theorem sylvester_schur_of_small_start
    (hsmall : SylvesterSchurSmallStart)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i :=
  sylvester_schur_of_interval (sylvester_schur_interval_of_small_start hsmall) n i hi hi_half

end Erdos699Formalization
