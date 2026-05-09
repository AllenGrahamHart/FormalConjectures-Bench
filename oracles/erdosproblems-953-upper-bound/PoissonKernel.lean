import FormalConjecturesBench.CircleBessel
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section

open scoped BigOperators

namespace Erdos953Formalization

/-- Positive weights in the Poisson-Bessel kernel, indexed from `k = n + 1`. -/
noncomputable def weight (s : ℝ) (n : ℕ) : ℝ :=
  let k : ℝ := ((n + 1 : ℕ) : ℝ)
  (k + 2 * s * k ^ 2) * Real.exp (-s * k)

lemma weight_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ weight s n := by
  unfold weight
  positivity

lemma abs_weight_mul_J0_le {s : ℝ} (hs : 0 ≤ s) (n : ℕ) (t : ℝ) :
    |weight s n *
      CircleBessel.J0 (2 * Real.pi * (((n + 1 : ℕ) : ℝ)) * t)| ≤ weight s n := by
  rw [abs_mul, abs_of_nonneg (weight_nonneg hs n)]
  exact mul_le_of_le_one_right (weight_nonneg hs n) (CircleBessel.abs_J0_le_one _)

lemma exp_neg_mul_nat_eq_pow (s : ℝ) (n : ℕ) :
    Real.exp (-s * (n : ℝ)) = Real.exp (-s) ^ n := by
  rw [show -s * (n : ℝ) = (n : ℝ) * (-s) by ring, Real.exp_nat_mul]

lemma one_sub_exp_neg_ge_half {s : ℝ} (hspos : 0 < s) (hsle : s ≤ 1 / 2) :
    s / 2 ≤ 1 - Real.exp (-s) := by
  have habsarg : |(-s)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hspos.le]
    linarith
  have h := Real.abs_exp_sub_one_sub_id_le (x := -s) habsarg
  have hupper : Real.exp (-s) - 1 - (-s) ≤ s ^ 2 := by
    simpa using (abs_le.1 h).2
  have hs_sq_le_half : s ^ 2 ≤ s / 2 := by
    nlinarith [hspos.le, hsle]
  linarith

lemma choose_two_majorizes_sq (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ 2) ≤ 2 * (((n + 2).choose 2 : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two]
  norm_num
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  nlinarith

lemma weight_le_diag_majorant {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    weight s n ≤
      ((((n + 1).choose 1 : ℕ) : ℝ) +
        4 * s * (((n + 2).choose 2 : ℕ) : ℝ)) * Real.exp (-s) ^ n := by
  let r := Real.exp (-s)
  have hr_nonneg : 0 ≤ r := Real.exp_nonneg _
  have hr_le_one : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hk_nonneg : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  have hrpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr_nonneg n
  have hrpow_succ_le : r ^ (n + 1) ≤ r ^ n := by
    rw [pow_succ]
    calc
      r ^ n * r ≤ r ^ n * 1 := mul_le_mul_of_nonneg_left hr_le_one hrpow_nonneg
      _ = r ^ n := by ring
  have hfirst :
      (((n + 1 : ℕ) : ℝ)) * r ^ (n + 1) ≤
        (((n + 1 : ℕ) : ℝ)) * r ^ n :=
    mul_le_mul_of_nonneg_left hrpow_succ_le hk_nonneg
  have hsq_choose :
      (((n + 1 : ℕ) : ℝ) ^ 2) * r ^ (n + 1) ≤
        (2 * (((n + 2).choose 2 : ℕ) : ℝ)) * r ^ n := by
    have hsq := choose_two_majorizes_sq n
    calc
      (((n + 1 : ℕ) : ℝ) ^ 2) * r ^ (n + 1) ≤
          (((n + 1 : ℕ) : ℝ) ^ 2) * r ^ n :=
        mul_le_mul_of_nonneg_left hrpow_succ_le (sq_nonneg _)
      _ ≤ (2 * (((n + 2).choose 2 : ℕ) : ℝ)) * r ^ n :=
        mul_le_mul_of_nonneg_right hsq hrpow_nonneg
  have hsecond :
      2 * s * (((n + 1 : ℕ) : ℝ) ^ 2 * r ^ (n + 1)) ≤
        4 * s * (((n + 2).choose 2 : ℕ) : ℝ) * r ^ n := by
    calc
      2 * s * (((n + 1 : ℕ) : ℝ) ^ 2 * r ^ (n + 1)) ≤
          2 * s * ((2 * (((n + 2).choose 2 : ℕ) : ℝ)) * r ^ n) := by
        exact mul_le_mul_of_nonneg_left hsq_choose (mul_nonneg (by norm_num) hs)
      _ = 4 * s * (((n + 2).choose 2 : ℕ) : ℝ) * r ^ n := by ring
  unfold weight
  change (((n + 1 : ℕ) : ℝ) + 2 * s * ((n + 1 : ℕ) : ℝ) ^ 2) *
      Real.exp (-s * ((n + 1 : ℕ) : ℝ)) ≤ _
  rw [exp_neg_mul_nat_eq_pow]
  change ((((n + 1 : ℕ) : ℝ) + 2 * s * ((n + 1 : ℕ) : ℝ) ^ 2) *
      r ^ (n + 1) ≤
        ((((n + 1).choose 1 : ℕ) : ℝ) +
          4 * s * (((n + 2).choose 2 : ℕ) : ℝ)) * r ^ n)
  rw [Nat.choose_one_right]
  nlinarith

lemma summable_weight {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => weight s n) := by
  have h1raw : Summable fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ 1) * Real.exp (-s * (((n + 1 : ℕ) : ℝ))) := by
    exact (summable_nat_add_iff (f := fun n : ℕ =>
      ((n : ℝ) ^ 1) * Real.exp (-s * (n : ℝ))) 1).2
        (Real.summable_pow_mul_exp_neg_nat_mul 1 hs)
  have h1 : Summable fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)) * Real.exp (-s * (((n + 1 : ℕ) : ℝ))) := by
    simpa using h1raw
  have h2 : Summable fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-s * (((n + 1 : ℕ) : ℝ))) := by
    exact (summable_nat_add_iff (f := fun n : ℕ =>
      ((n : ℝ) ^ 2) * Real.exp (-s * (n : ℝ))) 1).2
        (Real.summable_pow_mul_exp_neg_nat_mul 2 hs)
  have hsum : Summable fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)) * Real.exp (-s * (((n + 1 : ℕ) : ℝ))) +
        (2 * s) * ((((n + 1 : ℕ) : ℝ) ^ 2) *
          Real.exp (-s * (((n + 1 : ℕ) : ℝ)))) :=
    h1.add (h2.mul_left (2 * s))
  exact hsum.congr (fun n => by
    unfold weight
    ring)

lemma summable_finset_sum_of_summable {ι : Type*} [DecidableEq ι]
    (P : Finset ι) {f : ι → ℕ → ℝ}
    (hf : ∀ i ∈ P, Summable (f i)) :
    Summable (fun n : ℕ => ∑ i ∈ P, f i n) := by
  induction P using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _n : ℕ => (0 : ℝ)))
  | insert a s has ih =>
      have ha : Summable (f a) := hf a (by simp)
      have hs : Summable (fun n : ℕ => ∑ i ∈ s, f i n) :=
        ih (fun i hi => hf i (by simp [hi]))
      simpa [Finset.sum_insert has] using ha.add hs

lemma abs_weight_mul_circleKernel_le {s : ℝ} (hs : 0 ≤ s) (n : ℕ) (x : Plane) :
    |weight s n * CircleBessel.circleKernel (n + 1) x| ≤ weight s n := by
  rw [abs_mul, abs_of_nonneg (weight_nonneg hs n)]
  exact mul_le_of_le_one_right (weight_nonneg hs n)
    (CircleBessel.abs_circleKernel_le_one (n + 1) x)

/--
The positive-definite plane kernel before reducing it to the radial `J₀`
formula.  The remaining bridge is the rotation-invariance identity
`circleKernel k x = J₀(2π k ‖x‖)`.
-/
noncomputable def K_circle (s : ℝ) (x : Plane) : ℝ :=
  ∑' n : ℕ, weight s n * CircleBessel.circleKernel (n + 1) x

lemma summable_K_circle_terms {s : ℝ} (hs : 0 < s) (x : Plane) :
    Summable (fun n : ℕ => weight s n * CircleBessel.circleKernel (n + 1) x) := by
  exact (summable_weight hs).of_norm_bounded (fun n => by
    simpa [Real.norm_eq_abs] using abs_weight_mul_circleKernel_le hs.le n x)

lemma K_circle_pair_sum_eq_tsum (s : ℝ) (hs : 0 < s) (P : Finset Plane) :
    (∑ p ∈ P, ∑ q ∈ P, K_circle s (p - q)) =
      ∑' n : ℕ, weight s n *
        (∑ p ∈ P, ∑ q ∈ P, CircleBessel.circleKernel (n + 1) (p - q)) := by
  unfold K_circle
  calc
    (∑ p ∈ P, ∑ q ∈ P,
        ∑' n : ℕ, weight s n * CircleBessel.circleKernel (n + 1) (p - q))
        = ∑ p ∈ P, ∑' n : ℕ,
            ∑ q ∈ P, weight s n * CircleBessel.circleKernel (n + 1) (p - q) := by
          congr 1
          ext p
          exact (Summable.tsum_finsetSum (s := P)
            (f := fun q n => weight s n * CircleBessel.circleKernel (n + 1) (p - q))
            (fun q _hq => summable_K_circle_terms hs (p - q))).symm
    _ = ∑' n : ℕ, ∑ p ∈ P,
            ∑ q ∈ P, weight s n * CircleBessel.circleKernel (n + 1) (p - q) := by
          exact (Summable.tsum_finsetSum (s := P)
            (f := fun p n => ∑ q ∈ P,
              weight s n * CircleBessel.circleKernel (n + 1) (p - q))
            (fun p _hp => summable_finset_sum_of_summable P
              (fun q _hq => summable_K_circle_terms hs (p - q)))).symm
    _ = ∑' n : ℕ, weight s n *
            (∑ p ∈ P, ∑ q ∈ P, CircleBessel.circleKernel (n + 1) (p - q)) := by
          congr 1
          ext n
          simp [Finset.mul_sum]

lemma K_circle_pos_def {s : ℝ} (hs : 0 < s) (P : Finset Plane) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, K_circle s (p - q) := by
  rw [K_circle_pair_sum_eq_tsum s hs P]
  exact tsum_nonneg (fun n => mul_nonneg (weight_nonneg hs.le n)
    (CircleBessel.circleKernel_pair_sum_nonneg (n + 1) P))

/-- The positive-definite Bessel kernel from the informal proof. -/
noncomputable def K_bessel (s t : ℝ) : ℝ :=
  ∑' n : ℕ,
    weight s n *
      CircleBessel.J0 (2 * Real.pi * (((n + 1 : ℕ) : ℝ)) * t)

lemma K_circle_eq_K_bessel_norm (s : ℝ) (x : Plane) :
    K_circle s x = K_bessel s ‖x‖ := by
  unfold K_circle K_bessel
  apply tsum_congr
  intro n
  rw [CircleBessel.circleKernel_eq_J0_norm]

lemma K_bessel_pos_def {s : ℝ} (hs : 0 < s) (P : Finset Plane) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, K_bessel s (dist p q) := by
  simpa [K_circle_eq_K_bessel_norm, dist_eq_norm] using K_circle_pos_def hs P

lemma K_bessel_zero_eq (s : ℝ) :
    K_bessel s 0 = ∑' n : ℕ, weight s n := by
  simp [K_bessel, CircleBessel.J0_zero]

lemma summable_K_bessel_terms_of_summable_weight {s t : ℝ} (hs : 0 ≤ s)
    (hweight : Summable (fun n : ℕ => weight s n)) :
    Summable (fun n : ℕ => weight s n *
      CircleBessel.J0 (2 * Real.pi * (((n + 1 : ℕ) : ℝ)) * t)) := by
  exact hweight.of_norm_bounded (fun n => by
    simpa [Real.norm_eq_abs] using abs_weight_mul_J0_le hs n t)

lemma summable_K_bessel_terms {s t : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => weight s n *
      CircleBessel.J0 (2 * Real.pi * (((n + 1 : ℕ) : ℝ)) * t)) :=
  summable_K_bessel_terms_of_summable_weight hs.le (summable_weight hs)

lemma abs_K_bessel_le_tsum_weight {s t : ℝ} (hs : 0 ≤ s)
    (hweight : Summable (fun n : ℕ => weight s n)) :
    |K_bessel s t| ≤ ∑' n : ℕ, weight s n := by
  unfold K_bessel
  exact (summable_K_bessel_terms_of_summable_weight hs hweight).hasSum.norm_le_of_bounded
    hweight.hasSum (fun n => by
      simpa [Real.norm_eq_abs] using abs_weight_mul_J0_le hs n t)

lemma abs_K_bessel_le_K_bessel_zero {s t : ℝ} (hs : 0 < s) :
    |K_bessel s t| ≤ K_bessel s 0 := by
  rw [K_bessel_zero_eq]
  exact abs_K_bessel_le_tsum_weight hs.le (summable_weight hs)

lemma diag_majorant_tsum_formula {r s : ℝ} (hr : ‖r‖ < 1) :
    (∑' n : ℕ,
      ((((n + 1).choose 1 : ℕ) : ℝ) + 4 * s * (((n + 2).choose 2 : ℕ) : ℝ)) *
        r ^ n) =
      1 / (1 - r) ^ 2 + 4 * s * (1 / (1 - r) ^ 3) := by
  have h1 := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 (r := r) hr
  have h2 := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 (r := r) hr
  have hs1 : Summable fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * r ^ n :=
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hr)
  have hs2 : Summable fun n : ℕ => (((n + 2).choose 2 : ℕ) : ℝ) * r ^ n :=
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := r) hr)
  rw [← h1, ← h2]
  rw [← tsum_mul_left]
  rw [← Summable.tsum_add hs1 (hs2.mul_left (4 * s))]
  congr 1
  ext n
  ring

lemma tsum_weight_le_diag_expr {s : ℝ} (hs : 0 < s) :
    (∑' n : ℕ, weight s n) ≤
      1 / (1 - Real.exp (-s)) ^ 2 + 4 * s * (1 / (1 - Real.exp (-s)) ^ 3) := by
  let r := Real.exp (-s)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hmaj_summable : Summable fun n : ℕ =>
      ((((n + 1).choose 1 : ℕ) : ℝ) +
        4 * s * (((n + 2).choose 2 : ℕ) : ℝ)) * r ^ n := by
    have hs1 : Summable fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * r ^ n :=
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hr)
    have hs2 : Summable fun n : ℕ => (((n + 2).choose 2 : ℕ) : ℝ) * r ^ n :=
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := r) hr)
    have hsum := hs1.add (hs2.mul_left (4 * s))
    exact hsum.congr (fun n => by ring)
  calc
    (∑' n : ℕ, weight s n) ≤
        ∑' n : ℕ, ((((n + 1).choose 1 : ℕ) : ℝ) +
          4 * s * (((n + 2).choose 2 : ℕ) : ℝ)) * Real.exp (-s) ^ n := by
      exact Summable.tsum_le_tsum (weight_le_diag_majorant hs.le)
        (summable_weight hs) hmaj_summable
    _ = 1 / (1 - Real.exp (-s)) ^ 2 +
          4 * s * (1 / (1 - Real.exp (-s)) ^ 3) := by
      simpa [r] using diag_majorant_tsum_formula (r := r) (s := s) hr

lemma diag_expr_le_inv_sq {s d : ℝ} (hs : 0 < s) (hD : s / 2 ≤ d) :
    1 / d ^ 2 + 4 * s * (1 / d ^ 3) ≤ 36 * (s ^ 2)⁻¹ := by
  have hhalfpos : 0 < s / 2 := by positivity
  have hpow2 : (s / 2) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hhalfpos.le hD 2
  have hpow3 : (s / 2) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hhalfpos.le hD 3
  have hterm1 : 1 / d ^ 2 ≤ 4 * (s ^ 2)⁻¹ := by
    have hinv := one_div_le_one_div_of_le (pow_pos hhalfpos 2) hpow2
    calc
      1 / d ^ 2 ≤ 1 / (s / 2) ^ 2 := hinv
      _ = 4 * (s ^ 2)⁻¹ := by
        field_simp [hs.ne']
        ring
  have hterm2 : 4 * s * (1 / d ^ 3) ≤ 32 * (s ^ 2)⁻¹ := by
    have hinv := one_div_le_one_div_of_le (pow_pos hhalfpos 3) hpow3
    calc
      4 * s * (1 / d ^ 3) ≤ 4 * s * (1 / (s / 2) ^ 3) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 32 * (s ^ 2)⁻¹ := by
        field_simp [hs.ne']
        ring
  linarith

lemma tsum_weight_le_inv_sq {s : ℝ} (hs : 0 < s) (hsle : s ≤ 1 / 2) :
    (∑' n : ℕ, weight s n) ≤ 36 * (s ^ 2)⁻¹ := by
  have hden : s / 2 ≤ 1 - Real.exp (-s) :=
    one_sub_exp_neg_ge_half hs hsle
  exact (tsum_weight_le_diag_expr hs).trans (diag_expr_le_inv_sq hs hden)

lemma K_bessel_diag_bound_explicit {s : ℝ} (hs : 0 < s) (hsle : s ≤ 1 / 2) :
    K_bessel s 0 ≤ 36 * (s ^ 2)⁻¹ := by
  rw [K_bessel_zero_eq]
  exact tsum_weight_le_inv_sq hs hsle

/-- Even integer samples of the radial Bessel-Laplace terms appearing in `K_bessel`. -/
noncomputable def poissonSample (j : ℕ) (s t : ℝ) (m : ℤ) : ℝ :=
  |(m : ℝ)| ^ j * Real.exp (-s * |(m : ℝ)|) *
    CircleBessel.J0 (2 * Real.pi * t * |(m : ℝ)|)

lemma poissonSample_natCast (j : ℕ) (s t : ℝ) (n : ℕ) :
    poissonSample j s t (n : ℤ) =
      (n : ℝ) ^ j * Real.exp (-s * (n : ℝ)) *
        CircleBessel.J0 (2 * Real.pi * t * (n : ℝ)) := by
  unfold poissonSample
  simp

lemma abs_poissonSample_natCast_le (j : ℕ) (s t : ℝ) (n : ℕ) :
    ‖poissonSample j s t (n : ℤ)‖ ≤
      (n : ℝ) ^ j * Real.exp (-s * (n : ℝ)) := by
  rw [Real.norm_eq_abs, poissonSample_natCast]
  rw [abs_mul]
  rw [abs_of_nonneg
    (by positivity : 0 ≤ (n : ℝ) ^ j * Real.exp (-s * (n : ℝ)))]
  exact mul_le_of_le_one_right (by positivity) (CircleBessel.abs_J0_le_one _)

lemma summable_poissonSample_natCast (j : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable (fun n : ℕ => poissonSample j s t (n : ℤ)) := by
  exact (Real.summable_pow_mul_exp_neg_nat_mul j hs).of_norm_bounded
    (abs_poissonSample_natCast_le j s t)

lemma poissonSample_negSucc (j : ℕ) (s t : ℝ) (n : ℕ) :
    poissonSample j s t (Int.negSucc n) =
      ((n + 1 : ℕ) : ℝ) ^ j * Real.exp (-s * ((n + 1 : ℕ) : ℝ)) *
        CircleBessel.J0 (2 * Real.pi * t * ((n + 1 : ℕ) : ℝ)) := by
  unfold poissonSample
  rw [Int.cast_negSucc]
  rw [abs_of_nonpos]
  · ring_nf
  · have h : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    linarith

lemma abs_poissonSample_negSucc_le (j : ℕ) (s t : ℝ) (n : ℕ) :
    ‖poissonSample j s t (-(↑n + 1))‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ j * Real.exp (-s * ((n + 1 : ℕ) : ℝ)) := by
  rw [show (-(↑n + 1) : ℤ) = Int.negSucc n by rfl]
  rw [Real.norm_eq_abs, poissonSample_negSucc]
  rw [abs_mul]
  rw [abs_of_nonneg
    (by positivity :
      0 ≤ ((n + 1 : ℕ) : ℝ) ^ j * Real.exp (-s * ((n + 1 : ℕ) : ℝ)))]
  exact mul_le_of_le_one_right (by positivity) (CircleBessel.abs_J0_le_one _)

lemma summable_poissonSample_negSucc (j : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable (fun n : ℕ => poissonSample j s t (-(↑n + 1))) := by
  have hbase : Summable fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ j * Real.exp (-s * ((n + 1 : ℕ) : ℝ)) := by
    exact (summable_nat_add_iff (f := fun n : ℕ =>
      (n : ℝ) ^ j * Real.exp (-s * (n : ℝ))) 1).2
        (Real.summable_pow_mul_exp_neg_nat_mul j hs)
  exact hbase.of_norm_bounded (abs_poissonSample_negSucc_le j s t)

lemma summable_poissonSample_int (j : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable (fun m : ℤ => poissonSample j s t m) := by
  exact Summable.of_nat_of_neg_add_one
    (summable_poissonSample_natCast j hs t)
    (summable_poissonSample_negSucc j hs t)

lemma poissonSample_even (j : ℕ) (s t : ℝ) : Function.Even (poissonSample j s t) := by
  intro m
  unfold poissonSample
  simp

lemma poissonSample_zero_of_pos {j : ℕ} (hj : 0 < j) (s t : ℝ) :
    poissonSample j s t 0 = 0 := by
  unfold poissonSample
  simp [Nat.pos_iff_ne_zero.mp hj]

lemma tsum_poissonSample_eq_two_tsum_succ {j : ℕ} (hj : 0 < j) {s : ℝ}
    (hs : 0 < s) (t : ℝ) :
    (∑' m : ℤ, poissonSample j s t m) =
      2 * (∑' n : ℕ, poissonSample j s t ((n + 1 : ℕ) : ℤ)) := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (poissonSample_even j s t)
    (summable_poissonSample_int j hs t)]
  rw [poissonSample_zero_of_pos hj]
  rw [zero_add]
  have hpnat : (∑' n : ℕ+, poissonSample j s t (((n : ℕ) : ℤ))) =
      (∑' n : ℕ, poissonSample j s t (((n + 1 : ℕ) : ℤ))) := by
    exact tsum_pnat_eq_tsum_succ (f := fun n : ℕ => poissonSample j s t (n : ℤ))
  rw [hpnat]
  rw [two_smul]
  ring

lemma K_bessel_eq_tsum_poissonSamples {s t : ℝ} (hs : 0 < s) :
    K_bessel s t =
      (1 / 2 : ℝ) * (∑' m : ℤ, poissonSample 1 s t m) +
        s * (∑' m : ℤ, poissonSample 2 s t m) := by
  have hsum1 : Summable fun n : ℕ => poissonSample 1 s t ((n + 1 : ℕ) : ℤ) := by
    simpa using (summable_nat_add_iff
      (f := fun n : ℕ => poissonSample 1 s t (n : ℤ)) 1).2
        (summable_poissonSample_natCast 1 hs t)
  have hsum2 : Summable fun n : ℕ => poissonSample 2 s t ((n + 1 : ℕ) : ℤ) := by
    simpa using (summable_nat_add_iff
      (f := fun n : ℕ => poissonSample 2 s t (n : ℤ)) 1).2
        (summable_poissonSample_natCast 2 hs t)
  rw [tsum_poissonSample_eq_two_tsum_succ (by norm_num : 0 < 1) hs t]
  rw [tsum_poissonSample_eq_two_tsum_succ (by norm_num : 0 < 2) hs t]
  have hhalf : (1 / 2 : ℝ) *
        (2 * (∑' n : ℕ, poissonSample 1 s t ((n + 1 : ℕ) : ℤ))) =
      ∑' n : ℕ, poissonSample 1 s t ((n + 1 : ℕ) : ℤ) := by
    ring
  rw [hhalf]
  have hs2 : s *
        (2 * (∑' n : ℕ, poissonSample 2 s t ((n + 1 : ℕ) : ℤ))) =
      ∑' n : ℕ, (2 * s) * poissonSample 2 s t ((n + 1 : ℕ) : ℤ) := by
    calc
      s * (2 * (∑' n : ℕ, poissonSample 2 s t ((n + 1 : ℕ) : ℤ))) =
          (2 * s) * (∑' n : ℕ, poissonSample 2 s t ((n + 1 : ℕ) : ℤ)) := by
        ring
      _ = ∑' n : ℕ, (2 * s) * poissonSample 2 s t ((n + 1 : ℕ) : ℤ) := by
        rw [tsum_mul_left]
  rw [hs2]
  rw [← Summable.tsum_add hsum1 (hsum2.mul_left (2 * s))]
  unfold K_bessel weight poissonSample
  apply tsum_congr
  intro n
  have habs : |((((n + 1 : ℕ) : ℤ) : ℝ))| = ((n + 1 : ℕ) : ℝ) := by
    rw [Int.cast_natCast]
    exact abs_of_nonneg (by positivity)
  rw [habs]
  have harg : 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t =
      2 * Real.pi * t * ((n + 1 : ℕ) : ℝ) := by
    ring
  rw [harg]
  ring

/-- The shifted Fourier/Laplace parameter `λ_m = s + 2πim`. -/
noncomputable def lam (s : ℝ) (m : ℤ) : ℂ :=
  Complex.ofReal s + 2 * Complex.ofReal Real.pi * Complex.I * Complex.ofReal (m : ℝ)

/-- The quadratic expression `q_m(t) = λ_m^2 + (2πt)^2`. -/
noncomputable def q (s t : ℝ) (m : ℤ) : ℂ :=
  lam s m ^ 2 + Complex.ofReal ((2 * Real.pi * t) ^ 2)

/-- A real power as a complex principal-branch power. -/
noncomputable def cpowR (z : ℂ) (a : ℝ) : ℂ :=
  z ^ (Complex.ofReal a)

/-- The signed Poisson-side summand from Proposition 4. -/
noncomputable def Tterm (s t : ℝ) (m : ℤ) : ℝ :=
  ((lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) +
      2 * Complex.ofReal s *
        (-cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)))).re

end Erdos953Formalization
