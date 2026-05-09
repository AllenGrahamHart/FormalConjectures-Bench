import FormalConjecturesBench.RobustPointBound
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace Erdos953Formalization

/--
The real-valued one-dimensional sample whose integer sum is `K_bessel`.
This is the function to which one-dimensional Poisson summation is applied.
-/
noncomputable def poissonKernelSampleR (s t x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * |x| + s * |x| ^ 2) * Real.exp (-s * |x|) *
    CircleBessel.J0 (2 * Real.pi * t * |x|)

/-- Complex coercion of `poissonKernelSampleR`, used by mathlib's Fourier transform API. -/
noncomputable def poissonKernelSampleC (s t x : ℝ) : ℂ :=
  (poissonKernelSampleR s t x : ℂ)

/-- The complex Poisson-side summand whose real part is `Tterm`. -/
noncomputable def TtermC (s t : ℝ) (m : ℤ) : ℂ :=
  (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) +
    2 * Complex.ofReal s *
      (-cpowR (q s t m) (-(3 / 2 : ℝ)) +
        3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)))

lemma Tterm_eq_TtermC_re (s t : ℝ) (m : ℤ) :
    Tterm s t m = (TtermC s t m).re := by
  rfl

lemma lam_re (s : ℝ) (m : ℤ) : (lam s m).re = s := by
  unfold lam
  simp [Complex.mul_re]

lemma lam_ne_zero {s : ℝ} (hs : 0 < s) (m : ℤ) : lam s m ≠ 0 := by
  intro h
  have hre : (lam s m).re = 0 := by simp [h]
  rw [lam_re] at hre
  linarith

lemma cpowR_lam_sq_neg_three_halves {s : ℝ} (hs : 0 < s) (m : ℤ) :
    cpowR ((lam s m) ^ 2) (-(3 / 2 : ℝ)) = (lam s m) ^ (-3 : ℤ) := by
  unfold cpowR
  have hhalf : (((-(3 / 2 : ℝ) : ℝ) : ℂ)) = (-3 : ℤ) * (2⁻¹ : ℂ) := by
    norm_num [div_eq_mul_inv]
  rw [hhalf]
  rw [Complex.cpow_int_mul]
  have hsqrt : ((lam s m) ^ 2) ^ (2⁻¹ : ℂ) = lam s m := by
    simpa [pow_two] using
      Complex.sq_cpow_two_inv (x := lam s m) (by simpa [lam_re] using hs)
  rw [hsqrt]

lemma cpowR_lam_sq_neg_five_halves {s : ℝ} (hs : 0 < s) (m : ℤ) :
    cpowR ((lam s m) ^ 2) (-(5 / 2 : ℝ)) = (lam s m) ^ (-5 : ℤ) := by
  unfold cpowR
  have hhalf : (((-(5 / 2 : ℝ) : ℝ) : ℂ)) = (-5 : ℤ) * (2⁻¹ : ℂ) := by
    norm_num [div_eq_mul_inv]
  rw [hhalf]
  rw [Complex.cpow_int_mul]
  have hsqrt : ((lam s m) ^ 2) ^ (2⁻¹ : ℂ) = lam s m := by
    simpa [pow_two] using
      Complex.sq_cpow_two_inv (x := lam s m) (by simpa [lam_re] using hs)
  rw [hsqrt]

lemma q_zero_t (s : ℝ) (m : ℤ) : q s 0 m = (lam s m) ^ 2 := by
  unfold q
  norm_num

lemma angular_rhs_first_t_zero {s : ℝ} (hs : 0 < s) (m : ℤ) :
    (lam s m) * cpowR (q s 0 m) (-(3 / 2 : ℝ)) =
      1 / (lam s m) ^ 2 := by
  rw [q_zero_t, cpowR_lam_sq_neg_three_halves hs]
  have hne := lam_ne_zero hs m
  field_simp [hne]

lemma angular_rhs_second_t_zero {s : ℝ} (hs : 0 < s) (m : ℤ) :
    -cpowR (q s 0 m) (-(3 / 2 : ℝ)) +
        3 * (lam s m) ^ 2 * cpowR (q s 0 m) (-(5 / 2 : ℝ)) =
      2 / (lam s m) ^ 3 := by
  rw [q_zero_t, cpowR_lam_sq_neg_three_halves hs, cpowR_lam_sq_neg_five_halves hs]
  have hne := lam_ne_zero hs m
  field_simp [hne]
  ring

lemma poissonKernelSampleR_intCast (s t : ℝ) (m : ℤ) :
    poissonKernelSampleR s t (m : ℝ) =
      (1 / 2 : ℝ) * poissonSample 1 s t m + s * poissonSample 2 s t m := by
  unfold poissonKernelSampleR poissonSample
  ring

lemma continuous_poissonKernelSampleR (s t : ℝ) :
    Continuous (poissonKernelSampleR s t) := by
  unfold poissonKernelSampleR
  have hpoly : Continuous fun x : ℝ => (1 / 2 : ℝ) * |x| + s * |x| ^ 2 := by
    fun_prop
  have hexp : Continuous fun x : ℝ => Real.exp (-s * |x|) := by
    fun_prop
  have harg : Continuous fun x : ℝ => 2 * Real.pi * t * |x| := by
    fun_prop
  exact (hpoly.mul hexp).mul (CircleBessel.continuous_J0.comp harg)

lemma continuous_poissonKernelSampleC (s t : ℝ) :
    Continuous (poissonKernelSampleC s t) := by
  unfold poissonKernelSampleC
  exact Complex.continuous_ofReal.comp (continuous_poissonKernelSampleR s t)

lemma summable_poissonKernelSampleR_int {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable (fun m : ℤ => poissonKernelSampleR s t (m : ℝ)) := by
  have h1 : Summable fun m : ℤ => (1 / 2 : ℝ) * poissonSample 1 s t m :=
    (summable_poissonSample_int 1 hs t).mul_left (1 / 2 : ℝ)
  have h2 : Summable fun m : ℤ => s * poissonSample 2 s t m :=
    (summable_poissonSample_int 2 hs t).mul_left s
  exact (h1.add h2).congr (fun m => by rw [poissonKernelSampleR_intCast])

lemma K_bessel_eq_tsum_poissonKernelSampleR {s t : ℝ} (hs : 0 < s) :
    K_bessel s t = ∑' m : ℤ, poissonKernelSampleR s t (m : ℝ) := by
  rw [K_bessel_eq_tsum_poissonSamples hs]
  have h1 : Summable fun m : ℤ => poissonSample 1 s t m :=
    summable_poissonSample_int 1 hs t
  have h2 : Summable fun m : ℤ => poissonSample 2 s t m :=
    summable_poissonSample_int 2 hs t
  rw [← tsum_mul_left, ← tsum_mul_left]
  rw [← Summable.tsum_add (h1.mul_left (1 / 2 : ℝ)) (h2.mul_left s)]
  apply tsum_congr
  intro m
  rw [poissonKernelSampleR_intCast]

lemma poissonKernelSampleC_bound_atTop {s t x : ℝ} (hs : 0 < s) (hx : 1 ≤ x) :
    ‖poissonKernelSampleC s t x‖ ≤
      ((1 / 2 : ℝ) + s) * (x ^ (2 : ℝ) * Real.exp (-s * x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hJ := CircleBessel.abs_J0_le_one (2 * Real.pi * t * x)
  calc
    ‖poissonKernelSampleC s t x‖ = |poissonKernelSampleR s t x| := by
      simp [poissonKernelSampleC]
    _ = |(((1 / 2 : ℝ) * x + s * x ^ 2) * Real.exp (-s * x) *
          CircleBessel.J0 (2 * Real.pi * t * x))| := by
      simp [poissonKernelSampleR, abs_of_nonneg hx0]
    _ ≤ (((1 / 2 : ℝ) * x + s * x ^ 2) * Real.exp (-s * x)) := by
      rw [abs_mul]
      rw [abs_of_nonneg
        (by positivity :
          0 ≤ ((1 / 2 : ℝ) * x + s * x ^ 2) * Real.exp (-s * x))]
      exact mul_le_of_le_one_right (by positivity) hJ
    _ ≤ ((1 / 2 : ℝ) + s) * (x ^ (2 : ℝ) * Real.exp (-s * x)) := by
      have hx_rpow_two : x ^ (2 : ℝ) = x ^ 2 := by
        norm_num [Real.rpow_natCast]
      rw [hx_rpow_two]
      have hx_le_sq : x ≤ x ^ 2 := by nlinarith
      have hpoly :
          (1 / 2 : ℝ) * x + s * x ^ 2 ≤ ((1 / 2 : ℝ) + s) * x ^ 2 := by
        nlinarith [hs.le, hx_le_sq]
      calc
        ((1 / 2 : ℝ) * x + s * x ^ 2) * Real.exp (-s * x) ≤
            (((1 / 2 : ℝ) + s) * x ^ 2) * Real.exp (-s * x) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
        _ = ((1 / 2 : ℝ) + s) * (x ^ 2 * Real.exp (-s * x)) := by
          ring

lemma poissonKernelSampleC_isBigO_atTop {s t : ℝ} (hs : 0 < s) :
    (poissonKernelSampleC s t) =O[atTop]
      (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-s * x)) := by
  refine IsBigO.of_bound (((1 / 2 : ℝ) + s)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa using poissonKernelSampleC_bound_atTop (s := s) (t := t) hs hx

lemma rpow_two_exp_decay_atTop {s : ℝ} (hs : 0 < s) :
    (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-s * x)) =O[atTop]
      (fun x : ℝ => x ^ (-(2 : ℝ))) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hs (-(4 : ℝ))).isBigO
  have hmul := (isBigO_refl (fun x : ℝ => x ^ (2 : ℝ)) atTop).mul h
  refine hmul.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_add hx]
  norm_num

lemma poissonKernelSampleC_decay_atTop {s t : ℝ} (hs : 0 < s) :
    (poissonKernelSampleC s t) =O[atTop]
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  refine (poissonKernelSampleC_isBigO_atTop (s := s) (t := t) hs).trans ?_
  refine (rpow_two_exp_decay_atTop hs).congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [abs_of_pos hx]

lemma poissonKernelSampleC_even (s t : ℝ) : Function.Even (poissonKernelSampleC s t) := by
  intro x
  simp [poissonKernelSampleC, poissonKernelSampleR]

lemma poissonKernelSampleC_decay_atBot {s t : ℝ} (hs : 0 < s) :
    (poissonKernelSampleC s t) =O[atBot]
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  have htop := poissonKernelSampleC_decay_atTop (s := s) (t := t) hs
  have hcomp := htop.comp_tendsto tendsto_neg_atBot_atTop
  refine hcomp.congr' ?_ ?_
  · filter_upwards with x
    exact poissonKernelSampleC_even s t x
  · filter_upwards with x
    simp

lemma poissonKernelSampleC_decay_cocompact {s t : ℝ} (hs : 0 < s) :
    (poissonKernelSampleC s t) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  rw [cocompact_eq_atBot_atTop, isBigO_sup]
  exact ⟨poissonKernelSampleC_decay_atBot (s := s) (t := t) hs,
    poissonKernelSampleC_decay_atTop (s := s) (t := t) hs⟩

lemma integrableAtFilter_abs_rpow_neg_two_atTop :
    MeasureTheory.IntegrableAtFilter (fun x : ℝ => |x| ^ (-(2 : ℝ)))
      atTop MeasureTheory.volume := by
  rw [MeasureTheory.integrableAtFilter_atTop_iff]
  refine ⟨(1 : ℝ), ?_⟩
  have hpow_ioi :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(2 : ℝ)))
        (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hpow_ici :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(2 : ℝ)))
        (Set.Ici (1 : ℝ)) MeasureTheory.volume := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hpow_ioi
  exact hpow_ici.congr_fun (fun x hx => by
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx
    rw [abs_of_nonneg hx0]) measurableSet_Ici

lemma integrable_poissonKernelSampleC {s t : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable (poissonKernelSampleC s t) := by
  have hloc : MeasureTheory.LocallyIntegrable
      (poissonKernelSampleC s t) MeasureTheory.volume :=
    (continuous_poissonKernelSampleC s t).locallyIntegrable
  have hsymm : norm ∘ poissonKernelSampleC s t =ᵐ[MeasureTheory.volume]
      norm ∘ poissonKernelSampleC s t ∘ Neg.neg := by
    exact MeasureTheory.ae_of_all _ (fun x => by
      simp [Function.comp_def, poissonKernelSampleC_even s t x])
  exact hloc.integrable_of_isBigO_atTop_of_norm_isNegInvariant hsymm
    (poissonKernelSampleC_decay_atTop (s := s) (t := t) hs)
    integrableAtFilter_abs_rpow_neg_two_atTop

lemma integral_comp_neg_eq_self_of_integrable {f : ℝ → ℂ}
    (hf : MeasureTheory.Integrable f MeasureTheory.volume) :
    (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
  have hfm : AEStronglyMeasurable f (Measure.map Neg.neg MeasureTheory.volume) := by
    simpa [Measure.map_neg_eq_self (MeasureTheory.volume : Measure ℝ)] using
      hf.aestronglyMeasurable
  have hmap := MeasureTheory.integral_map (μ := MeasureTheory.volume)
    (φ := Neg.neg) (f := f) measurable_neg.aemeasurable hfm
  simpa [Measure.map_neg_eq_self (MeasureTheory.volume : Measure ℝ)] using hmap.symm

lemma integrable_fourierIntegrand_poissonKernelSampleC {s t : ℝ} (hs : 0 < s)
    (w : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
        poissonKernelSampleC s t x) MeasureTheory.volume := by
  exact (integrable_poissonKernelSampleC (s := s) (t := t) hs).bdd_mul (c := 1)
    (by
      have hcont : Continuous
          (fun x : ℝ => Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact hcont.aestronglyMeasurable)
    (by
      exact MeasureTheory.ae_of_all _ (fun x => by
        exact le_of_eq (Complex.norm_exp_ofReal_mul_I (-2 * Real.pi * x * w))))

lemma fourier_poissonKernelSampleC_star_eq_self {s t : ℝ} (hs : 0 < s) (w : ℝ) :
    star (FourierTransform.fourier (poissonKernelSampleC s t) w) =
      FourierTransform.fourier (poissonKernelSampleC s t) w := by
  let g : ℝ → ℂ := fun x : ℝ =>
    Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) *
      poissonKernelSampleC s t x
  have hg : MeasureTheory.Integrable g MeasureTheory.volume := by
    exact integrable_fourierIntegrand_poissonKernelSampleC (s := s) (t := t) hs w
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (starRingEnd ℂ) (∫ x : ℝ, g x) = ∫ x : ℝ, g x
  rw [← (integral_conj (f := g))]
  rw [← integral_comp_neg_eq_self_of_integrable hg]
  apply integral_congr_ae
  exact MeasureTheory.ae_of_all _ (fun x => by
    dsimp [g]
    rw [poissonKernelSampleC_even s t x]
    rw [map_mul]
    rw [← Complex.exp_conj]
    have hf : (starRingEnd ℂ) (poissonKernelSampleC s t x) =
        poissonKernelSampleC s t x := by
      simp [poissonKernelSampleC]
    rw [hf]
    congr 1
    apply congrArg Complex.exp
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring)

lemma complex_eq_of_star_eq_self {z : ℂ} (hz : star z = z) : z = (z.re : ℂ) := by
  have him := congrArg Complex.im hz
  simp at him
  have hzero : z.im = 0 := by linarith
  apply Complex.ext <;> simp [hzero]

lemma fourier_poissonKernelSampleC_eq_ofReal_re {s t : ℝ} (hs : 0 < s) (w : ℝ) :
    FourierTransform.fourier (poissonKernelSampleC s t) w =
      ((FourierTransform.fourier (poissonKernelSampleC s t) w).re : ℂ) := by
  exact complex_eq_of_star_eq_self
    (fourier_poissonKernelSampleC_star_eq_self (s := s) (t := t) hs w)

/--
The positive-half-line integrand obtained after using the evenness of the
sample and combining the oscillatory Fourier factor with `exp (-s x)`.
-/
noncomputable def poissonKernelHalfLineIntegrand (s t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(lam s m) * (x : ℂ)) *
    ((((1 / 2 : ℝ) * x + s * x ^ 2) *
      CircleBessel.J0 (2 * Real.pi * t * x) : ℝ) : ℂ)

lemma fourier_poissonKernelSampleC_re_eq_two_re_halfLine {s t : ℝ} (hs : 0 < s)
    (m : ℤ) :
    (FourierTransform.fourier (poissonKernelSampleC s t) (m : ℝ)).re =
      2 * (∫ x in Set.Ioi (0 : ℝ),
        poissonKernelHalfLineIntegrand s t m x).re := by
  let G : ℝ → ℂ := fun x : ℝ =>
    Complex.exp (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) *
      poissonKernelSampleC s t x
  let H : ℝ → ℂ := poissonKernelHalfLineIntegrand s t m
  have hGint : MeasureTheory.Integrable G MeasureTheory.volume := by
    exact integrable_fourierIntegrand_poissonKernelSampleC (s := s) (t := t) hs (m : ℝ)
  have hleft_eq : (∫ x in Set.Iic (0 : ℝ), G x) =
      ∫ x in Set.Ioi (0 : ℝ), G (-x) := by
    convert integral_comp_neg_Iic (c := (0 : ℝ)) (f := fun y : ℝ => G (-y)) using 1 <;>
      simp
  have hneg_conj : ∀ x ∈ Set.Ioi (0 : ℝ), G (-x) = star (G x) := by
    intro x hx
    dsimp [G]
    rw [poissonKernelSampleC_even s t x]
    rw [map_mul]
    rw [← Complex.exp_conj]
    have hf : (starRingEnd ℂ) (poissonKernelSampleC s t x) =
        poissonKernelSampleC s t x := by
      simp [poissonKernelSampleC]
    rw [hf]
    congr 1
    apply congrArg Complex.exp
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
  have hconj : (∫ x in Set.Ioi (0 : ℝ), G (-x)) =
      ∫ x in Set.Ioi (0 : ℝ), star (G x) := by
    exact setIntegral_congr_fun measurableSet_Ioi hneg_conj
  have hright_re : (∫ x in Set.Ioi (0 : ℝ), G (-x)).re =
      (∫ x in Set.Ioi (0 : ℝ), G x).re := by
    rw [hconj]
    change (∫ x in Set.Ioi (0 : ℝ), (starRingEnd ℂ) (G x)).re =
      (∫ x in Set.Ioi (0 : ℝ), G x).re
    rw [integral_conj (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (f := G)]
    simp
  have hsplit : (∫ x : ℝ, G x) =
      (∫ x in Set.Iic (0 : ℝ), G x) + ∫ x in Set.Ioi (0 : ℝ), G x := by
    exact (intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hGint.integrableOn
      hGint.integrableOn).symm
  have hfull_re : (∫ x : ℝ, G x).re =
      2 * (∫ x in Set.Ioi (0 : ℝ), G x).re := by
    rw [hsplit]
    rw [hleft_eq]
    rw [Complex.add_re]
    rw [hright_re]
    ring_nf
  have hH : ∀ x ∈ Set.Ioi (0 : ℝ), G x = H x := by
    intro x hx
    have hxpos : 0 < x := hx
    dsimp [G, H, poissonKernelHalfLineIntegrand]
    simp [poissonKernelSampleC, poissonKernelSampleR, abs_of_nonneg hxpos.le, lam]
    rw [show Complex.exp (-(2 * ↑Real.pi * ↑x * ↑m * Complex.I)) *
        ((2⁻¹ * ↑x + ↑s * ↑x ^ 2) * Complex.exp (-(↑s * ↑x)) *
          ↑(CircleBessel.J0 (2 * Real.pi * t * x))) =
        (Complex.exp (-(2 * ↑Real.pi * ↑x * ↑m * Complex.I)) *
          Complex.exp (-(↑s * ↑x))) *
          ((2⁻¹ * ↑x + ↑s * ↑x ^ 2) *
            ↑(CircleBessel.J0 (2 * Real.pi * t * x))) by ring_nf]
    rw [← Complex.exp_add]
    congr 1
    ring_nf
  have hGH : (∫ x in Set.Ioi (0 : ℝ), G x) = ∫ x in Set.Ioi (0 : ℝ), H x := by
    exact setIntegral_congr_fun measurableSet_Ioi hH
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ x : ℝ, G x).re = 2 * (∫ x in Set.Ioi (0 : ℝ), H x).re
  rw [hfull_re]
  rw [hGH]

lemma summable_Tterm_of_summable_TtermC {s t : ℝ}
    (h : Summable (fun m : ℤ => TtermC s t m)) :
    Summable (fun m : ℤ => Tterm s t m) := by
  simpa [Tterm_eq_TtermC_re] using Complex.reCLM.summable h

lemma tsum_Tterm_eq_re_tsum_TtermC {s t : ℝ}
    (h : Summable (fun m : ℤ => TtermC s t m)) :
    (∑' m : ℤ, Tterm s t m) = ((∑' m : ℤ, TtermC s t m).re) := by
  simpa [Tterm_eq_TtermC_re] using (Complex.reCLM.map_tsum h).symm

lemma lam_nat_div_rpow_one_tendsto (s : ℝ) :
    Tendsto
      (fun n : ℕ => lam s (n : ℤ) / (((n : ℝ) ^ (1 : ℝ) : ℝ) : ℂ))
      atTop (𝓝 (2 * Complex.ofReal Real.pi * Complex.I)) := by
  have heq :
      (fun n : ℕ => lam s (n : ℤ) / (((n : ℝ) ^ (1 : ℝ) : ℝ) : ℂ)) =ᶠ[atTop]
        fun n : ℕ => (s : ℂ) / (n : ℂ) + 2 * Complex.ofReal Real.pi * Complex.I := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    unfold lam
    simp [Real.rpow_one]
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn]
  have hreal : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcomplex : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hreal
  have hzero : Tendsto (fun n : ℕ => (s : ℂ) / (n : ℂ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv] using
      hcomplex.const_mul (s : ℂ)
  have hconst : Tendsto (fun _ : ℕ => 2 * Complex.ofReal Real.pi * Complex.I) atTop
      (𝓝 (2 * Complex.ofReal Real.pi * Complex.I)) := tendsto_const_nhds
  have hsum := hzero.add hconst
  simpa [zero_add] using Filter.Tendsto.congr' heq.symm hsum

lemma lam_nat_isBigO (s : ℝ) :
    (fun n : ℕ => lam s (n : ℤ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (lam_nat_div_rpow_one_tendsto s)

lemma const_div_nat_rpow_two_tendsto (c : ℂ) :
    Tendsto (fun n : ℕ => c / (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hsq_atTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 : ℝ)) atTop atTop := by
    exact (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv_real : Tendsto (fun n : ℕ => (((n : ℝ) ^ (2 : ℝ))⁻¹ : ℝ)) atTop
      (𝓝 0) := by
    exact (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      hsq_atTop
  have hinv_complex : Tendsto (fun n : ℕ => ((((n : ℝ) ^ (2 : ℝ))⁻¹ : ℝ) : ℂ))
      atTop (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hinv_real
  have hmul : Tendsto (fun n : ℕ => c * (((((n : ℝ) ^ (2 : ℝ))⁻¹ : ℝ) : ℂ)))
      atTop (𝓝 0) := by
    simpa using hinv_complex.const_mul c
  have heq :
      (fun n : ℕ => c * (((((n : ℝ) ^ (2 : ℝ))⁻¹ : ℝ) : ℂ))) =ᶠ[atTop]
        fun n : ℕ => c / (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
    filter_upwards with n
    rw [div_eq_mul_inv]
    congr 1
    rw [← Complex.ofReal_inv]
  exact Filter.Tendsto.congr' heq hmul

lemma q_nat_div_rpow_two_tendsto (s t : ℝ) :
    Tendsto
      (fun n : ℕ => q s t (n : ℤ) / (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ)) atTop
      (𝓝 ((2 * Complex.ofReal Real.pi * Complex.I) ^ 2)) := by
  have heq :
      (fun n : ℕ => q s t (n : ℤ) / (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ)) =ᶠ[atTop]
        fun n : ℕ =>
          (lam s (n : ℤ) / (((n : ℝ) ^ (1 : ℝ) : ℝ) : ℂ)) ^ 2 +
            (((2 * Real.pi * t) ^ 2 : ℝ) : ℂ) /
              (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    unfold q
    have hnC : (((n : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      simp [Real.rpow_one]
      exact_mod_cast hn
    have hn2C : (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      norm_num [Real.rpow_natCast]
      exact_mod_cast hn
    have hpow : (((n : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) ^ 2 =
        (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
      norm_num [Real.rpow_natCast]
    field_simp [hnC, hn2C]
    rw [hpow]
    ring
  have hlam2 := (lam_nat_div_rpow_one_tendsto s).pow 2
  have hconst := const_div_nat_rpow_two_tendsto (((2 * Real.pi * t) ^ 2 : ℝ) : ℂ)
  have hsum := hlam2.add hconst
  simpa [add_zero] using Filter.Tendsto.congr' heq.symm hsum

lemma q_nat_isTheta_rpow_two (s t : ℝ) :
    (fun n : ℕ => q s t (n : ℤ)) =Θ[atTop]
      fun n : ℕ => (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) := by
  constructor
  · refine isBigO_of_div_tendsto_nhds ?_ ((2 * Complex.ofReal Real.pi * Complex.I) ^ 2)
      (q_nat_div_rpow_two_tendsto s t)
    filter_upwards [eventually_ne_atTop 0] with n hn hn2
    exfalso
    have hn2C : (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      norm_num [Real.rpow_natCast]
      exact_mod_cast hn
    exact hn2C hn2
  · have hlim :
        Tendsto (fun n : ℕ => (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) / q s t (n : ℤ))
          atTop (𝓝 (((2 * Complex.ofReal Real.pi * Complex.I) ^ 2)⁻¹)) := by
      have hnonzero : ((2 * Complex.ofReal Real.pi * Complex.I) ^ 2) ≠ 0 := by
        norm_num [Complex.ext_iff]
      simpa [inv_div] using (q_nat_div_rpow_two_tendsto s t).inv₀ hnonzero
    refine isBigO_of_div_tendsto_nhds ?_
      (((2 * Complex.ofReal Real.pi * Complex.I) ^ 2)⁻¹) hlim
    have hnonzero : ((2 * Complex.ofReal Real.pi * Complex.I) ^ 2) ≠ 0 := by
      norm_num [Complex.ext_iff]
    have hqdiv_ne : ∀ᶠ n : ℕ in atTop,
        q s t (n : ℤ) / (((n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
      (q_nat_div_rpow_two_tendsto s t).eventually (eventually_ne_nhds hnonzero)
    filter_upwards [hqdiv_ne] with n hqdiv hq0
    exfalso
    exact hqdiv (by simp [hq0])

lemma qnorm_nat_rpow_neg_three_halves_isBigO (s t : ℝ) :
    (fun n : ℕ => ‖q s t (n : ℤ)‖ ^ (-(3 / 2 : ℝ))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ)) := by
  have hnorm : (fun n : ℕ => ‖q s t (n : ℤ)‖) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
    simpa using (q_nat_isTheta_rpow_two s t).norm_left.norm_right
  have hinv := hnorm.inv
  have hpow := hinv.rpow (by norm_num : 0 ≤ (3 / 2 : ℝ))
    (by filter_upwards with n; positivity)
    (by filter_upwards with n; positivity)
  have hpowO : (fun n : ℕ => (‖q s t (n : ℤ)‖⁻¹) ^ (3 / 2 : ℝ)) =O[atTop]
      fun n : ℕ => (((n : ℝ) ^ (2 : ℝ))⁻¹) ^ (3 / 2 : ℝ) := hpow.isBigO
  refine hpowO.congr' ?_ ?_
  · filter_upwards with n
    rw [Real.inv_rpow (norm_nonneg _) (3 / 2 : ℝ),
      ← Real.rpow_neg (norm_nonneg _) (3 / 2 : ℝ)]
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [Real.inv_rpow (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℝ)) (3 / 2 : ℝ)]
    rw [← Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℝ)) (3 / 2 : ℝ)]
    rw [← Real.rpow_mul hn0.le]
    norm_num

lemma qnorm_nat_rpow_neg_five_halves_isBigO (s t : ℝ) :
    (fun n : ℕ => ‖q s t (n : ℤ)‖ ^ (-(5 / 2 : ℝ))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(5 : ℝ)) := by
  have hnorm : (fun n : ℕ => ‖q s t (n : ℤ)‖) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
    simpa using (q_nat_isTheta_rpow_two s t).norm_left.norm_right
  have hinv := hnorm.inv
  have hpow := hinv.rpow (by norm_num : 0 ≤ (5 / 2 : ℝ))
    (by filter_upwards with n; positivity)
    (by filter_upwards with n; positivity)
  have hpowO : (fun n : ℕ => (‖q s t (n : ℤ)‖⁻¹) ^ (5 / 2 : ℝ)) =O[atTop]
      fun n : ℕ => (((n : ℝ) ^ (2 : ℝ))⁻¹) ^ (5 / 2 : ℝ) := hpow.isBigO
  refine hpowO.congr' ?_ ?_
  · filter_upwards with n
    rw [Real.inv_rpow (norm_nonneg _) (5 / 2 : ℝ),
      ← Real.rpow_neg (norm_nonneg _) (5 / 2 : ℝ)]
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [Real.inv_rpow (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℝ)) (5 / 2 : ℝ)]
    rw [← Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℝ)) (5 / 2 : ℝ)]
    rw [← Real.rpow_mul hn0.le]
    norm_num

lemma cpowR_q_nat_neg_three_halves_isBigO (s t : ℝ) :
    (fun n : ℕ => cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ)) := by
  have hnorm :
      (fun n : ℕ => ‖cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ))‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ)) := by
    simpa only [cpowR, Complex.norm_cpow_real] using
      qnorm_nat_rpow_neg_three_halves_isBigO s t
  exact hnorm.of_norm_left

lemma cpowR_q_nat_neg_five_halves_isBigO (s t : ℝ) :
    (fun n : ℕ => cpowR (q s t (n : ℤ)) (-(5 / 2 : ℝ))) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(5 : ℝ)) := by
  have hnorm :
      (fun n : ℕ => ‖cpowR (q s t (n : ℤ)) (-(5 / 2 : ℝ))‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (-(5 : ℝ)) := by
    simpa only [cpowR, Complex.norm_cpow_real] using
      qnorm_nat_rpow_neg_five_halves_isBigO s t
  exact hnorm.of_norm_left

lemma TtermC_nat_isBigO (s t : ℝ) :
    (fun n : ℕ => TtermC s t (n : ℤ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
  have hlam := lam_nat_isBigO s
  have hcp3 := cpowR_q_nat_neg_three_halves_isBigO s t
  have hcp5 := cpowR_q_nat_neg_five_halves_isBigO s t
  have h_lam_cp3 :
      (fun n : ℕ => lam s (n : ℤ) * cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ)))
        =O[atTop] fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
    simpa using Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := (1 : ℝ)) (b := (-(3 : ℝ))) (c := (-(2 : ℝ))) hlam hcp3
      (by norm_num)
  have h_cp3 :
      (fun n : ℕ => -cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ))) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
    have hweaken :
        (fun n : ℕ => cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ))) =O[atTop]
          fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
      refine hcp3.trans (Eventually.isBigO ?_)
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hle : (n : ℝ) ^ (-(3 : ℝ)) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hn1
          (by norm_num : (-(3 : ℝ)) ≤ -(2 : ℝ))
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (-(3 : ℝ)))] using hle
    simpa using hweaken.const_mul_left (-1 : ℂ)
  have hlam2 :
      (fun n : ℕ => (lam s (n : ℤ)) ^ 2) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
    have hmul : (fun n : ℕ => lam s (n : ℤ) * lam s (n : ℤ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
      simpa using Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := (1 : ℝ)) (b := (1 : ℝ)) (c := (2 : ℝ)) hlam hlam (by norm_num)
    simpa [pow_two] using hmul
  have h_lam2_cp5 :
      (fun n : ℕ => (lam s (n : ℤ)) ^ 2 *
        cpowR (q s t (n : ℤ)) (-(5 / 2 : ℝ))) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
    simpa using Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := (2 : ℝ)) (b := (-(5 : ℝ))) (c := (-(2 : ℝ))) hlam2 hcp5
      (by norm_num)
  have h_inner :
      (fun n : ℕ =>
        -cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ)) +
          3 * (lam s (n : ℤ)) ^ 2 * cpowR (q s t (n : ℤ)) (-(5 / 2 : ℝ)))
        =O[atTop] fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
    exact h_cp3.add (by simpa [mul_assoc] using h_lam2_cp5.const_mul_left (3 : ℂ))
  have h_second :
      (fun n : ℕ => 2 * Complex.ofReal s *
        (-cpowR (q s t (n : ℤ)) (-(3 / 2 : ℝ)) +
          3 * (lam s (n : ℤ)) ^ 2 * cpowR (q s t (n : ℤ)) (-(5 / 2 : ℝ))))
        =O[atTop] fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ)) := by
    simpa [mul_assoc] using h_inner.const_mul_left (2 * Complex.ofReal s)
  have hsum := h_lam_cp3.add h_second
  simpa [TtermC] using hsum

lemma TtermC_neg_of_ne (s t : ℝ) {m : ℤ} (hs : 0 < s) (hm : m ≠ 0) :
    TtermC s t (-m) = star (TtermC s t m) := by
  unfold TtermC
  rw [lam_neg, q_neg]
  rw [cpowR_conj (q_arg_ne_pi hs hm)]
  rw [cpowR_conj (q_arg_ne_pi hs hm)]
  let X : ℂ := (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) +
      2 * Complex.ofReal s *
        (-cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)))
  change star (lam s m) * star (cpowR (q s t m) (-(3 / 2 : ℝ))) +
        2 * Complex.ofReal s *
          (-star (cpowR (q s t m) (-(3 / 2 : ℝ))) +
            3 * star (lam s m) ^ 2 * star (cpowR (q s t m) (-(5 / 2 : ℝ)))) =
      star X
  dsimp [X]
  simp [Complex.conj_ofNat]

lemma TtermC_negSucc_norm {s : ℝ} (hs : 0 < s) (t : ℝ) (n : ℕ) :
    ‖TtermC s t (-(↑n + 1))‖ = ‖TtermC s t ((n + 1 : ℕ) : ℤ)‖ := by
  have h := TtermC_neg_of_ne s t (m := ((n + 1 : ℕ) : ℤ)) hs
    (by exact_mod_cast Nat.succ_ne_zero n)
  simpa using congrArg norm h

lemma summable_TtermC_nat (s t : ℝ) :
    Summable (fun n : ℕ => TtermC s t (n : ℤ)) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  exact summable_of_isBigO_nat hg (TtermC_nat_isBigO s t)

lemma summable_TtermC_negSucc {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable (fun n : ℕ => TtermC s t (-(↑n + 1))) := by
  have hnat := summable_TtermC_nat s t
  have hpos : Summable (fun n : ℕ => TtermC s t (((n + 1 : ℕ) : ℤ))) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => TtermC s t (n : ℤ)) 1).2 hnat
  exact hpos.norm.of_norm_bounded (fun n => by
    exact le_of_eq (TtermC_negSucc_norm hs t n))

lemma summable_TtermC_int {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable (fun m : ℤ => TtermC s t m) := by
  exact Summable.of_nat_of_neg_add_one
    (summable_TtermC_nat s t)
    (summable_TtermC_negSucc hs t)

/--
The analytic fact still needed for the Poisson formula.  Continuity, decay of
the sample, and summability of the explicit Fourier-side terms are already
proved above; this hypothesis packages only the pointwise Fourier transform
evaluation.
-/
def PoissonKernelFourierFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      (FourierTransform.fourier (poissonKernelSampleC s t) (m : ℝ)).re =
        Tterm s t m

/--
Narrow form of the remaining explicit transform calculation.  It is the
classical half-line Laplace-Bessel identity, after differentiating the
`J₀` transform enough times to account for `(x / 2 + s x ^ 2)`.
-/
def PoissonKernelHalfLineFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      2 * (∫ x in Set.Ioi (0 : ℝ),
        poissonKernelHalfLineIntegrand s t m x).re = Tterm s t m

/-- First Laplace-Bessel moment appearing in the half-line transform. -/
noncomputable def poissonKernelMomentOneIntegrand (s t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(lam s m) * (x : ℂ)) *
    ((x * CircleBessel.J0 (2 * Real.pi * t * x) : ℝ) : ℂ)

/-- Second Laplace-Bessel moment appearing in the half-line transform. -/
noncomputable def poissonKernelMomentTwoIntegrand (s t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(lam s m) * (x : ℂ)) *
    ((x ^ 2 * CircleBessel.J0 (2 * Real.pi * t * x) : ℝ) : ℂ)

lemma poissonKernelMomentOneIntegrand_eq_circleIntegral (s t : ℝ) (m : ℤ) (x : ℝ) :
    poissonKernelMomentOneIntegrand s t m x =
      ∫ θ, (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))
        ∂CircleBessel.unitIntervalMeasure := by
  unfold poissonKernelMomentOneIntegrand
  push_cast
  rw [CircleBessel.J0c_eq_ofReal_J0 (2 * Real.pi * t * x)]
  unfold CircleBessel.J0c
  rw [MeasureTheory.integral_const_mul]
  simp
  ring

lemma poissonKernelMomentTwoIntegrand_eq_circleIntegral (s t : ℝ) (m : ℤ) (x : ℝ) :
    poissonKernelMomentTwoIntegrand s t m x =
      ∫ θ, (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))
        ∂CircleBessel.unitIntervalMeasure := by
  unfold poissonKernelMomentTwoIntegrand
  push_cast
  rw [CircleBessel.J0c_eq_ofReal_J0 (2 * Real.pi * t * x)]
  unfold CircleBessel.J0c
  rw [MeasureTheory.integral_const_mul]
  simp
  ring

lemma integrableOn_cexp_neg_mul_moment_one {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (-a * (x : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun x : ℝ => x * Real.exp (-(a.re * x)))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) ha
    simpa [Real.rpow_one] using h
  refine hbase.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hnorm_exp : ‖Complex.exp (-a * (x : ℂ))‖ = Real.exp (-(a.re * x)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [norm_mul, hnorm_exp]
    simp [Real.norm_eq_abs, abs_of_pos hxpos]

lemma integrableOn_cexp_neg_mul_moment_two {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (-a * (x : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(a.re * x)))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (2 : ℝ))
      (by norm_num : (-1 : ℝ) < 2) (by norm_num : (1 : ℝ) ≤ 1) ha
    simpa [Real.rpow_natCast] using h
  refine hbase.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnorm_exp : ‖Complex.exp (-a * (x : ℂ))‖ = Real.exp (-(a.re * x)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [norm_mul, hnorm_exp]
    simp [Real.norm_eq_abs]

lemma tendsto_cexp_neg_mul_atTop {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => Complex.exp (-a * (x : ℂ))) atTop (𝓝 0) := by
  rw [Complex.tendsto_exp_nhds_zero_iff]
  have hreal : Tendsto (fun x : ℝ => (-a.re) * x) atTop atBot := by
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -a.re < 0)
  refine hreal.congr' ?_
  filter_upwards with x
  simp [Complex.mul_re]

lemma tendsto_cexp_neg_mul_moment_one_atTop {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) * Complex.exp (-a * (x : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hreal : Tendsto (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-a.re * x))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a.re ha
  refine hreal.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hnorm_exp : ‖Complex.exp (-a * (x : ℂ))‖ = Real.exp (-a.re * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [norm_mul, hnorm_exp]
  simp [Real.norm_eq_abs, abs_of_pos hx, Real.rpow_one]

lemma tendsto_cexp_neg_mul_moment_two_atTop {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (-a * (x : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hreal : Tendsto (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-a.re * x))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a.re ha
  refine hreal.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hnorm_exp : ‖Complex.exp (-a * (x : ℂ))‖ = Real.exp (-a.re * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [norm_mul, hnorm_exp]
  simp [Real.norm_eq_abs]

lemma integral_Ioi_cexp_neg_mul_moment_one {a : ℂ} (ha : 0 < a.re) :
    (∫ x in Set.Ioi (0 : ℝ), (x : ℂ) * Complex.exp (-a * (x : ℂ))) =
      1 / a ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro h
    have : a.re = 0 := by simp [h]
    linarith
  let F : ℝ → ℂ := fun y =>
    -Complex.exp (-a * (y : ℂ)) * ((y : ℂ) / a + 1 / a ^ 2)
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt F
      ((x : ℂ) * Complex.exp (-a * (x : ℂ))) x := by
    intro x hx
    dsimp [F]
    have hco : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
    have harg : HasDerivAt (fun y : ℝ => -a * (y : ℂ)) (-a) x := by
      simpa using hco.const_mul (-a)
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (-a * (y : ℂ)))
        (Complex.exp (-a * (x : ℂ)) * (-a)) x := by
      simpa using harg.cexp
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) / a + 1 / a ^ 2) (1 / a) x := by
      simpa using (hco.div_const a).const_add (1 / a ^ 2)
    have hprod := hexp.neg.mul hlin
    convert hprod using 1
    field_simp [ha0]
    simp
    ring_nf
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (-a * (x : ℂ)))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_cexp_neg_mul_moment_one ha
  have hF0 : Tendsto F atTop (𝓝 0) := by
    have hterm1 : Tendsto
        (fun x : ℝ => -(((x : ℂ) * Complex.exp (-a * (x : ℂ))) / a))
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_cexp_neg_mul_moment_one_atTop ha).div_const a |>.neg
    have hterm2 : Tendsto
        (fun x : ℝ => -(Complex.exp (-a * (x : ℂ)) / a ^ 2))
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_cexp_neg_mul_atTop ha).div_const (a ^ 2) |>.neg
    have hsum := hterm1.add hterm2
    have hcongr : F =ᶠ[atTop] fun x : ℝ =>
        -(((x : ℂ) * Complex.exp (-a * (x : ℂ))) / a) +
          -(Complex.exp (-a * (x : ℂ)) / a ^ 2) := by
      filter_upwards with x
      dsimp [F]
      ring
    simpa using hsum.congr' hcongr.symm
  have hcalc := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (f := F)
    (f' := fun x : ℝ => (x : ℂ) * Complex.exp (-a * (x : ℂ))) (m := (0 : ℂ))
    hderiv hint hF0
  simpa [F, ha0] using hcalc

lemma integral_Ioi_cexp_neg_mul_moment_two {a : ℂ} (ha : 0 < a.re) :
    (∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ 2 * Complex.exp (-a * (x : ℂ))) =
      2 / a ^ 3 := by
  have ha0 : a ≠ 0 := by
    intro h
    have : a.re = 0 := by simp [h]
    linarith
  let F : ℝ → ℂ := fun y =>
    -Complex.exp (-a * (y : ℂ)) *
      (((y : ℂ) ^ 2) / a + 2 * (y : ℂ) / a ^ 2 + 2 / a ^ 3)
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt F
      (((x : ℂ) ^ 2) * Complex.exp (-a * (x : ℂ))) x := by
    intro x hx
    dsimp [F]
    have hco : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
    have harg : HasDerivAt (fun y : ℝ => -a * (y : ℂ)) (-a) x := by
      simpa using hco.const_mul (-a)
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (-a * (y : ℂ)))
        (Complex.exp (-a * (x : ℂ)) * (-a)) x := by
      simpa using harg.cexp
    have hpoly : HasDerivAt
        (fun y : ℝ => ((y : ℂ) ^ 2) / a + 2 * (y : ℂ) / a ^ 2 + 2 / a ^ 3)
        (2 * (x : ℂ) / a + 2 / a ^ 2) x := by
      have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (x : ℂ)) x := by
        simpa [two_mul] using hco.pow 2
      have h1 := hsq.div_const a
      have h2 : HasDerivAt (fun y : ℝ => 2 * (y : ℂ) / a ^ 2) (2 / a ^ 2) x := by
        simpa using (hco.const_mul (2 : ℂ)).div_const (a ^ 2)
      simpa [add_assoc] using h1.add (h2.add_const (2 / a ^ 3))
    have hprod := hexp.neg.mul hpoly
    convert hprod using 1
    field_simp [ha0]
    simp only [Pi.neg_apply]
    ring_nf
  have hint : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (-a * (x : ℂ)))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_cexp_neg_mul_moment_two ha
  have hF0 : Tendsto F atTop (𝓝 0) := by
    have hterm1 : Tendsto
        (fun x : ℝ => -((((x : ℂ) ^ 2) * Complex.exp (-a * (x : ℂ))) / a))
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_cexp_neg_mul_moment_two_atTop ha).div_const a |>.neg
    have hterm2 : Tendsto
        (fun x : ℝ => -(2 * ((x : ℂ) * Complex.exp (-a * (x : ℂ))) / a ^ 2))
        atTop (𝓝 0) := by
      have h := (tendsto_cexp_neg_mul_moment_one_atTop ha).const_mul (2 : ℂ)
      simpa [div_eq_mul_inv, mul_assoc] using h.div_const (a ^ 2) |>.neg
    have hterm3 : Tendsto
        (fun x : ℝ => -(2 * Complex.exp (-a * (x : ℂ)) / a ^ 3))
        atTop (𝓝 0) := by
      have h := (tendsto_cexp_neg_mul_atTop ha).const_mul (2 : ℂ)
      simpa [div_eq_mul_inv, mul_assoc] using h.div_const (a ^ 3) |>.neg
    have hsum := (hterm1.add hterm2).add hterm3
    have hcongr : F =ᶠ[atTop] fun x : ℝ =>
        (-((((x : ℂ) ^ 2) * Complex.exp (-a * (x : ℂ))) / a) +
          -(2 * ((x : ℂ) * Complex.exp (-a * (x : ℂ))) / a ^ 2)) +
          -(2 * Complex.exp (-a * (x : ℂ)) / a ^ 3) := by
      filter_upwards with x
      dsimp [F]
      ring
    simpa using hsum.congr' hcongr.symm
  have hcalc := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (f := F)
    (f' := fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (-a * (x : ℂ))) (m := (0 : ℂ))
    hderiv hint hF0
  simpa [F, ha0] using hcalc

/--
The combined angular Laplace parameter after replacing `J₀` by its circle
average:
`exp (-λ x) exp (i β x cos θ) = exp (-(λ - i β cos θ) x)`.
-/
noncomputable def poissonAngularLam (s t : ℝ) (m : ℤ) (θ : ℝ) : ℂ :=
  lam s m - Complex.I * ((2 * Real.pi * t * Real.cos (2 * Real.pi * θ) : ℝ) : ℂ)

noncomputable def poissonAngularDenomCircle (s t : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  lam s m - Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) * ((z + z⁻¹) / 2)

noncomputable def poissonQSqrt (s t : ℝ) (m : ℤ) : ℂ :=
  cpowR (q s t m) (1 / 2 : ℝ)

noncomputable def poissonRootIn (s t : ℝ) (m : ℤ) : ℂ :=
  Complex.I * (poissonQSqrt s t m - lam s m) / ((bOfT t : ℝ) : ℂ)

noncomputable def poissonRootOut (s t : ℝ) (m : ℤ) : ℂ :=
  -Complex.I * (poissonQSqrt s t m + lam s m) / ((bOfT t : ℝ) : ℂ)

noncomputable def poissonDenomFactor (t : ℝ) : ℂ :=
  -Complex.I * ((bOfT t : ℝ) : ℂ) / 2

lemma bOfT_pos {t : ℝ} (ht : 0 < t) : 0 < bOfT t := by
  unfold bOfT
  positivity

lemma q_eq_lam_sq_add_bOfT_sq (s t : ℝ) (m : ℤ) :
    q s t m = (lam s m) ^ 2 + (((bOfT t : ℝ) : ℂ)) ^ 2 := by
  unfold q bOfT
  push_cast
  ring

lemma q_re (s t : ℝ) (m : ℤ) :
    (q s t m).re =
      s ^ 2 - (2 * Real.pi * (m : ℝ)) ^ 2 + (bOfT t) ^ 2 := by
  unfold q lam bOfT
  simp [pow_two, Complex.add_re, Complex.mul_re]

lemma q_ne_zero_of_s_pos {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    q s t m ≠ 0 := by
  by_cases hm : m = 0
  · subst m
    intro hq
    have hre : (q s t 0).re = 0 := by simp [hq]
    rw [q_re] at hre
    norm_num at hre
    have hs_sq_pos : 0 < s ^ 2 := sq_pos_of_pos hs
    have hb_sq_nonneg : 0 ≤ (bOfT t) ^ 2 := sq_nonneg _
    nlinarith
  · intro hq
    have him : (q s t m).im = 0 := by simp [hq]
    have him_ne : (q s t m).im ≠ 0 := by
      rw [q_im]
      positivity
    exact him_ne him

lemma q_arg_ne_pi_of_s_pos {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    Complex.arg (q s t m) ≠ Real.pi := by
  by_cases hm : m = 0
  · subst m
    rw [Ne, Complex.arg_eq_pi_iff]
    intro h
    rw [q_re] at h
    norm_num at h
    have hs_sq_pos : 0 < s ^ 2 := sq_pos_of_pos hs
    have hb_sq_nonneg : 0 ≤ (bOfT t) ^ 2 := sq_nonneg _
    nlinarith
  · exact q_arg_ne_pi hs hm

lemma norm_add_re_pos_of_arg_ne_pi {z : ℂ} (hz0 : z ≠ 0)
    (harg : Complex.arg z ≠ Real.pi) :
    0 < ‖z‖ + z.re := by
  by_contra hle'
  have hle : z.re ≤ -‖z‖ := by linarith
  have hz_eq : z = -((‖z‖ : ℝ) : ℂ) :=
    (RCLike.re_le_neg_norm_iff_eq_neg_norm (K := ℂ)).1 hle
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have harg_eq : Complex.arg z = Real.pi := by
    rw [hz_eq]
    simpa using Complex.arg_ofReal_of_neg (show -(‖z‖ : ℝ) < 0 by linarith)
  exact harg harg_eq

lemma poissonQSqrt_sq {s t : ℝ} (m : ℤ) :
    (poissonQSqrt s t m) ^ 2 = q s t m := by
  unfold poissonQSqrt cpowR
  have hpow := Complex.cpow_nat_inv_pow (q s t m) (n := 2) (by norm_num)
  norm_num [one_div] at hpow ⊢
  exact hpow

lemma poissonQSqrt_ne_zero {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    poissonQSqrt s t m ≠ 0 := by
  intro h
  have hsq := poissonQSqrt_sq (s := s) (t := t) m
  rw [h] at hsq
  simp at hsq
  exact q_ne_zero_of_s_pos (s := s) (t := t) hs m hsq.symm

lemma cpowR_q_neg_three_halves_eq_qsqrt_zpow (s t : ℝ) (m : ℤ) :
    cpowR (q s t m) (-(3 / 2 : ℝ)) = (poissonQSqrt s t m) ^ (-3 : ℤ) := by
  unfold cpowR
  simp only [poissonQSqrt, cpowR]
  have hhalf : (((-(3 / 2 : ℝ) : ℝ) : ℂ)) =
      (-3 : ℤ) * (((1 / 2 : ℝ) : ℂ)) := by
    norm_num [div_eq_mul_inv]
  rw [hhalf]
  rw [Complex.cpow_int_mul]

lemma cpowR_q_neg_five_halves_eq_qsqrt_zpow (s t : ℝ) (m : ℤ) :
    cpowR (q s t m) (-(5 / 2 : ℝ)) = (poissonQSqrt s t m) ^ (-5 : ℤ) := by
  unfold cpowR
  simp only [poissonQSqrt, cpowR]
  have hhalf : (((-(5 / 2 : ℝ) : ℝ) : ℂ)) =
      (-5 : ℤ) * (((1 / 2 : ℝ) : ℂ)) := by
    norm_num [div_eq_mul_inv]
  rw [hhalf]
  rw [Complex.cpow_int_mul]

lemma poissonQSqrt_re_pos {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    0 < (poissonQSqrt s t m).re := by
  unfold poissonQSqrt cpowR
  rw [show (((1 / 2 : ℝ) : ℂ)) = (2⁻¹ : ℂ) by norm_num]
  rw [Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.2
  have hpos : 0 < ‖q s t m‖ + (q s t m).re :=
    norm_add_re_pos_of_arg_ne_pi (z := q s t m)
      (q_ne_zero_of_s_pos (s := s) (t := t) hs m)
      (q_arg_ne_pi_of_s_pos (s := s) (t := t) hs m)
  nlinarith

lemma poissonQSqrt_re_gt_s {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (m : ℤ) :
    s < (poissonQSqrt s t m).re := by
  let u := (poissonQSqrt s t m).re
  let v := (poissonQSqrt s t m).im
  let a := 2 * Real.pi * (m : ℝ)
  let B := bOfT t
  have hu : 0 < u := by
    simpa [u] using poissonQSqrt_re_pos (s := s) (t := t) hs m
  have hB : 0 < B := by
    simpa [B] using bOfT_pos ht
  have hreal : u ^ 2 - v ^ 2 = s ^ 2 - a ^ 2 + B ^ 2 := by
    have h := congrArg Complex.re (poissonQSqrt_sq (s := s) (t := t) m)
    rw [q_re] at h
    simpa [u, v, a, B, pow_two, Complex.mul_re] using h
  have him : u * v = s * a := by
    have h := congrArg Complex.im (poissonQSqrt_sq (s := s) (t := t) m)
    rw [q_im] at h
    simp [pow_two, Complex.mul_im] at h
    nlinarith
  have himsq : (u * v) ^ 2 = (s * a) ^ 2 := by rw [him]
  have hprod : (u ^ 2 - s ^ 2) * (u ^ 2 + a ^ 2) = B ^ 2 * u ^ 2 := by
    nlinarith [hreal, himsq]
  have hprod_pos : 0 < (u ^ 2 - s ^ 2) * (u ^ 2 + a ^ 2) := by
    rw [hprod]
    positivity
  have hfactor_nonneg : 0 ≤ u ^ 2 + a ^ 2 := by positivity
  have hsquare : 0 < u ^ 2 - s ^ 2 := by
    exact pos_of_mul_pos_left hprod_pos hfactor_nonneg
  nlinarith

lemma poissonQSqrt_sub_lam_normSq_lt_bOfT_sq {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (m : ℤ) :
    Complex.normSq (poissonQSqrt s t m - lam s m) < (bOfT t) ^ 2 := by
  let u := (poissonQSqrt s t m).re
  let v := (poissonQSqrt s t m).im
  let a := 2 * Real.pi * (m : ℝ)
  let B := bOfT t
  have hu_gt : s < u := by
    simpa [u] using poissonQSqrt_re_gt_s (s := s) (t := t) hs ht m
  have hreal : u ^ 2 - v ^ 2 = s ^ 2 - a ^ 2 + B ^ 2 := by
    have h := congrArg Complex.re (poissonQSqrt_sq (s := s) (t := t) m)
    rw [q_re] at h
    simpa [u, v, a, B, pow_two, Complex.mul_re] using h
  have him : u * v = s * a := by
    have h := congrArg Complex.im (poissonQSqrt_sq (s := s) (t := t) m)
    rw [q_im] at h
    simp [pow_two, Complex.mul_im] at h
    nlinarith
  have himv : u * v ^ 2 = s * a * v := by
    calc
      u * v ^ 2 = (u * v) * v := by ring
      _ = (s * a) * v := by rw [him]
      _ = s * a * v := by ring
  have hdiff : s * (B ^ 2 - ((u - s) ^ 2 + (v - a) ^ 2)) =
      2 * (u - s) * (s ^ 2 + v ^ 2) := by
    nlinarith [hreal, himv]
  have hs2v2_pos : 0 < s ^ 2 + v ^ 2 := by
    nlinarith [sq_pos_of_pos hs, sq_nonneg v]
  have hu_sub_pos : 0 < u - s := by linarith
  have hright_pos : 0 < 2 * (u - s) * (s ^ 2 + v ^ 2) :=
    mul_pos (mul_pos (by norm_num) hu_sub_pos) hs2v2_pos
  have hdiff_pos : 0 < B ^ 2 - ((u - s) ^ 2 + (v - a) ^ 2) := by
    nlinarith [hdiff, hright_pos, hs]
  have hnorm : Complex.normSq (poissonQSqrt s t m - lam s m) =
      (u - s) ^ 2 + (v - a) ^ 2 := by
    unfold u v a
    unfold lam
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, pow_two]
  rw [hnorm]
  linarith

lemma bOfT_sq_lt_poissonQSqrt_add_lam_normSq {s t : ℝ}
    (hs : 0 < s) (m : ℤ) :
    (bOfT t) ^ 2 < Complex.normSq (poissonQSqrt s t m + lam s m) := by
  let u := (poissonQSqrt s t m).re
  let v := (poissonQSqrt s t m).im
  let a := 2 * Real.pi * (m : ℝ)
  let B := bOfT t
  have hu : 0 < u := by
    simpa [u] using poissonQSqrt_re_pos (s := s) (t := t) hs m
  have hreal : u ^ 2 - v ^ 2 = s ^ 2 - a ^ 2 + B ^ 2 := by
    have h := congrArg Complex.re (poissonQSqrt_sq (s := s) (t := t) m)
    rw [q_re] at h
    simpa [u, v, a, B, pow_two, Complex.mul_re] using h
  have him : u * v = s * a := by
    have h := congrArg Complex.im (poissonQSqrt_sq (s := s) (t := t) m)
    rw [q_im] at h
    simp [pow_two, Complex.mul_im] at h
    nlinarith
  have himv : u * v ^ 2 = s * a * v := by
    calc
      u * v ^ 2 = (u * v) * v := by ring
      _ = (s * a) * v := by rw [him]
      _ = s * a * v := by ring
  have hdiff : s * (((u + s) ^ 2 + (v + a) ^ 2) - B ^ 2) =
      2 * (u + s) * (s ^ 2 + v ^ 2) := by
    nlinarith [hreal, himv]
  have hs2v2_pos : 0 < s ^ 2 + v ^ 2 := by
    nlinarith [sq_pos_of_pos hs, sq_nonneg v]
  have hu_add_pos : 0 < u + s := by linarith
  have hright_pos : 0 < 2 * (u + s) * (s ^ 2 + v ^ 2) :=
    mul_pos (mul_pos (by norm_num) hu_add_pos) hs2v2_pos
  have hdiff_pos : 0 < ((u + s) ^ 2 + (v + a) ^ 2) - B ^ 2 := by
    nlinarith [hdiff, hright_pos, hs]
  have hnorm : Complex.normSq (poissonQSqrt s t m + lam s m) =
      (u + s) ^ 2 + (v + a) ^ 2 := by
    unfold u v a
    unfold lam
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  rw [hnorm]
  linarith

lemma poissonRootIn_mem_ball {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (m : ℤ) :
    poissonRootIn s t m ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  have hBpos : 0 < bOfT t := bOfT_pos ht
  have hBnormSq : Complex.normSq (((bOfT t : ℝ) : ℂ)) = (bOfT t) ^ 2 := by
    rw [Complex.normSq_ofReal]
    ring
  have hnormSq_lt : Complex.normSq (poissonRootIn s t m) < 1 := by
    unfold poissonRootIn
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_I, one_mul, hBnormSq]
    rw [div_lt_one (sq_pos_of_pos hBpos)]
    exact poissonQSqrt_sub_lam_normSq_lt_bOfT_sq (s := s) (t := t) hs ht m
  have hsq : ‖poissonRootIn s t m‖ ^ 2 < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormSq_lt
  have habs : |‖poissonRootIn s t m‖| < 1 := (sq_lt_one_iff_abs_lt_one _).1 hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

lemma one_lt_norm_poissonRootOut {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (m : ℤ) :
    1 < ‖poissonRootOut s t m‖ := by
  have hBpos : 0 < bOfT t := bOfT_pos ht
  have hBnormSq : Complex.normSq (((bOfT t : ℝ) : ℂ)) = (bOfT t) ^ 2 := by
    rw [Complex.normSq_ofReal]
    ring
  have hnormSq_gt : 1 < Complex.normSq (poissonRootOut s t m) := by
    unfold poissonRootOut
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I,
      one_mul, hBnormSq]
    rw [one_lt_div (sq_pos_of_pos hBpos)]
    exact bOfT_sq_lt_poissonQSqrt_add_lam_normSq (s := s) (t := t) hs m
  have hsq : (1 : ℝ) ^ 2 < ‖poissonRootOut s t m‖ ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormSq_gt
  have habs : |(1 : ℝ)| < |‖poissonRootOut s t m‖| := (sq_lt_sq).1 hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

lemma poissonRoot_sub {s t : ℝ} (ht : 0 < t) (m : ℤ) :
    poissonRootIn s t m - poissonRootOut s t m =
      2 * Complex.I * poissonQSqrt s t m / (((bOfT t : ℝ) : ℂ)) := by
  have hB : (((bOfT t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (bOfT_pos ht))
  unfold poissonRootIn poissonRootOut
  field_simp [hB]
  ring

lemma poissonRoot_add {s t : ℝ} (ht : 0 < t) (m : ℤ) :
    poissonRootIn s t m + poissonRootOut s t m =
      -2 * Complex.I * lam s m / (((bOfT t : ℝ) : ℂ)) := by
  have hB : (((bOfT t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (bOfT_pos ht))
  unfold poissonRootIn poissonRootOut
  field_simp [hB]
  ring

lemma poissonAngularDenomCircle_factor {s t : ℝ} (ht : 0 < t)
    (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    poissonAngularDenomCircle s t m z =
      poissonDenomFactor t / z * (z - poissonRootIn s t m) *
        (z - poissonRootOut s t m) := by
  have hB : (((bOfT t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (bOfT_pos ht))
  have hSsq := poissonQSqrt_sq (s := s) (t := t) m
  rw [q_eq_lam_sq_add_bOfT_sq] at hSsq
  unfold poissonAngularDenomCircle poissonDenomFactor poissonRootIn poissonRootOut
  field_simp [hz, hB]
  simp [bOfT] at hSsq ⊢
  ring_nf at hSsq ⊢
  rw [hSsq]
  simp [Complex.I_sq]
  ring

lemma poissonDenomFactor_ne_zero {t : ℝ} (ht : 0 < t) :
    poissonDenomFactor t ≠ 0 := by
  unfold poissonDenomFactor
  have hB : (((bOfT t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (bOfT_pos ht))
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hB) (by norm_num)

lemma poissonAngularDenomCircle_factor_sq_integrand {s t : ℝ} (ht : 0 < t)
    (m : ℤ) {z : ℂ} (hz0 : z ≠ 0) :
    (z - 0)⁻¹ • (1 / (poissonAngularDenomCircle s t m z) ^ 2) =
      z / (poissonDenomFactor t) ^ 2 /
        ((z - poissonRootIn s t m) ^ 2 * (z - poissonRootOut s t m) ^ 2) := by
  have hC : poissonDenomFactor t ≠ 0 := poissonDenomFactor_ne_zero ht
  rw [poissonAngularDenomCircle_factor (s := s) (t := t) ht m hz0]
  simp [smul_eq_mul]
  field_simp [hz0, hC]

lemma poissonAngularDenomCircle_factor_cube_integrand {s t : ℝ} (ht : 0 < t)
    (m : ℤ) {z : ℂ} (hz0 : z ≠ 0) :
    (z - 0)⁻¹ • (2 / (poissonAngularDenomCircle s t m z) ^ 3) =
      2 * z ^ 2 / (poissonDenomFactor t) ^ 3 /
        ((z - poissonRootIn s t m) ^ 3 * (z - poissonRootOut s t m) ^ 3) := by
  have hC : poissonDenomFactor t ≠ 0 := poissonDenomFactor_ne_zero ht
  rw [poissonAngularDenomCircle_factor (s := s) (t := t) ht m hz0]
  simp [smul_eq_mul]
  field_simp [hz0, hC]

lemma double_pole_coefficient_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (m : ℤ) :
    -(poissonRootIn s t m + poissonRootOut s t m) /
        (poissonDenomFactor t ^ 2 * (poissonRootIn s t m - poissonRootOut s t m) ^ 3) =
      (lam s m) * (poissonQSqrt s t m) ^ (-3 : ℤ) := by
  have hB : (((bOfT t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (bOfT_pos ht))
  have hS : poissonQSqrt s t m ≠ 0 := poissonQSqrt_ne_zero (s := s) (t := t) hs m
  rw [poissonRoot_add (s := s) (t := t) ht m]
  rw [poissonRoot_sub (s := s) (t := t) ht m]
  unfold poissonDenomFactor
  field_simp [hB, hS]
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    norm_num [Complex.I_mul_I, pow_succ]
  rw [hI4]
  ring

lemma triple_pole_coefficient_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (m : ℤ) :
    (1 / poissonDenomFactor t ^ 3) *
        (2 / (poissonRootIn s t m - poissonRootOut s t m) ^ 3 -
          12 * poissonRootIn s t m / (poissonRootIn s t m - poissonRootOut s t m) ^ 4 +
          12 * (poissonRootIn s t m) ^ 2 /
            (poissonRootIn s t m - poissonRootOut s t m) ^ 5) =
      -(poissonQSqrt s t m) ^ (-3 : ℤ) +
        3 * (lam s m) ^ 2 * (poissonQSqrt s t m) ^ (-5 : ℤ) := by
  have hB : (((bOfT t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (bOfT_pos ht))
  have hS : poissonQSqrt s t m ≠ 0 := poissonQSqrt_ne_zero (s := s) (t := t) hs m
  rw [poissonRoot_sub (s := s) (t := t) ht m]
  unfold poissonRootIn poissonDenomFactor
  field_simp [hB, hS]
  have hI6 : (Complex.I : ℂ) ^ 6 = -1 := by
    norm_num [Complex.I_mul_I, pow_succ]
  rw [hI6]
  ring

lemma circleIntegral_sub_inv_of_one_lt_norm {w : ℂ} (hw : 1 < ‖w‖) :
    (∮ z in C((0 : ℂ), (1 : ℝ)), (z - w)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (R := (1 : ℝ)) (c := (0 : ℂ)) (by norm_num)
    (s := (∅ : Set ℂ)) Set.countable_empty
  · refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz hzero
    have hz_norm : ‖z‖ ≤ 1 := by
      simpa [mem_closedBall_zero_iff] using hz
    have : z = w := by simpa using sub_eq_zero.mp hzero
    subst z
    linarith
  · intro z hz
    refine ((differentiableAt_id.sub (differentiableAt_const (𝕜 := ℂ) w))).inv ?_
    intro hzero
    have hz_norm : ‖z‖ < 1 := by
      have hzball : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
      simpa [mem_ball_zero_iff] using hzball
    have : z = w := by simpa using sub_eq_zero.mp hzero
    subst z
    linarith

lemma rational_double_pole_partial_fraction {r R C z : ℂ}
    (hC : C ≠ 0) (hrR : r ≠ R) (hzr : z ≠ r) (hzR : z ≠ R) :
    z / C ^ 2 / ((z - r) ^ 2 * (z - R) ^ 2) =
      (r / (C ^ 2 * (r - R) ^ 2)) / (z - r) ^ 2 +
      (-(r + R) / (C ^ 2 * (r - R) ^ 3)) / (z - r) +
      (R / (C ^ 2 * (r - R) ^ 2)) / (z - R) ^ 2 +
      ((r + R) / (C ^ 2 * (r - R) ^ 3)) / (z - R) := by
  have hd : r - R ≠ 0 := sub_ne_zero.mpr hrR
  have hzrd : z - r ≠ 0 := sub_ne_zero.mpr hzr
  have hzRd : z - R ≠ 0 := sub_ne_zero.mpr hzR
  field_simp [hC, hd, hzrd, hzRd]
  ring

lemma rational_double_pole_partial_fraction_zpow {r R C z : ℂ}
    (hC : C ≠ 0) (hrR : r ≠ R) (hzr : z ≠ r) (hzR : z ≠ R) :
    z / C ^ 2 / ((z - r) ^ 2 * (z - R) ^ 2) =
      (r / (C ^ 2 * (r - R) ^ 2)) • ((z - r) ^ (-2 : ℤ)) +
        ((-(r + R) / (C ^ 2 * (r - R) ^ 3)) • ((z - r) ^ (-1 : ℤ)) +
          ((R / (C ^ 2 * (r - R) ^ 2)) • ((z - R) ^ (-2 : ℤ)) +
            (((r + R) / (C ^ 2 * (r - R) ^ 3)) • ((z - R) ^ (-1 : ℤ))))) := by
  have hd : r - R ≠ 0 := sub_ne_zero.mpr hrR
  have hzrd : z - r ≠ 0 := sub_ne_zero.mpr hzr
  have hzRd : z - R ≠ 0 := sub_ne_zero.mpr hzR
  simp [smul_eq_mul, zpow_neg, div_eq_mul_inv]
  field_simp [hC, hd, hzrd, hzRd]
  ring

lemma rational_triple_pole_partial_fraction {r R C z : ℂ}
    (hC : C ≠ 0) (hrR : r ≠ R) (hzr : z ≠ r) (hzR : z ≠ R) :
    2 * z ^ 2 / C ^ 3 / ((z - r) ^ 3 * (z - R) ^ 3) =
      (2 * r ^ 2 / (C ^ 3 * (r - R) ^ 3)) / (z - r) ^ 3 +
      ((2 / C ^ 3) *
          (2 * r / (r - R) ^ 3 - 3 * r ^ 2 / (r - R) ^ 4)) / (z - r) ^ 2 +
      ((1 / C ^ 3) *
          (2 / (r - R) ^ 3 - 12 * r / (r - R) ^ 4 +
            12 * r ^ 2 / (r - R) ^ 5)) / (z - r) +
      (-2 * R ^ 2 / (C ^ 3 * (r - R) ^ 3)) / (z - R) ^ 3 +
      ((2 / C ^ 3) *
          (-2 * R / (r - R) ^ 3 - 3 * R ^ 2 / (r - R) ^ 4)) / (z - R) ^ 2 +
      ((1 / C ^ 3) *
          (-2 / (r - R) ^ 3 - 12 * R / (r - R) ^ 4 -
            12 * R ^ 2 / (r - R) ^ 5)) / (z - R) := by
  have hd : r - R ≠ 0 := sub_ne_zero.mpr hrR
  have hzrd : z - r ≠ 0 := sub_ne_zero.mpr hzr
  have hzRd : z - R ≠ 0 := sub_ne_zero.mpr hzR
  field_simp [hC, hd, hzrd, hzRd]
  ring

lemma rational_triple_pole_partial_fraction_zpow {r R C z : ℂ}
    (hC : C ≠ 0) (hrR : r ≠ R) (hzr : z ≠ r) (hzR : z ≠ R) :
    2 * z ^ 2 / C ^ 3 / ((z - r) ^ 3 * (z - R) ^ 3) =
      (2 * r ^ 2 / (C ^ 3 * (r - R) ^ 3)) • ((z - r) ^ (-3 : ℤ)) +
        (((2 / C ^ 3) *
            (2 * r / (r - R) ^ 3 - 3 * r ^ 2 / (r - R) ^ 4)) •
            ((z - r) ^ (-2 : ℤ)) +
          (((1 / C ^ 3) *
              (2 / (r - R) ^ 3 - 12 * r / (r - R) ^ 4 +
                12 * r ^ 2 / (r - R) ^ 5)) • ((z - r) ^ (-1 : ℤ)) +
            ((-2 * R ^ 2 / (C ^ 3 * (r - R) ^ 3)) • ((z - R) ^ (-3 : ℤ)) +
              (((2 / C ^ 3) *
                  (-2 * R / (r - R) ^ 3 - 3 * R ^ 2 / (r - R) ^ 4)) •
                  ((z - R) ^ (-2 : ℤ)) +
                (((1 / C ^ 3) *
                    (-2 / (r - R) ^ 3 - 12 * R / (r - R) ^ 4 -
                      12 * R ^ 2 / (r - R) ^ 5)) • ((z - R) ^ (-1 : ℤ))))))) := by
  have hd : r - R ≠ 0 := sub_ne_zero.mpr hrR
  have hzrd : z - r ≠ 0 := sub_ne_zero.mpr hzr
  have hzRd : z - R ≠ 0 := sub_ne_zero.mpr hzR
  simp [smul_eq_mul, zpow_neg, div_eq_mul_inv]
  field_simp [hC, hd, hzrd, hzRd]
  ring

lemma circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere
    (A w : ℂ) (n : ℤ) (hw : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), z ≠ w) :
    CircleIntegrable (fun z : ℂ => A • ((z - w) ^ n)) (0 : ℂ) (1 : ℝ) := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  have hsub : ContinuousOn (fun z : ℂ => z - w) (Metric.sphere (0 : ℂ) (1 : ℝ)) := by
    exact (continuousOn_id' (Metric.sphere (0 : ℂ) (1 : ℝ))).sub continuousOn_const
  have hzpow : ContinuousOn (fun z : ℂ => (z - w) ^ n)
      (Metric.sphere (0 : ℂ) (1 : ℝ)) := by
    refine hsub.zpow₀ n ?_
    intro z hz
    exact Or.inl (sub_ne_zero.mpr (hw z hz))
  exact hzpow.const_smul A

lemma circleIntegral_const_smul_sub_zpow_of_ne (A w : ℂ) {n : ℤ} (hn : n ≠ -1) :
    (∮ z in C((0 : ℂ), (1 : ℝ)), A • ((z - w) ^ n)) = 0 := by
  rw [circleIntegral.integral_smul]
  rw [circleIntegral.integral_sub_zpow_of_ne hn]
  simp

lemma circleIntegral_const_smul_sub_inv_of_mem_unit_ball {w A : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) (1 : ℝ)) :
    (∮ z in C((0 : ℂ), (1 : ℝ)), A • ((z - w) ^ (-1 : ℤ))) =
      A • (2 * Complex.ofReal Real.pi * Complex.I) := by
  rw [circleIntegral.integral_smul]
  rw [show (fun z : ℂ => (z - w) ^ (-1 : ℤ)) = fun z => (z - w)⁻¹ by
    funext z
    simp]
  rw [circleIntegral.integral_sub_inv_of_mem_ball hw]

lemma circleIntegral_const_smul_sub_inv_of_one_lt_norm {w A : ℂ} (hw : 1 < ‖w‖) :
    (∮ z in C((0 : ℂ), (1 : ℝ)), A • ((z - w) ^ (-1 : ℤ))) = 0 := by
  rw [circleIntegral.integral_smul]
  rw [show (fun z : ℂ => (z - w) ^ (-1 : ℤ)) = fun z => (z - w)⁻¹ by
    funext z
    simp]
  rw [circleIntegral_sub_inv_of_one_lt_norm hw]
  simp

lemma normalized_circleIntegral_double_pole {r R C : ℂ}
    (hr : r ∈ Metric.ball (0 : ℂ) (1 : ℝ)) (hR : 1 < ‖R‖) (hC : C ≠ 0) :
    ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
      (∮ z in C((0 : ℂ), (1 : ℝ)),
        z / C ^ 2 / ((z - r) ^ 2 * (z - R) ^ 2))) =
      -(r + R) / (C ^ 2 * (r - R) ^ 3) := by
  have hr_norm : ‖r‖ < 1 := by simpa [mem_ball_zero_iff] using hr
  have hrR : r ≠ R := by
    intro h
    subst R
    linarith
  have hSphere_r : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), z ≠ r := by
    intro z hz hzr
    have hz_norm : ‖z‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hz
    subst z
    linarith
  have hSphere_R : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), z ≠ R := by
    intro z hz hzR
    have hz_norm : ‖z‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hz
    subst z
    linarith
  let A1 : ℂ := r / (C ^ 2 * (r - R) ^ 2)
  let B1 : ℂ := -(r + R) / (C ^ 2 * (r - R) ^ 3)
  let A2 : ℂ := R / (C ^ 2 * (r - R) ^ 2)
  let B2 : ℂ := (r + R) / (C ^ 2 * (r - R) ^ 3)
  let f1 : ℂ → ℂ := fun z => A1 • ((z - r) ^ (-2 : ℤ))
  let f2 : ℂ → ℂ := fun z => B1 • ((z - r) ^ (-1 : ℤ))
  let f3 : ℂ → ℂ := fun z => A2 • ((z - R) ^ (-2 : ℤ))
  let f4 : ℂ → ℂ := fun z => B2 • ((z - R) ^ (-1 : ℤ))
  have hcongr : (∮ z in C((0 : ℂ), (1 : ℝ)),
        z / C ^ 2 / ((z - r) ^ 2 * (z - R) ^ 2)) =
      ∮ z in C((0 : ℂ), (1 : ℝ)), f1 z + (f2 z + (f3 z + f4 z)) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hzr := hSphere_r z hz
    have hzR := hSphere_R z hz
    dsimp [f1, f2, f3, f4, A1, B1, A2, B2]
    exact rational_double_pole_partial_fraction_zpow (C := C) (r := r) (R := R)
      (z := z) hC hrR hzr hzR
  rw [hcongr]
  have hf1 : CircleIntegrable f1 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere A1 r (-2) hSphere_r
  have hf2 : CircleIntegrable f2 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere B1 r (-1) hSphere_r
  have hf3 : CircleIntegrable f3 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere A2 R (-2) hSphere_R
  have hf4 : CircleIntegrable f4 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere B2 R (-1) hSphere_R
  rw [circleIntegral.integral_add (f := f1) (g := fun z => f2 z + (f3 z + f4 z))
    hf1 (hf2.add (hf3.add hf4))]
  rw [circleIntegral.integral_add (f := f2) (g := fun z => f3 z + f4 z)
    hf2 (hf3.add hf4)]
  rw [circleIntegral.integral_add (f := f3) (g := f4) hf3 hf4]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f1 z) = 0 by
    dsimp [f1]
    exact circleIntegral_const_smul_sub_zpow_of_ne A1 r (by decide : (-2 : ℤ) ≠ -1)]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f2 z) =
      B1 • (2 * Complex.ofReal Real.pi * Complex.I) by
    dsimp [f2]
    exact circleIntegral_const_smul_sub_inv_of_mem_unit_ball (w := r) (A := B1) hr]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f3 z) = 0 by
    dsimp [f3]
    exact circleIntegral_const_smul_sub_zpow_of_ne A2 R (by decide : (-2 : ℤ) ≠ -1)]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f4 z) = 0 by
    dsimp [f4]
    exact circleIntegral_const_smul_sub_inv_of_one_lt_norm (w := R) (A := B2) hR]
  simp only [zero_add, add_zero]
  dsimp [B1]
  field_simp [Complex.two_pi_I_ne_zero]

lemma normalized_circleIntegral_triple_pole {r R C : ℂ}
    (hr : r ∈ Metric.ball (0 : ℂ) (1 : ℝ)) (hR : 1 < ‖R‖) (hC : C ≠ 0) :
    ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
      (∮ z in C((0 : ℂ), (1 : ℝ)),
        2 * z ^ 2 / C ^ 3 / ((z - r) ^ 3 * (z - R) ^ 3))) =
      (1 / C ^ 3) *
        (2 / (r - R) ^ 3 - 12 * r / (r - R) ^ 4 + 12 * r ^ 2 / (r - R) ^ 5) := by
  have hr_norm : ‖r‖ < 1 := by simpa [mem_ball_zero_iff] using hr
  have hrR : r ≠ R := by
    intro h
    subst R
    linarith
  have hSphere_r : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), z ≠ r := by
    intro z hz hzr
    have hz_norm : ‖z‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hz
    subst z
    linarith
  have hSphere_R : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), z ≠ R := by
    intro z hz hzR
    have hz_norm : ‖z‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hz
    subst z
    linarith
  let A3 : ℂ := 2 * r ^ 2 / (C ^ 3 * (r - R) ^ 3)
  let A2 : ℂ := (2 / C ^ 3) * (2 * r / (r - R) ^ 3 - 3 * r ^ 2 / (r - R) ^ 4)
  let A1 : ℂ := (1 / C ^ 3) *
    (2 / (r - R) ^ 3 - 12 * r / (r - R) ^ 4 + 12 * r ^ 2 / (r - R) ^ 5)
  let B3 : ℂ := -2 * R ^ 2 / (C ^ 3 * (r - R) ^ 3)
  let B2 : ℂ := (2 / C ^ 3) *
    (-2 * R / (r - R) ^ 3 - 3 * R ^ 2 / (r - R) ^ 4)
  let B1 : ℂ := (1 / C ^ 3) *
    (-2 / (r - R) ^ 3 - 12 * R / (r - R) ^ 4 - 12 * R ^ 2 / (r - R) ^ 5)
  let f1 : ℂ → ℂ := fun z => A3 • ((z - r) ^ (-3 : ℤ))
  let f2 : ℂ → ℂ := fun z => A2 • ((z - r) ^ (-2 : ℤ))
  let f3 : ℂ → ℂ := fun z => A1 • ((z - r) ^ (-1 : ℤ))
  let f4 : ℂ → ℂ := fun z => B3 • ((z - R) ^ (-3 : ℤ))
  let f5 : ℂ → ℂ := fun z => B2 • ((z - R) ^ (-2 : ℤ))
  let f6 : ℂ → ℂ := fun z => B1 • ((z - R) ^ (-1 : ℤ))
  have hcongr : (∮ z in C((0 : ℂ), (1 : ℝ)),
        2 * z ^ 2 / C ^ 3 / ((z - r) ^ 3 * (z - R) ^ 3)) =
      ∮ z in C((0 : ℂ), (1 : ℝ)),
        f1 z + (f2 z + (f3 z + (f4 z + (f5 z + f6 z)))) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hzr := hSphere_r z hz
    have hzR := hSphere_R z hz
    dsimp [f1, f2, f3, f4, f5, f6, A1, A2, A3, B1, B2, B3]
    exact rational_triple_pole_partial_fraction_zpow (C := C) (r := r) (R := R)
      (z := z) hC hrR hzr hzR
  rw [hcongr]
  have hf1 : CircleIntegrable f1 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere A3 r (-3) hSphere_r
  have hf2 : CircleIntegrable f2 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere A2 r (-2) hSphere_r
  have hf3 : CircleIntegrable f3 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere A1 r (-1) hSphere_r
  have hf4 : CircleIntegrable f4 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere B3 R (-3) hSphere_R
  have hf5 : CircleIntegrable f5 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere B2 R (-2) hSphere_R
  have hf6 : CircleIntegrable f6 (0 : ℂ) (1 : ℝ) := by
    exact circleIntegrable_const_smul_sub_zpow_of_ne_on_unit_sphere B1 R (-1) hSphere_R
  rw [circleIntegral.integral_add (f := f1)
    (g := fun z => f2 z + (f3 z + (f4 z + (f5 z + f6 z))))
    hf1 (hf2.add (hf3.add (hf4.add (hf5.add hf6))))]
  rw [circleIntegral.integral_add (f := f2)
    (g := fun z => f3 z + (f4 z + (f5 z + f6 z)))
    hf2 (hf3.add (hf4.add (hf5.add hf6)))]
  rw [circleIntegral.integral_add (f := f3)
    (g := fun z => f4 z + (f5 z + f6 z)) hf3 (hf4.add (hf5.add hf6))]
  rw [circleIntegral.integral_add (f := f4) (g := fun z => f5 z + f6 z)
    hf4 (hf5.add hf6)]
  rw [circleIntegral.integral_add (f := f5) (g := f6) hf5 hf6]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f1 z) = 0 by
    dsimp [f1]
    exact circleIntegral_const_smul_sub_zpow_of_ne A3 r (by decide : (-3 : ℤ) ≠ -1)]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f2 z) = 0 by
    dsimp [f2]
    exact circleIntegral_const_smul_sub_zpow_of_ne A2 r (by decide : (-2 : ℤ) ≠ -1)]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f3 z) =
      A1 • (2 * Complex.ofReal Real.pi * Complex.I) by
    dsimp [f3]
    exact circleIntegral_const_smul_sub_inv_of_mem_unit_ball (w := r) (A := A1) hr]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f4 z) = 0 by
    dsimp [f4]
    exact circleIntegral_const_smul_sub_zpow_of_ne B3 R (by decide : (-3 : ℤ) ≠ -1)]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f5 z) = 0 by
    dsimp [f5]
    exact circleIntegral_const_smul_sub_zpow_of_ne B2 R (by decide : (-2 : ℤ) ≠ -1)]
  rw [show (∮ z in C((0 : ℂ), (1 : ℝ)), f6 z) = 0 by
    dsimp [f6]
    exact circleIntegral_const_smul_sub_inv_of_one_lt_norm (w := R) (A := B1) hR]
  simp only [zero_add, add_zero]
  dsimp [A1]
  field_simp [Complex.two_pi_I_ne_zero]

lemma poissonAngularLam_re (s t : ℝ) (m : ℤ) (θ : ℝ) :
    (poissonAngularLam s t m θ).re = s := by
  let r : ℝ := 2 * Real.pi * t * Real.cos (2 * Real.pi * θ)
  have hI : (Complex.I * (r : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  change (lam s m - Complex.I * (r : ℂ)).re = s
  rw [Complex.sub_re, hI, lam_re]
  ring_nf

lemma poissonAngularLam_re_pos {s t : ℝ} (m : ℤ) (θ : ℝ) (hs : 0 < s) :
    0 < (poissonAngularLam s t m θ).re := by
  simpa [poissonAngularLam_re] using hs

lemma real_cos_eq_exp_unit (θ : ℝ) :
    (((Real.cos (2 * Real.pi * θ) : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) +
        (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)))⁻¹) / 2 := by
  rw [Complex.ofReal_cos]
  have h : 2 * Complex.cos (((2 * Real.pi * θ : ℝ) : ℂ)) =
      Complex.exp ((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I) +
        Complex.exp (-((((2 * Real.pi * θ : ℝ) : ℂ)) * Complex.I)) := by
    simpa [neg_mul] using Complex.two_cos (((2 * Real.pi * θ : ℝ) : ℂ))
  rw [show Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) =
      Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) by ring_nf]
  rw [show (Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I))⁻¹ =
      Complex.exp (-(((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)) by
    rw [Complex.exp_neg]]
  rw [← h]
  ring

lemma poissonAngularLam_eq_denomCircle (s t : ℝ) (m : ℤ) (θ : ℝ) :
    poissonAngularLam s t m θ =
      poissonAngularDenomCircle s t m
        (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ))) := by
  unfold poissonAngularLam poissonAngularDenomCircle
  rw [show ((2 * Real.pi * t * Real.cos (2 * Real.pi * θ) : ℝ) : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) *
        ((Real.cos (2 * Real.pi * θ) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [real_cos_eq_exp_unit θ]
  ring

lemma integral_unitInterval_exp_eq_circleAverage (F : ℂ → ℂ) :
    (∫ θ, F (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)))
      ∂CircleBessel.unitIntervalMeasure) =
    Real.circleAverage F 0 1 := by
  rw [CircleBessel.integral_unitIntervalMeasure_eq_intervalIntegral_complex]
  rw [Real.circleAverage]
  let G : ℝ → ℂ := fun φ => F (Complex.exp (Complex.I * (φ : ℂ)))
  have hchange : (∫ θ in (0 : ℝ)..1,
      F (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)))) =
      (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..2 * Real.pi, G φ := by
    simpa [G, mul_comm, mul_assoc] using
      (intervalIntegral.integral_comp_mul_left (f := G) (a := (0 : ℝ)) (b := (1 : ℝ))
        (c := 2 * Real.pi) (by positivity : (2 * Real.pi : ℝ) ≠ 0))
  rw [hchange]
  congr 1
  apply intervalIntegral.integral_congr
  intro φ hφ
  simp [G, circleMap]
  ring_nf

lemma integral_poissonAngularLam_sq_eq_circleAverage (s t : ℝ) (m : ℤ) :
    (∫ θ, 1 / (poissonAngularLam s t m θ) ^ 2
      ∂CircleBessel.unitIntervalMeasure) =
    Real.circleAverage
      (fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2) 0 1 := by
  rw [← integral_unitInterval_exp_eq_circleAverage
    (F := fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2)]
  apply integral_congr_ae
  exact MeasureTheory.ae_of_all _ (fun θ => by
    change 1 / (poissonAngularLam s t m θ) ^ 2 =
      1 / (poissonAngularDenomCircle s t m
        (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)))) ^ 2
    rw [poissonAngularLam_eq_denomCircle])

lemma integral_poissonAngularLam_cube_eq_circleAverage (s t : ℝ) (m : ℤ) :
    (∫ θ, 2 / (poissonAngularLam s t m θ) ^ 3
      ∂CircleBessel.unitIntervalMeasure) =
    Real.circleAverage
      (fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3) 0 1 := by
  rw [← integral_unitInterval_exp_eq_circleAverage
    (F := fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3)]
  apply integral_congr_ae
  exact MeasureTheory.ae_of_all _ (fun θ => by
    change 2 / (poissonAngularLam s t m θ) ^ 3 =
      2 / (poissonAngularDenomCircle s t m
        (Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)))) ^ 3
    rw [poissonAngularLam_eq_denomCircle])

lemma poissonAngularDenomCircle_t_zero (s : ℝ) (m : ℤ) (z : ℂ) :
    poissonAngularDenomCircle s 0 m z = lam s m := by
  unfold poissonAngularDenomCircle
  norm_num

lemma norm_exp_neg_lam (s : ℝ) (m : ℤ) (x : ℝ) :
    ‖Complex.exp (-(lam s m) * (x : ℂ))‖ = Real.exp (-(s * x)) := by
  rw [Complex.norm_exp]
  congr 1
  unfold lam
  simp [Complex.add_re, Complex.mul_re]

lemma norm_exp_angular (t x θ : ℝ) :
    ‖Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ)))‖ = 1 := by
  rw [Complex.norm_exp]
  let r : ℝ := 2 * Real.pi * t * x
  let c : ℝ := Real.cos (2 * Real.pi * θ)
  have hre : (Complex.I * (r : ℂ) * (c : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  change Real.exp ((Complex.I * (r : ℂ) * (c : ℂ)).re) = 1
  rw [hre, Real.exp_zero]

lemma poissonMomentOneCircleIntegrand_eq_exp (s t : ℝ) (m : ℤ) (x θ : ℝ) :
    (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))) =
      (x : ℂ) * Complex.exp (-(poissonAngularLam s t m θ) * (x : ℂ)) := by
  calc
    (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))
        = (x : ℂ) * (Complex.exp (-(lam s m) * (x : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
            Complex.ofReal (Real.cos (2 * Real.pi * θ)))) := by
      ring_nf
    _ = (x : ℂ) * Complex.exp (-(lam s m) * (x : ℂ) +
          Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
            Complex.ofReal (Real.cos (2 * Real.pi * θ))) := by
      rw [Complex.exp_add]
    _ = (x : ℂ) * Complex.exp (-(poissonAngularLam s t m θ) * (x : ℂ)) := by
      congr 1
      unfold poissonAngularLam
      push_cast
      ring_nf

lemma poissonMomentTwoCircleIntegrand_eq_exp (s t : ℝ) (m : ℤ) (x θ : ℝ) :
    (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))) =
      (x : ℂ) ^ 2 * Complex.exp (-(poissonAngularLam s t m θ) * (x : ℂ)) := by
  calc
    (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))
        = (x : ℂ) ^ 2 * (Complex.exp (-(lam s m) * (x : ℂ)) *
          Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
            Complex.ofReal (Real.cos (2 * Real.pi * θ)))) := by
      ring_nf
    _ = (x : ℂ) ^ 2 * Complex.exp (-(lam s m) * (x : ℂ) +
          Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
            Complex.ofReal (Real.cos (2 * Real.pi * θ))) := by
      rw [Complex.exp_add]
    _ = (x : ℂ) ^ 2 * Complex.exp (-(poissonAngularLam s t m θ) * (x : ℂ)) := by
      congr 1
      unfold poissonAngularLam
      push_cast
      ring_nf

lemma integral_Ioi_poissonMomentOneCircleIntegrand
    (s t : ℝ) (m : ℤ) (θ : ℝ) (hs : 0 < s) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))) =
      1 / (poissonAngularLam s t m θ) ^ 2 := by
  have hpos : 0 < (poissonAngularLam s t m θ).re :=
    poissonAngularLam_re_pos m θ hs
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
    exact poissonMomentOneCircleIntegrand_eq_exp s t m x θ)]
  exact integral_Ioi_cexp_neg_mul_moment_one hpos

lemma integral_Ioi_poissonMomentTwoCircleIntegrand
    (s t : ℝ) (m : ℤ) (θ : ℝ) (hs : 0 < s) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))) =
      2 / (poissonAngularLam s t m θ) ^ 3 := by
  have hpos : 0 < (poissonAngularLam s t m θ).re :=
    poissonAngularLam_re_pos m θ hs
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
    exact poissonMomentTwoCircleIntegrand_eq_exp s t m x θ)]
  exact integral_Ioi_cexp_neg_mul_moment_two hpos

lemma integrableOn_poissonMomentOneCircleProduct {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      (Complex.exp (-(lam s m) * (p.1 : ℂ)) * (p.1 : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * p.1 : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * p.2))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
      (MeasureTheory.volume.prod CircleBessel.unitIntervalMeasure) := by
  haveI : IsFiniteMeasure CircleBessel.unitIntervalMeasure := ⟨by
    simp [CircleBessel.unitIntervalMeasure_univ]⟩
  have hbaseX : Integrable (fun x : ℝ => x * Real.exp (-(s * x)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) hs
    simpa [IntegrableOn, Real.rpow_one] using h
  have hbaseY : Integrable (fun _θ : ℝ => (1 : ℝ))
      (CircleBessel.unitIntervalMeasure.restrict Set.univ) := by
    simp
  have hbaseProd : Integrable (fun p : ℝ × ℝ =>
      p.1 * Real.exp (-(s * p.1)) * (1 : ℝ))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (CircleBessel.unitIntervalMeasure.restrict Set.univ)) := by
    simpa using hbaseX.mul_prod hbaseY
  have hbaseOn : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * Real.exp (-(s * p.1)) * (1 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
      (MeasureTheory.volume.prod CircleBessel.unitIntervalMeasure) := by
    rw [IntegrableOn, ← MeasureTheory.Measure.prod_restrict]
    exact hbaseProd
  refine hbaseOn.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
    have hxpos : 0 < p.1 := hp.1
    rw [norm_mul, norm_mul, norm_exp_neg_lam, norm_exp_angular]
    simp [Real.norm_eq_abs, abs_of_pos hxpos, mul_comm]

lemma integrableOn_poissonMomentTwoCircleProduct {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      (Complex.exp (-(lam s m) * (p.1 : ℂ)) * ((p.1 : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * p.1 : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * p.2))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
      (MeasureTheory.volume.prod CircleBessel.unitIntervalMeasure) := by
  haveI : IsFiniteMeasure CircleBessel.unitIntervalMeasure := ⟨by
    simp [CircleBessel.unitIntervalMeasure_univ]⟩
  have hbaseX : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(s * x)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (2 : ℝ))
      (by norm_num : (-1 : ℝ) < 2) (by norm_num : (1 : ℝ) ≤ 1) hs
    simpa [IntegrableOn, Real.rpow_natCast] using h
  have hbaseY : Integrable (fun _θ : ℝ => (1 : ℝ))
      (CircleBessel.unitIntervalMeasure.restrict Set.univ) := by
    simp
  have hbaseProd : Integrable (fun p : ℝ × ℝ =>
      p.1 ^ 2 * Real.exp (-(s * p.1)) * (1 : ℝ))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (CircleBessel.unitIntervalMeasure.restrict Set.univ)) := by
    simpa using hbaseX.mul_prod hbaseY
  have hbaseOn : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 ^ 2 * Real.exp (-(s * p.1)) * (1 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)
      (MeasureTheory.volume.prod CircleBessel.unitIntervalMeasure) := by
    rw [IntegrableOn, ← MeasureTheory.Measure.prod_restrict]
    exact hbaseProd
  refine hbaseOn.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
    rw [norm_mul, norm_mul, norm_exp_neg_lam, norm_exp_angular]
    simp [Real.norm_eq_abs]
    rw [mul_comm]

lemma integral_Ioi_integral_poissonMomentOneCircle_swap {s t : ℝ}
    (hs : 0 < s) (m : ℤ) :
    (∫ x in Set.Ioi (0 : ℝ), (∫ θ,
      (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))
      ∂CircleBessel.unitIntervalMeasure)) =
    (∫ θ, (∫ x in Set.Ioi (0 : ℝ),
      (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))))
      ∂CircleBessel.unitIntervalMeasure) := by
  haveI : IsFiniteMeasure CircleBessel.unitIntervalMeasure := ⟨by
    simp [CircleBessel.unitIntervalMeasure_univ]⟩
  let F : ℝ → ℝ → ℂ := fun x θ =>
    (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
      Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ)))
  have hOn := integrableOn_poissonMomentOneCircleProduct (s := s) (t := t) hs m
  have hInt : Integrable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        CircleBessel.unitIntervalMeasure) := by
    rw [IntegrableOn, ← MeasureTheory.Measure.prod_restrict] at hOn
    simpa [F] using hOn
  change (∫ x in Set.Ioi (0 : ℝ), (∫ θ, F x θ ∂CircleBessel.unitIntervalMeasure)) =
    (∫ θ, (∫ x in Set.Ioi (0 : ℝ), F x θ) ∂CircleBessel.unitIntervalMeasure)
  exact integral_integral_swap (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := CircleBessel.unitIntervalMeasure) (f := F) hInt

lemma integral_Ioi_integral_poissonMomentTwoCircle_swap {s t : ℝ}
    (hs : 0 < s) (m : ℤ) :
    (∫ x in Set.Ioi (0 : ℝ), (∫ θ,
      (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ)))
      ∂CircleBessel.unitIntervalMeasure)) =
    (∫ θ, (∫ x in Set.Ioi (0 : ℝ),
      (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
        Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))))
      ∂CircleBessel.unitIntervalMeasure) := by
  haveI : IsFiniteMeasure CircleBessel.unitIntervalMeasure := ⟨by
    simp [CircleBessel.unitIntervalMeasure_univ]⟩
  let F : ℝ → ℝ → ℂ := fun x θ =>
    (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
      Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ)))
  have hOn := integrableOn_poissonMomentTwoCircleProduct (s := s) (t := t) hs m
  have hInt : Integrable (Function.uncurry F)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        CircleBessel.unitIntervalMeasure) := by
    rw [IntegrableOn, ← MeasureTheory.Measure.prod_restrict] at hOn
    simpa [F] using hOn
  change (∫ x in Set.Ioi (0 : ℝ), (∫ θ, F x θ ∂CircleBessel.unitIntervalMeasure)) =
    (∫ θ, (∫ x in Set.Ioi (0 : ℝ), F x θ) ∂CircleBessel.unitIntervalMeasure)
  exact integral_integral_swap (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := CircleBessel.unitIntervalMeasure) (f := F) hInt

lemma integrableOn_poissonKernelMomentOneIntegrand {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    MeasureTheory.IntegrableOn (poissonKernelMomentOneIntegrand s t m)
      (Set.Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun x : ℝ => x * Real.exp (-(s * x))) (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (by norm_num : (-1 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1) hs
    simpa [Real.rpow_one] using h
  refine hbase.mono' ?_ ?_
  · have harg : Continuous fun x : ℝ => 2 * Real.pi * t * x := by fun_prop
    have hJ : Continuous fun x : ℝ => CircleBessel.J0 (2 * Real.pi * t * x) :=
      CircleBessel.continuous_J0.comp harg
    have hreal : Continuous fun x : ℝ => x * CircleBessel.J0 (2 * Real.pi * t * x) := by
      exact continuous_id.mul hJ
    have hexp : Continuous fun x : ℝ => Complex.exp (-(lam s m) * (x : ℂ)) := by
      fun_prop
    exact (hexp.mul (Complex.continuous_ofReal.comp hreal)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have hnorm_exp : ‖Complex.exp (-(lam s m) * (x : ℂ))‖ = Real.exp (-(s * x)) := by
      rw [Complex.norm_exp]
      congr 1
      unfold lam
      simp [Complex.add_re, Complex.mul_re]
    have hJ := CircleBessel.abs_J0_le_one (2 * Real.pi * t * x)
    rw [poissonKernelMomentOneIntegrand, norm_mul, hnorm_exp]
    simp [Real.norm_eq_abs]
    rw [abs_of_pos hxpos]
    calc
      Real.exp (-(s * x)) * (x * |CircleBessel.J0 (2 * Real.pi * t * x)|) ≤
          Real.exp (-(s * x)) * (x * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hJ hxpos.le) (Real.exp_nonneg _)
      _ = x * Real.exp (-(s * x)) := by ring

lemma integrableOn_poissonKernelMomentTwoIntegrand {s t : ℝ} (hs : 0 < s) (m : ℤ) :
    MeasureTheory.IntegrableOn (poissonKernelMomentTwoIntegrand s t m)
      (Set.Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(s * x)))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (2 : ℝ))
      (by norm_num : (-1 : ℝ) < 2) (by norm_num : (1 : ℝ) ≤ 1) hs
    simpa [Real.rpow_natCast] using h
  refine hbase.mono' ?_ ?_
  · have harg : Continuous fun x : ℝ => 2 * Real.pi * t * x := by fun_prop
    have hJ : Continuous fun x : ℝ => CircleBessel.J0 (2 * Real.pi * t * x) :=
      CircleBessel.continuous_J0.comp harg
    have hreal : Continuous fun x : ℝ => x ^ 2 * CircleBessel.J0 (2 * Real.pi * t * x) := by
      exact (continuous_id.pow 2).mul hJ
    have hexp : Continuous fun x : ℝ => Complex.exp (-(lam s m) * (x : ℂ)) := by
      fun_prop
    exact (hexp.mul (Complex.continuous_ofReal.comp hreal)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnorm_exp : ‖Complex.exp (-(lam s m) * (x : ℂ))‖ = Real.exp (-(s * x)) := by
      rw [Complex.norm_exp]
      congr 1
      unfold lam
      simp [Complex.add_re, Complex.mul_re]
    have hJ := CircleBessel.abs_J0_le_one (2 * Real.pi * t * x)
    rw [poissonKernelMomentTwoIntegrand, norm_mul, hnorm_exp]
    simp [Real.norm_eq_abs]
    calc
      Real.exp (-(s * x)) * (x ^ 2 * |CircleBessel.J0 (2 * Real.pi * t * x)|) ≤
          Real.exp (-(s * x)) * (x ^ 2 * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hJ (sq_nonneg x)) (Real.exp_nonneg _)
      _ = x ^ 2 * Real.exp (-(s * x)) := by ring

/--
Moment form of the remaining Laplace-Bessel transform calculation.  This is the
shape obtained by differentiating the base transform
`∫₀∞ exp (-λ x) J₀(a x) dx = (λ ^ 2 + a ^ 2) ^ (-1 / 2)` once and twice.
-/
def PoissonKernelMomentFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      (∫ x in Set.Ioi (0 : ℝ), poissonKernelMomentOneIntegrand s t m x) =
        (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) ∧
      (∫ x in Set.Ioi (0 : ℝ), poissonKernelMomentTwoIntegrand s t m x) =
        -cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ))

/--
Angular form of the remaining transform calculation after Fubini and the
elementary half-line exponential moments.  What remains is the classical
rational trigonometric integral in the parameter `λ - iβ cos θ`.
-/
def PoissonKernelAngularFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      (∫ θ, 1 / (poissonAngularLam s t m θ) ^ 2
          ∂CircleBessel.unitIntervalMeasure) =
        (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) ∧
      (∫ θ, 2 / (poissonAngularLam s t m θ) ^ 3
          ∂CircleBessel.unitIntervalMeasure) =
        -cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ))

/--
Circle-average version of `PoissonKernelAngularFormula`.  This is the form
best suited to a contour-integral/residue calculation on the unit circle.
-/
def PoissonKernelCircleAverageFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      Real.circleAverage
        (fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2) 0 1 =
        (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) ∧
      Real.circleAverage
        (fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3) 0 1 =
        -cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ))

/--
Positive-radius circle-average target.  The separate `t = 0` case is proved
below, so this is the only case left for the residue calculation.
-/
def PoissonKernelCircleAverageFormulaPos : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 < t →
    ∀ m : ℤ,
      Real.circleAverage
        (fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2) 0 1 =
        (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) ∧
      Real.circleAverage
        (fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3) 0 1 =
        -cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ))

/--
Contour-integral form of the remaining angular identities.  The integrand is
the direct unit-circle rational function obtained from
`z = exp (i 2πθ)`.
-/
def PoissonKernelContourFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), (1 : ℝ)),
          (z - 0)⁻¹ • (1 / (poissonAngularDenomCircle s t m z) ^ 2))) =
        (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) ∧
      ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), (1 : ℝ)),
          (z - 0)⁻¹ • (2 / (poissonAngularDenomCircle s t m z) ^ 3))) =
        -cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ))

theorem PoissonKernelCircleAverageFormula_of_contourFormula
    (hcontour : PoissonKernelContourFormula) : PoissonKernelCircleAverageFormula := by
  intro s t hs ht m
  rcases hcontour s t hs ht m with ⟨h1, h2⟩
  constructor
  · rw [Real.circleAverage_eq_circleIntegral (R := (1 : ℝ)) (c := (0 : ℂ))
      (f := fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2) (by norm_num)]
    exact h1
  · rw [Real.circleAverage_eq_circleIntegral (R := (1 : ℝ)) (c := (0 : ℂ))
      (f := fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3) (by norm_num)]
    exact h2

lemma PoissonKernelCircleAverageFormula_t_zero {s : ℝ} (hs : 0 < s) (m : ℤ) :
    Real.circleAverage (fun z => 1 / (poissonAngularDenomCircle s 0 m z) ^ 2) 0 1 =
        (lam s m) * cpowR (q s 0 m) (-(3 / 2 : ℝ)) ∧
      Real.circleAverage (fun z => 2 / (poissonAngularDenomCircle s 0 m z) ^ 3) 0 1 =
        -cpowR (q s 0 m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s 0 m) (-(5 / 2 : ℝ)) := by
  constructor
  · rw [show (fun z => 1 / (poissonAngularDenomCircle s 0 m z) ^ 2) =
        fun _z : ℂ => 1 / (lam s m) ^ 2 by
      funext z
      rw [poissonAngularDenomCircle_t_zero]]
    rw [Real.circleAverage_const]
    rw [angular_rhs_first_t_zero hs]
  · rw [show (fun z => 2 / (poissonAngularDenomCircle s 0 m z) ^ 3) =
        fun _z : ℂ => 2 / (lam s m) ^ 3 by
      funext z
      rw [poissonAngularDenomCircle_t_zero]]
    rw [Real.circleAverage_const]
    rw [angular_rhs_second_t_zero hs]

theorem PoissonKernelCircleAverageFormulaPos_residue :
    PoissonKernelCircleAverageFormulaPos := by
  intro s t hs ht m
  have hC : poissonDenomFactor t ≠ 0 := poissonDenomFactor_ne_zero ht
  have hr : poissonRootIn s t m ∈ Metric.ball (0 : ℂ) (1 : ℝ) :=
    poissonRootIn_mem_ball hs ht m
  have hR : 1 < ‖poissonRootOut s t m‖ :=
    one_lt_norm_poissonRootOut hs ht m
  have hfirst_integral :
      (∮ z in C((0 : ℂ), (1 : ℝ)),
          (z - 0)⁻¹ • (1 / (poissonAngularDenomCircle s t m z) ^ 2)) =
        (∮ z in C((0 : ℂ), (1 : ℝ)),
          z / (poissonDenomFactor t) ^ 2 /
            ((z - poissonRootIn s t m) ^ 2 *
              (z - poissonRootOut s t m) ^ 2)) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hz_norm : ‖z‖ = 1 := by
      simpa [mem_sphere_zero_iff_norm] using hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      norm_num at hz_norm
    exact poissonAngularDenomCircle_factor_sq_integrand (s := s) (t := t) ht m hz0
  have hsecond_integral :
      (∮ z in C((0 : ℂ), (1 : ℝ)),
          (z - 0)⁻¹ • (2 / (poissonAngularDenomCircle s t m z) ^ 3)) =
        (∮ z in C((0 : ℂ), (1 : ℝ)),
          2 * z ^ 2 / (poissonDenomFactor t) ^ 3 /
            ((z - poissonRootIn s t m) ^ 3 *
              (z - poissonRootOut s t m) ^ 3)) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hz_norm : ‖z‖ = 1 := by
      simpa [mem_sphere_zero_iff_norm] using hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      norm_num at hz_norm
    exact poissonAngularDenomCircle_factor_cube_integrand (s := s) (t := t) ht m hz0
  constructor
  · calc
      Real.circleAverage
          (fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2) 0 1 =
        ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
          (∮ z in C((0 : ℂ), (1 : ℝ)),
            (z - 0)⁻¹ • (1 / (poissonAngularDenomCircle s t m z) ^ 2))) := by
          rw [Real.circleAverage_eq_circleIntegral (R := (1 : ℝ)) (c := (0 : ℂ))
            (f := fun z => 1 / (poissonAngularDenomCircle s t m z) ^ 2) (by norm_num)]
      _ = ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
          (∮ z in C((0 : ℂ), (1 : ℝ)),
            z / (poissonDenomFactor t) ^ 2 /
              ((z - poissonRootIn s t m) ^ 2 *
                (z - poissonRootOut s t m) ^ 2))) := by
          rw [hfirst_integral]
      _ = -(poissonRootIn s t m + poissonRootOut s t m) /
            (poissonDenomFactor t ^ 2 *
              (poissonRootIn s t m - poissonRootOut s t m) ^ 3) := by
          exact normalized_circleIntegral_double_pole
            (r := poissonRootIn s t m) (R := poissonRootOut s t m)
            (C := poissonDenomFactor t) hr hR hC
      _ = (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) := by
          rw [double_pole_coefficient_eq (s := s) (t := t) hs ht m]
          rw [cpowR_q_neg_three_halves_eq_qsqrt_zpow]
  · calc
      Real.circleAverage
          (fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3) 0 1 =
        ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
          (∮ z in C((0 : ℂ), (1 : ℝ)),
            (z - 0)⁻¹ • (2 / (poissonAngularDenomCircle s t m z) ^ 3))) := by
          rw [Real.circleAverage_eq_circleIntegral (R := (1 : ℝ)) (c := (0 : ℂ))
            (f := fun z => 2 / (poissonAngularDenomCircle s t m z) ^ 3) (by norm_num)]
      _ = ((2 * Complex.ofReal Real.pi * Complex.I)⁻¹ •
          (∮ z in C((0 : ℂ), (1 : ℝ)),
            2 * z ^ 2 / (poissonDenomFactor t) ^ 3 /
              ((z - poissonRootIn s t m) ^ 3 *
                (z - poissonRootOut s t m) ^ 3))) := by
          rw [hsecond_integral]
      _ = (1 / poissonDenomFactor t ^ 3) *
            (2 / (poissonRootIn s t m - poissonRootOut s t m) ^ 3 -
              12 * poissonRootIn s t m /
                (poissonRootIn s t m - poissonRootOut s t m) ^ 4 +
              12 * (poissonRootIn s t m) ^ 2 /
                (poissonRootIn s t m - poissonRootOut s t m) ^ 5) := by
          exact normalized_circleIntegral_triple_pole
            (r := poissonRootIn s t m) (R := poissonRootOut s t m)
            (C := poissonDenomFactor t) hr hR hC
      _ = -cpowR (q s t m) (-(3 / 2 : ℝ)) +
            3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)) := by
          rw [triple_pole_coefficient_eq (s := s) (t := t) hs ht m]
          rw [cpowR_q_neg_three_halves_eq_qsqrt_zpow,
            cpowR_q_neg_five_halves_eq_qsqrt_zpow]

theorem PoissonKernelCircleAverageFormula_of_pos
    (hpos : PoissonKernelCircleAverageFormulaPos) : PoissonKernelCircleAverageFormula := by
  intro s t hs ht m
  rcases ht.eq_or_lt with rfl | htpos
  · exact PoissonKernelCircleAverageFormula_t_zero hs m
  · exact hpos s t hs htpos m

theorem PoissonKernelAngularFormula_of_circleAverageFormula
    (hcircle : PoissonKernelCircleAverageFormula) : PoissonKernelAngularFormula := by
  intro s t hs ht m
  rcases hcircle s t hs ht m with ⟨h1, h2⟩
  constructor
  · rw [integral_poissonAngularLam_sq_eq_circleAverage]
    exact h1
  · rw [integral_poissonAngularLam_cube_eq_circleAverage]
    exact h2

theorem PoissonKernelMomentFormula_of_angularFormula
    (hangular : PoissonKernelAngularFormula) : PoissonKernelMomentFormula := by
  intro s t hs ht m
  rcases hangular s t hs ht m with ⟨h1ang, h2ang⟩
  constructor
  · calc
      (∫ x in Set.Ioi (0 : ℝ), poissonKernelMomentOneIntegrand s t m x)
          = ∫ x in Set.Ioi (0 : ℝ), (∫ θ,
              (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
                Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
                  Complex.ofReal (Real.cos (2 * Real.pi * θ)))
              ∂CircleBessel.unitIntervalMeasure) := by
            exact setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
              poissonKernelMomentOneIntegrand_eq_circleIntegral s t m x)
      _ = ∫ θ, (∫ x in Set.Ioi (0 : ℝ),
              (Complex.exp (-(lam s m) * (x : ℂ)) * (x : ℂ)) *
                Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
                  Complex.ofReal (Real.cos (2 * Real.pi * θ))))
              ∂CircleBessel.unitIntervalMeasure := by
            exact integral_Ioi_integral_poissonMomentOneCircle_swap
              (s := s) (t := t) hs m
      _ = ∫ θ, 1 / (poissonAngularLam s t m θ) ^ 2
              ∂CircleBessel.unitIntervalMeasure := by
            apply integral_congr_ae
            exact MeasureTheory.ae_of_all _ (fun θ => by
              exact integral_Ioi_poissonMomentOneCircleIntegrand s t m θ hs)
      _ = (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) := h1ang
  · calc
      (∫ x in Set.Ioi (0 : ℝ), poissonKernelMomentTwoIntegrand s t m x)
          = ∫ x in Set.Ioi (0 : ℝ), (∫ θ,
              (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
                Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
                  Complex.ofReal (Real.cos (2 * Real.pi * θ)))
              ∂CircleBessel.unitIntervalMeasure) := by
            exact setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
              poissonKernelMomentTwoIntegrand_eq_circleIntegral s t m x)
      _ = ∫ θ, (∫ x in Set.Ioi (0 : ℝ),
              (Complex.exp (-(lam s m) * (x : ℂ)) * ((x : ℂ) ^ 2)) *
                Complex.exp (Complex.I * ((2 * Real.pi * t * x : ℝ) : ℂ) *
                  Complex.ofReal (Real.cos (2 * Real.pi * θ))))
              ∂CircleBessel.unitIntervalMeasure := by
            exact integral_Ioi_integral_poissonMomentTwoCircle_swap
              (s := s) (t := t) hs m
      _ = ∫ θ, 2 / (poissonAngularLam s t m θ) ^ 3
              ∂CircleBessel.unitIntervalMeasure := by
            apply integral_congr_ae
            exact MeasureTheory.ae_of_all _ (fun θ => by
              exact integral_Ioi_poissonMomentTwoCircleIntegrand s t m θ hs)
      _ = -cpowR (q s t m) (-(3 / 2 : ℝ)) +
          3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)) := h2ang

/--
Complex-valued version of the remaining weighted Laplace-Bessel transform.
This is the natural target obtained from
`∫₀∞ exp (-λ x) J₀(a x) dx = (λ ^ 2 + a ^ 2) ^ (-1 / 2)`
by differentiating with respect to `λ`.
-/
def PoissonKernelHalfLineComplexFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    ∀ m : ℤ,
      (∫ x in Set.Ioi (0 : ℝ), poissonKernelHalfLineIntegrand s t m x) =
        (1 / 2 : ℂ) * (lam s m) * cpowR (q s t m) (-(3 / 2 : ℝ)) +
          (s : ℂ) *
            (-cpowR (q s t m) (-(3 / 2 : ℝ)) +
              3 * (lam s m) ^ 2 * cpowR (q s t m) (-(5 / 2 : ℝ)))

theorem PoissonKernelHalfLineComplexFormula_of_momentFormula
    (hformula : PoissonKernelMomentFormula) : PoissonKernelHalfLineComplexFormula := by
  intro s t hs ht m
  rcases hformula s t hs ht m with ⟨h1, h2⟩
  have h1int := integrableOn_poissonKernelMomentOneIntegrand (s := s) (t := t) hs m
  have h2int := integrableOn_poissonKernelMomentTwoIntegrand (s := s) (t := t) hs m
  let F1 : ℝ → ℂ := poissonKernelMomentOneIntegrand s t m
  let F2 : ℝ → ℂ := poissonKernelMomentTwoIntegrand s t m
  have hdecomp :
      (∫ x in Set.Ioi (0 : ℝ), poissonKernelHalfLineIntegrand s t m x) =
        ∫ x in Set.Ioi (0 : ℝ), (1 / 2 : ℂ) * F1 x + (s : ℂ) * F2 x := by
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _hx => by
      dsimp [F1, F2, poissonKernelMomentOneIntegrand, poissonKernelMomentTwoIntegrand,
        poissonKernelHalfLineIntegrand]
      push_cast
      ring_nf)
  rw [hdecomp]
  rw [MeasureTheory.integral_add]
  · rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_const_mul]
    dsimp [F1, F2]
    rw [h1, h2]
    ring
  · exact h1int.const_mul (1 / 2 : ℂ)
  · exact h2int.const_mul (s : ℂ)

theorem PoissonKernelHalfLineFormula_of_complexFormula
    (hformula : PoissonKernelHalfLineComplexFormula) : PoissonKernelHalfLineFormula := by
  intro s t hs ht m
  rw [hformula s t hs ht m]
  rw [Tterm_eq_TtermC_re]
  unfold TtermC
  simp [Complex.add_re, Complex.mul_re]
  ring

theorem PoissonKernelFourierFormula_of_halfLineFormula
    (hformula : PoissonKernelHalfLineFormula) : PoissonKernelFourierFormula := by
  intro s t hs ht m
  rw [fourier_poissonKernelSampleC_re_eq_two_re_halfLine (s := s) (t := t) hs m]
  exact hformula s t hs ht m

theorem PoissonKernelFourierFormula_of_momentFormula
    (hformula : PoissonKernelMomentFormula) : PoissonKernelFourierFormula :=
  PoissonKernelFourierFormula_of_halfLineFormula
    (PoissonKernelHalfLineFormula_of_complexFormula
      (PoissonKernelHalfLineComplexFormula_of_momentFormula hformula))

theorem PoissonKernelFourierFormula_of_angularFormula
    (hformula : PoissonKernelAngularFormula) : PoissonKernelFourierFormula :=
  PoissonKernelFourierFormula_of_momentFormula
    (PoissonKernelMomentFormula_of_angularFormula hformula)

theorem PoissonKernelFourierFormula_of_circleAverageFormula
    (hformula : PoissonKernelCircleAverageFormula) : PoissonKernelFourierFormula :=
  PoissonKernelFourierFormula_of_angularFormula
    (PoissonKernelAngularFormula_of_circleAverageFormula hformula)

theorem PoissonKernelFourierFormula_of_circleAverageFormulaPos
    (hformula : PoissonKernelCircleAverageFormulaPos) : PoissonKernelFourierFormula :=
  PoissonKernelFourierFormula_of_circleAverageFormula
    (PoissonKernelCircleAverageFormula_of_pos hformula)

theorem PoissonKernelFourierFormula_of_contourFormula
    (hformula : PoissonKernelContourFormula) : PoissonKernelFourierFormula :=
  PoissonKernelFourierFormula_of_circleAverageFormula
    (PoissonKernelCircleAverageFormula_of_contourFormula hformula)

/--
Once the explicit Fourier transform evaluation is available, the project-level
Poisson representation follows formally from mathlib's Poisson summation theorem.
-/
theorem K_besselPoissonFormula_of_fourierFormula
    (hformula : PoissonKernelFourierFormula) : K_besselPoissonFormula := by
  intro s t hs ht
  let hTsumC : Summable (fun m : ℤ => TtermC s t m) := summable_TtermC_int hs t
  let hTsumR : Summable (fun m : ℤ => Tterm s t m) :=
    summable_Tterm_of_summable_TtermC hTsumC
  let hFourier : ∀ m : ℤ,
      FourierTransform.fourier (poissonKernelSampleC s t) (m : ℝ) = (Tterm s t m : ℂ) := by
    intro m
    rw [fourier_poissonKernelSampleC_eq_ofReal_re (s := s) (t := t) hs (m : ℝ)]
    exact congrArg Complex.ofReal (hformula s t hs ht m)
  refine ⟨hTsumR, ?_⟩
  have hFsum :
      Summable fun n : ℤ => FourierTransform.fourier (poissonKernelSampleC s t) (n : ℝ) :=
    (Complex.ofRealCLM.summable hTsumR).congr (fun n => (hFourier n).symm)
  have hc := continuous_poissonKernelSampleC s t
  have hdecay := poissonKernelSampleC_decay_cocompact (s := s) (t := t) hs
  have hpoiss := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (f := poissonKernelSampleC s t) hc (by norm_num : (1 : ℝ) < 2) hdecay hFsum 0
  have hpoiss' : (∑' n : ℤ, poissonKernelSampleC s t (n : ℝ)) =
      ∑' m : ℤ, (Tterm s t m : ℂ) := by
    simp_rw [hFourier] at hpoiss
    simpa using hpoiss
  have hKc : (K_bessel s t : ℂ) =
      ∑' n : ℤ, poissonKernelSampleC s t (n : ℝ) := by
    rw [K_bessel_eq_tsum_poissonKernelSampleR hs]
    simpa [poissonKernelSampleC] using
      (Complex.ofRealCLM.map_tsum (summable_poissonKernelSampleR_int hs t))
  have hKcT : (K_bessel s t : ℂ) = ∑' m : ℤ, (Tterm s t m : ℂ) := by
    rw [hKc, hpoiss']
  have hTsumC_ofReal :
      ((∑' m : ℤ, Tterm s t m : ℝ) : ℂ) =
        ∑' m : ℤ, (Tterm s t m : ℂ) := by
    simpa using (Complex.ofRealCLM.map_tsum hTsumR)
  exact_mod_cast hKcT.trans hTsumC_ofReal.symm

theorem K_besselPoissonFormula_of_momentFormula
    (hformula : PoissonKernelMomentFormula) : K_besselPoissonFormula :=
  K_besselPoissonFormula_of_fourierFormula
    (PoissonKernelFourierFormula_of_momentFormula hformula)

theorem K_besselPoissonFormula_of_angularFormula
    (hformula : PoissonKernelAngularFormula) : K_besselPoissonFormula :=
  K_besselPoissonFormula_of_fourierFormula
    (PoissonKernelFourierFormula_of_angularFormula hformula)

theorem K_besselPoissonFormula_of_circleAverageFormula
    (hformula : PoissonKernelCircleAverageFormula) : K_besselPoissonFormula :=
  K_besselPoissonFormula_of_fourierFormula
    (PoissonKernelFourierFormula_of_circleAverageFormula hformula)

theorem K_besselPoissonFormula_of_circleAverageFormulaPos
    (hformula : PoissonKernelCircleAverageFormulaPos) : K_besselPoissonFormula :=
  K_besselPoissonFormula_of_fourierFormula
    (PoissonKernelFourierFormula_of_circleAverageFormulaPos hformula)

theorem K_besselPoissonFormula_of_contourFormula
    (hformula : PoissonKernelContourFormula) : K_besselPoissonFormula :=
  K_besselPoissonFormula_of_fourierFormula
    (PoissonKernelFourierFormula_of_contourFormula hformula)

end Erdos953Formalization
