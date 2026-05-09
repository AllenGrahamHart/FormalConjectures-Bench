import FormalConjecturesBench.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Erdos953Formalization
namespace CircleBessel

/-- Lebesgue measure restricted to the unit interval, used for angular averages. -/
noncomputable def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

lemma unitIntervalMeasure_univ : unitIntervalMeasure Set.univ = 1 := by
  unfold unitIntervalMeasure
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Icc]

lemma unitIntervalMeasure_real_univ : unitIntervalMeasure.real Set.univ = 1 := by
  rw [measureReal_def, unitIntervalMeasure_univ]
  exact ENNReal.toReal_one

/--
Circle-average definition of the Bessel function `J₀`, before taking real part.
This is the exact special function needed for the Poisson-Bessel kernel.
-/
noncomputable def J0c (u : ℝ) : ℂ :=
  ∫ θ, Complex.exp
      (Complex.I * (u : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ))) ∂unitIntervalMeasure

/-- Real-valued `J₀`, defined as the real part of the circle average. -/
noncomputable def J0 (u : ℝ) : ℝ :=
  (J0c u).re

lemma J0c_eq_setIntegral (u : ℝ) :
    J0c u = ∫ θ in Set.Icc (0 : ℝ) 1,
      Complex.exp
        (Complex.I * (u : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))) := by
  rfl

lemma continuous_J0c : Continuous J0c := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      Complex.exp
        (Complex.I * (p.1 : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * p.2)))) := by
    fun_prop
  convert continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun u θ : ℝ =>
      Complex.exp
        (Complex.I * (u : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))))
    hcont (s := Set.Icc (0 : ℝ) 1) isCompact_Icc using 1

lemma continuous_J0 : Continuous J0 := by
  unfold J0
  exact Complex.continuous_re.comp continuous_J0c

/-- The usual angular parametrisation of the unit circle. -/
noncomputable def circlePoint (θ : ℝ) : Plane :=
  !₂[Real.cos (2 * Real.pi * θ), Real.sin (2 * Real.pi * θ)]

/-- The point `(t, 0)` on the horizontal axis. -/
noncomputable def xAxisPoint (t : ℝ) : Plane :=
  !₂[t, 0]

/-- The coordinate identification of the Euclidean plane with the complex plane. -/
noncomputable def planeToComplex (x : Plane) : ℂ :=
  ⟨x (0 : Fin 2), x (1 : Fin 2)⟩

lemma norm_circlePoint (θ : ℝ) : ‖circlePoint θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [circlePoint, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

lemma dist_circlePoint_zero (θ : ℝ) : dist (circlePoint θ) 0 = 1 := by
  simpa [dist_eq_norm] using norm_circlePoint θ

lemma norm_xAxisPoint (t : ℝ) : ‖xAxisPoint t‖ = |t| := by
  rw [EuclideanSpace.norm_eq]
  simp [xAxisPoint, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]

lemma dist_xAxisPoint_zero_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    dist (xAxisPoint t) 0 = t := by
  rw [dist_eq_norm, sub_zero, norm_xAxisPoint, abs_of_nonneg ht]

lemma norm_planeToComplex (x : Plane) : ‖planeToComplex x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def]
  congr 1
  simp [planeToComplex, Complex.normSq_apply, Fin.sum_univ_two, pow_two]

lemma planeToComplex_eq_zero_iff {x : Plane} : planeToComplex x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hre : x (0 : Fin 2) = 0 := by
      simpa [planeToComplex] using congrArg Complex.re hx
    have him : x (1 : Fin 2) = 0 := by
      simpa [planeToComplex] using congrArg Complex.im hx
    ext i
    fin_cases i <;> simp [hre, him]
  · intro hx
    apply Complex.ext <;> simp [hx, planeToComplex]

lemma inner_circlePoint_xAxisPoint (θ t : ℝ) :
    inner ℝ (circlePoint θ) (xAxisPoint t) = t * Real.cos (2 * Real.pi * θ) := by
  simp [circlePoint, xAxisPoint, Fin.sum_univ_two, inner]

lemma inner_circlePoint_eq_norm_mul_cos_sub_arg (θ : ℝ) (x : Plane) :
    inner ℝ (circlePoint θ) x =
      ‖x‖ * Real.cos (2 * Real.pi * θ - (planeToComplex x).arg) := by
  by_cases hx : planeToComplex x = 0
  · have hx0 : x = 0 := planeToComplex_eq_zero_iff.mp hx
    simp [hx0]
  · have hnorm_ne : ‖x‖ ≠ 0 := by
      rw [← norm_planeToComplex]
      exact norm_ne_zero_iff.mpr hx
    rw [Real.cos_sub, Complex.cos_arg hx, Complex.sin_arg, norm_planeToComplex]
    simp [circlePoint, planeToComplex, Fin.sum_univ_two, inner]
    field_simp [hnorm_ne]

lemma continuous_circlePoint : Continuous circlePoint := by
  unfold circlePoint
  change Continuous (fun θ : ℝ =>
    WithLp.toLp 2 (![Real.cos (2 * Real.pi * θ), Real.sin (2 * Real.pi * θ)] : Fin 2 → ℝ))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi (by
    intro i
    fin_cases i <;> simp <;> fun_prop))

/-- A single plane-wave frequency restricted to the unit circle. -/
noncomputable def circleFrequency (k : ℕ) (θ : ℝ) (x : Plane) : ℂ :=
  Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
        Complex.ofReal (inner ℝ (circlePoint θ) x))

lemma circleFrequency_eq_exp_ofReal_mul_I (k : ℕ) (θ : ℝ) (x : Plane) :
    circleFrequency k θ x =
      Complex.exp
        (Complex.ofReal (2 * Real.pi * (k : ℝ) * inner ℝ (circlePoint θ) x) *
          Complex.I) := by
  unfold circleFrequency
  congr 1
  push_cast
  ring

lemma norm_circleFrequency (k : ℕ) (θ : ℝ) (x : Plane) :
    ‖circleFrequency k θ x‖ = 1 := by
  rw [circleFrequency_eq_exp_ofReal_mul_I]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_circleFrequency (k : ℕ) (x : Plane) :
    Continuous (fun θ => circleFrequency k θ x) := by
  unfold circleFrequency
  exact Complex.continuous_exp.comp
    (((continuous_const.mul continuous_const).mul continuous_const).mul
      (Complex.continuous_ofReal.comp (continuous_circlePoint.inner continuous_const)))

lemma integrable_circleFrequency (k : ℕ) (x : Plane) :
    Integrable (fun θ => circleFrequency k θ x) unitIntervalMeasure := by
  haveI : IsFiniteMeasure unitIntervalMeasure := ⟨by simp [unitIntervalMeasure_univ]⟩
  refine (integrable_const (α := ℝ) (μ := unitIntervalMeasure) (1 : ℝ)).mono' ?_ ?_
  · exact (continuous_circleFrequency k x).aestronglyMeasurable
  · exact ae_of_all _ (fun θ => by simp [norm_circleFrequency])

lemma integrable_circleFrequency_re (k : ℕ) (x : Plane) :
    Integrable (fun θ => (circleFrequency k θ x).re) unitIntervalMeasure :=
  (integrable_circleFrequency k x).re

lemma star_exp_ofReal_mul_I (a : ℝ) :
    star (Complex.exp (Complex.ofReal a * Complex.I)) =
      Complex.exp (-(Complex.ofReal a * Complex.I)) := by
  apply Complex.ext
  · simp [Complex.exp_re]
  · simp [Complex.exp_im]

lemma star_circleFrequency (k : ℕ) (θ : ℝ) (x : Plane) :
    star (circleFrequency k θ x) = circleFrequency k θ (-x) := by
  rw [circleFrequency_eq_exp_ofReal_mul_I, circleFrequency_eq_exp_ofReal_mul_I]
  rw [star_exp_ofReal_mul_I]
  congr 1
  simp [inner_neg_right]

lemma circleFrequency_sub_eq_mul_star (k : ℕ) (θ : ℝ) (x y : Plane) :
    circleFrequency k θ (x - y) =
      circleFrequency k θ x * star (circleFrequency k θ y) := by
  rw [star_circleFrequency]
  rw [circleFrequency_eq_exp_ofReal_mul_I, circleFrequency_eq_exp_ofReal_mul_I,
    circleFrequency_eq_exp_ofReal_mul_I]
  rw [← Complex.exp_add]
  congr 1
  simp [inner_sub_right]
  ring

lemma circleFrequency_xAxisPoint (k : ℕ) (θ t : ℝ) :
    circleFrequency k θ (xAxisPoint t) =
      Complex.exp
        (Complex.I * (2 * Real.pi * (k : ℝ) * t : ℂ) *
          Complex.ofReal (Real.cos (2 * Real.pi * θ))) := by
  unfold circleFrequency
  rw [inner_circlePoint_xAxisPoint]
  congr 1
  push_cast
  ring

lemma shifted_angle_eq (θ φ : ℝ) :
    2 * Real.pi * (θ + (-φ / (2 * Real.pi))) = 2 * Real.pi * θ - φ := by
  field_simp [Real.pi_ne_zero]
  ring

lemma circleFrequency_eq_J0c_shifted_integrand (k : ℕ) (θ : ℝ) (x : Plane) :
    circleFrequency k θ x =
      Complex.exp
        (Complex.I * (2 * Real.pi * (k : ℝ) * ‖x‖ : ℂ) *
          Complex.ofReal
            (Real.cos (2 * Real.pi *
              (θ + (-(planeToComplex x).arg / (2 * Real.pi)))))) := by
  unfold circleFrequency
  rw [inner_circlePoint_eq_norm_mul_cos_sub_arg]
  rw [shifted_angle_eq]
  congr 1
  push_cast
  ring

/-- Average of a single Fourier frequency over the unit circle. -/
noncomputable def circleExpAverage (k : ℕ) (x : Plane) : ℂ :=
  ∫ θ, circleFrequency k θ x ∂unitIntervalMeasure

lemma integral_unitIntervalMeasure_eq_intervalIntegral_complex (f : ℝ → ℂ) :
    ∫ θ, f θ ∂unitIntervalMeasure = ∫ θ in (0 : ℝ)..1, f θ := by
  unfold unitIntervalMeasure
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

lemma integral_unitIntervalMeasure_shift_eq_of_periodic_complex
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) (η : ℝ) :
    (∫ θ, f (θ + η) ∂unitIntervalMeasure) = ∫ θ, f θ ∂unitIntervalMeasure := by
  rw [integral_unitIntervalMeasure_eq_intervalIntegral_complex,
    integral_unitIntervalMeasure_eq_intervalIntegral_complex]
  rw [intervalIntegral.integral_comp_add_right]
  have h := hf.intervalIntegral_add_eq (0 : ℝ) η
  simpa [zero_add, add_comm] using h.symm

lemma periodic_J0c_integrand (u : ℝ) :
    Function.Periodic
      (fun θ : ℝ => Complex.exp
        (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))) 1 := by
  intro θ
  change Complex.exp
        (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * (θ + 1)))) =
      Complex.exp
        (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))
  have harg : 2 * Real.pi * (θ + 1) = 2 * Real.pi * θ + 2 * Real.pi := by ring
  rw [harg, Real.cos_add_two_pi]

lemma circleExpAverage_xAxisPoint (k : ℕ) (t : ℝ) :
    circleExpAverage k (xAxisPoint t) = J0c (2 * Real.pi * (k : ℝ) * t) := by
  unfold circleExpAverage J0c
  congr 1
  ext θ
  simpa using circleFrequency_xAxisPoint k θ t

lemma circleExpAverage_eq_J0c_norm (k : ℕ) (x : Plane) :
    circleExpAverage k x = J0c (2 * Real.pi * (k : ℝ) * ‖x‖) := by
  unfold circleExpAverage J0c
  let u : ℝ := 2 * Real.pi * (k : ℝ) * ‖x‖
  let η : ℝ := -(planeToComplex x).arg / (2 * Real.pi)
  have hshift := integral_unitIntervalMeasure_shift_eq_of_periodic_complex
    (f := fun θ : ℝ => Complex.exp
      (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ))))
    (periodic_J0c_integrand u) η
  rw [← hshift]
  congr 1
  ext θ
  simpa [u, η] using circleFrequency_eq_J0c_shifted_integrand k θ x

lemma J0c_zero : J0c 0 = 1 := by
  unfold J0c
  simp [unitIntervalMeasure_real_univ]

lemma J0_zero : J0 0 = 1 := by
  simp [J0, J0c_zero]

lemma J0c_neg_conj (u : ℝ) : J0c (-u) = star (J0c u) := by
  unfold J0c
  change (∫ θ, Complex.exp
      (Complex.I * ((-u : ℝ) : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))
      ∂unitIntervalMeasure) =
    (starRingEnd ℂ) (∫ θ, Complex.exp
      (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))
      ∂unitIntervalMeasure)
  rw [← (integral_conj (μ := unitIntervalMeasure)
    (f := fun θ : ℝ => Complex.exp
      (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))))]
  apply integral_congr_ae
  exact ae_of_all _ (fun θ => by
    change Complex.exp (Complex.I * ((-u : ℝ) : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ))) =
      (starRingEnd ℂ) (Complex.exp (Complex.I * (u : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ))))
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring)

lemma J0c_neg (u : ℝ) : J0c (-u) = J0c u := by
  unfold J0c
  let f : ℝ → ℂ := fun θ : ℝ => Complex.exp
      (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))
  have hshift := integral_unitIntervalMeasure_shift_eq_of_periodic_complex
    (f := f) (periodic_J0c_integrand u) (1 / 2 : ℝ)
  rw [← hshift]
  apply integral_congr_ae
  exact ae_of_all _ (fun θ => by
    dsimp [f]
    congr 1
    have harg : 2 * Real.pi * (θ + 1 / 2) = 2 * Real.pi * θ + Real.pi := by
      ring
    have hcos : Real.cos (2 * Real.pi * (θ + 1 / 2)) =
        -Real.cos (2 * Real.pi * θ) := by
      rw [harg, Real.cos_add_pi]
    rw [hcos]
    push_cast
    ring)

lemma J0c_star_eq_self (u : ℝ) : star (J0c u) = J0c u := by
  rw [← J0c_neg_conj u, J0c_neg]

lemma J0c_eq_ofReal_J0 (u : ℝ) : (J0 u : ℂ) = J0c u := by
  have hstar := J0c_star_eq_self u
  have him := congrArg Complex.im hstar
  simp at him
  have hzero : (J0c u).im = 0 := by linarith
  apply Complex.ext <;> simp [J0, hzero]

lemma norm_circle_integrand (u θ : ℝ) :
    ‖Complex.exp
      (Complex.I * (u : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ)))‖ = 1 := by
  have harg :
      Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)) =
        Complex.ofReal (u * Real.cos (2 * Real.pi * θ)) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_J0c_le_one (u : ℝ) : ‖J0c u‖ ≤ 1 := by
  unfold J0c
  calc
    ‖∫ θ, Complex.exp
      (Complex.I * (u : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ))) ∂unitIntervalMeasure‖
        ≤ ∫ θ, ‖Complex.exp
      (Complex.I * (u : ℂ) *
        Complex.ofReal (Real.cos (2 * Real.pi * θ)))‖ ∂unitIntervalMeasure :=
          norm_integral_le_integral_norm _
    _ = ∫ _θ, (1 : ℝ) ∂unitIntervalMeasure := by
      congr 1
      ext θ
      exact norm_circle_integrand u θ
    _ = 1 := by
      simp [unitIntervalMeasure_real_univ]

lemma abs_J0_le_one (u : ℝ) : |J0 u| ≤ 1 := by
  unfold J0
  exact (Complex.abs_re_le_norm (J0c u)).trans (norm_J0c_le_one u)

lemma sum_pair_re_mul_star_nonneg (P : Finset Plane) (z : Plane → ℂ) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, (z p * star (z q)).re := by
  have hcomplex :
      (∑ p ∈ P, ∑ q ∈ P, z p * star (z q)) =
        (∑ p ∈ P, z p) * star (∑ p ∈ P, z p) := by
    calc
      (∑ p ∈ P, ∑ q ∈ P, z p * star (z q))
          = (∑ p ∈ P, z p) * (∑ q ∈ P, star (z q)) := by
            rw [Finset.sum_mul_sum]
      _ = (∑ p ∈ P, z p) * star (∑ p ∈ P, z p) := by
            congr 1
            exact (map_sum (starRingEnd ℂ) z P).symm
  have hre :
      (∑ p ∈ P, ∑ q ∈ P, (z p * star (z q)).re) =
        ((∑ p ∈ P, ∑ q ∈ P, z p * star (z q))).re := by
    simp_rw [Complex.re_sum]
  rw [hre, hcomplex]
  change 0 ≤ ((∑ p ∈ P, z p) * (starRingEnd ℂ) (∑ p ∈ P, z p)).re
  rw [Complex.mul_conj]
  exact Complex.normSq_nonneg _

lemma circleFrequency_pair_sum_nonneg (k : ℕ) (θ : ℝ) (P : Finset Plane) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, (circleFrequency k θ (p - q)).re := by
  simpa [circleFrequency_sub_eq_mul_star] using
    sum_pair_re_mul_star_nonneg P (fun p => circleFrequency k θ p)

/-- The real circle-average kernel associated to the integer frequency `k`. -/
noncomputable def circleKernel (k : ℕ) (x : Plane) : ℝ :=
  ∫ θ, (circleFrequency k θ x).re ∂unitIntervalMeasure

lemma circleKernel_eq_circleExpAverage_re (k : ℕ) (x : Plane) :
    circleKernel k x = (circleExpAverage k x).re := by
  unfold circleKernel circleExpAverage
  have h := Complex.reCLM.integral_comp_comm (integrable_circleFrequency k x)
  simpa using h

lemma circleKernel_xAxisPoint (k : ℕ) (t : ℝ) :
    circleKernel k (xAxisPoint t) = J0 (2 * Real.pi * (k : ℝ) * t) := by
  rw [circleKernel_eq_circleExpAverage_re, circleExpAverage_xAxisPoint]
  rfl

lemma circleKernel_eq_J0_norm (k : ℕ) (x : Plane) :
    circleKernel k x = J0 (2 * Real.pi * (k : ℝ) * ‖x‖) := by
  rw [circleKernel_eq_circleExpAverage_re, circleExpAverage_eq_J0c_norm]
  rfl

lemma circleKernel_pair_sum_eq_integral (k : ℕ) (P : Finset Plane) :
    (∑ p ∈ P, ∑ q ∈ P, circleKernel k (p - q)) =
      ∫ θ, (∑ p ∈ P, ∑ q ∈ P, (circleFrequency k θ (p - q)).re)
        ∂unitIntervalMeasure := by
  unfold circleKernel
  rw [MeasureTheory.integral_finset_sum]
  · congr 1
    ext p
    rw [MeasureTheory.integral_finset_sum]
    intro q _hq
    exact integrable_circleFrequency_re k (p - q)
  · intro p _hp
    exact MeasureTheory.integrable_finset_sum P
      (fun q _hq => integrable_circleFrequency_re k (p - q))

lemma circleKernel_pair_sum_nonneg (k : ℕ) (P : Finset Plane) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, circleKernel k (p - q) := by
  rw [circleKernel_pair_sum_eq_integral]
  exact MeasureTheory.integral_nonneg (fun θ => circleFrequency_pair_sum_nonneg k θ P)

lemma abs_circleKernel_le_one (k : ℕ) (x : Plane) :
    |circleKernel k x| ≤ 1 := by
  unfold circleKernel
  haveI : IsFiniteMeasure unitIntervalMeasure := ⟨by simp [unitIntervalMeasure_univ]⟩
  calc
    |∫ θ, (circleFrequency k θ x).re ∂unitIntervalMeasure| ≤
        ∫ θ, |(circleFrequency k θ x).re| ∂unitIntervalMeasure :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _θ, (1 : ℝ) ∂unitIntervalMeasure := by
      refine MeasureTheory.integral_mono (integrable_circleFrequency_re k x).abs
        (MeasureTheory.integrable_const (μ := unitIntervalMeasure) (1 : ℝ)) ?_
      intro θ
      exact (Complex.abs_re_le_norm (circleFrequency k θ x)).trans_eq
        (norm_circleFrequency k θ x)
    _ = 1 := by
      simp [unitIntervalMeasure_real_univ]

end CircleBessel
end Erdos953Formalization
