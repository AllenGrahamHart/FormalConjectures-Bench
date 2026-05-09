import FormalConjecturesBench.MeasureReduction
import FormalConjecturesBench.PoissonFormula
import FormalConjecturesBench.RobustPointBound

noncomputable section

namespace Erdos953Formalization

/--
Main theorem conditional on the remaining Poisson-side formula.  The termwise
sign estimates, finite Delsarte argument, and measurable reduction are fully
discharged by this point.
-/
theorem erdos953_upper_from_poisson_formula
    (hpoisson : K_besselPoissonFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_robust_finite_bound
    (robust_finite_bound_from_poisson hpoisson)

/--
Top-level reduction to the remaining explicit Fourier-transform computation.
-/
theorem erdos953_upper_from_fourier_formula
    (hformula : PoissonKernelFourierFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_poisson_formula
    (K_besselPoissonFormula_of_fourierFormula hformula)

/--
Top-level reduction to the two explicit half-line Laplace-Bessel moment
evaluations.
-/
theorem erdos953_upper_from_moment_formula
    (hformula : PoissonKernelMomentFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_poisson_formula
    (K_besselPoissonFormula_of_momentFormula hformula)

/--
Top-level reduction to the two explicit angular rational-integral identities.
-/
theorem erdos953_upper_from_angular_formula
    (hformula : PoissonKernelAngularFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_poisson_formula
    (K_besselPoissonFormula_of_angularFormula hformula)

/--
Top-level reduction to the same two identities as circle averages on the unit
circle, ready for a contour-integral calculation.
-/
theorem erdos953_upper_from_circle_average_formula
    (hformula : PoissonKernelCircleAverageFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_poisson_formula
    (K_besselPoissonFormula_of_circleAverageFormula hformula)

/--
Top-level reduction to the positive-radius circle-average identities.  The
`t = 0` branch has been discharged separately.
-/
theorem erdos953_upper_from_circle_average_formula_pos
    (hformula : PoissonKernelCircleAverageFormulaPos) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_poisson_formula
    (K_besselPoissonFormula_of_circleAverageFormulaPos hformula)

/--
Top-level reduction to the residue calculation for the two unit-circle contour
integrals.
-/
theorem erdos953_upper_from_contour_formula
    (hformula : PoissonKernelContourFormula) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_poisson_formula
    (K_besselPoissonFormula_of_contourFormula hformula)

/--
Upper-bound half of the order-of-growth resolution of Erdős Problem #953,
formalised for closed balls in the Euclidean plane.
-/
theorem erdos953_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  exact erdos953_upper_from_circle_average_formula_pos
    PoissonKernelCircleAverageFormulaPos_residue

end Erdos953Formalization
