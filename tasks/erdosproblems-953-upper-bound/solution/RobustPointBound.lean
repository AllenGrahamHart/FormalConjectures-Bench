import FormalConjecturesBench.Delsarte
import FormalConjecturesBench.TermNegativity

noncomputable section

namespace Erdos953Formalization

/--
The remaining Poisson-side sign theorem needed to instantiate the Delsarte
package for the Bessel kernel.
-/
def K_besselOffdiagNegativity : Prop :=
  ∃ A cneg s0 : ℝ,
    0 < A ∧ 0 < cneg ∧ 0 < s0 ∧
      ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A * s) t →
        K_bessel s t ≤ -cneg * invSqrtOnePlus t

/-- Poisson-side representation of `K_bessel` with summability of its term series. -/
def K_besselPoissonFormula : Prop :=
  ∀ (s t : ℝ), 0 < s → 0 ≤ t →
    Summable (fun m : ℤ => Tterm s t m) ∧
      K_bessel s t = ∑' m : ℤ, Tterm s t m

/-- Every Poisson-side term is non-positive under uniform integer separation. -/
def TtermNonposAway : Prop :=
  ∃ A s0 : ℝ, 0 < A ∧ 0 < s0 ∧
    ∀ (s t : ℝ) (m : ℤ), 0 < s → s < s0 → 0 ≤ t →
      AwayFromIntegers (A * s) t → Tterm s t m ≤ 0

/-- At least one Poisson-side term is quantitatively negative under integer separation. -/
def TtermExistsNegativeAway : Prop :=
  ∃ A c s0 : ℝ, 0 < A ∧ 0 < c ∧ 0 < s0 ∧
    ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A * s) t →
      ∃ m : ℤ, Tterm s t m ≤ -c * invSqrtOnePlus t

theorem Tterm_exists_negative_away : TtermExistsNegativeAway :=
  exists_negative_ceiling_term

theorem Tterm_nonpos_away : TtermNonposAway :=
  Tterm_nonpos_away_terms

/--
The final off-diagonal kernel estimate follows formally from the Poisson
formula, termwise non-positivity, and one quantitatively negative term.
-/
theorem K_bessel_offdiag_from_poisson_terms
    (hpoisson : K_besselPoissonFormula)
    (hnonpos : TtermNonposAway)
    (hnegative : TtermExistsNegativeAway) :
    K_besselOffdiagNegativity := by
  rcases hnonpos with ⟨Anonpos, s0nonpos, hAnonpospos, hs0nonpos, hnonpos_terms⟩
  rcases hnegative with ⟨Aneg, c, s0neg, hAnegpos, hcpos, hs0negpos, hneg_term⟩
  let A : ℝ := Aneg + Anonpos + 1
  let s0 : ℝ := min s0nonpos s0neg
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hs0pos : 0 < s0 := lt_min hs0nonpos hs0negpos
  refine ⟨A, c, s0, hApos, hcpos, hs0pos, ?_⟩
  intro s t hs hss0 ht haway
  have hs_nonneg : 0 ≤ s := hs.le
  have hAneg_le_A : Aneg ≤ A := by
    dsimp [A]
    linarith
  have hAnonpos_le_A : Anonpos ≤ A := by
    dsimp [A]
    linarith
  have haway_neg : AwayFromIntegers (Aneg * s) t := by
    exact away_mono (mul_le_mul_of_nonneg_right hAneg_le_A hs_nonneg) haway
  have haway_nonpos : AwayFromIntegers (Anonpos * s) t := by
    exact away_mono (mul_le_mul_of_nonneg_right hAnonpos_le_A hs_nonneg) haway
  have hs_lt_nonpos : s < s0nonpos := hss0.trans_le (min_le_left _ _)
  have hs_lt_neg : s < s0neg := hss0.trans_le (min_le_right _ _)
  rcases hneg_term s t hs hs_lt_neg ht haway_neg with ⟨m0, hm0neg⟩
  rcases hpoisson s t hs ht with ⟨hsumm, hK⟩
  rw [hK]
  refine (tsum_le_term_of_summable_nonpos hsumm ?_ m0).trans hm0neg
  intro m
  exact hnonpos_terms s t m hs hs_lt_nonpos ht haway_nonpos

/--
The finite robust point bound reduced to the off-diagonal negativity theorem.
Positive definiteness and the diagonal estimate are already proved for `K_bessel`.
-/
theorem robust_finite_bound_from_K_bessel_offdiag
    (hoff : K_besselOffdiagNegativity) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X := by
  rcases hoff with ⟨A, cneg, s0neg, hApos, hcpos, hs0negpos, hneg⟩
  let pkg : DelsarteKernelPackage :=
    { K := K_bessel
      A := A
      cneg := cneg
      Cdiag := 36
      s0 := min s0neg (1 / 2)
      A_pos := hApos
      cneg_pos := hcpos
      Cdiag_pos := by norm_num
      s0_pos := lt_min hs0negpos (by norm_num)
      pos_def := by
        intro s hs _hss0 P
        exact K_bessel_pos_def hs P
      diag_bound := by
        intro s hs hss0
        exact K_bessel_diag_bound_explicit hs
          ((le_of_lt hss0).trans (min_le_right _ _))
      offdiag_bound := by
        intro s t hs hss0 ht haway
        exact hneg s t hs (hss0.trans_le (min_le_left _ _)) ht haway }
  exact robust_finite_bound_from_kernel pkg

theorem robust_finite_bound_from_poisson_terms
    (hpoisson : K_besselPoissonFormula)
    (hnonpos : TtermNonposAway)
    (hnegative : TtermExistsNegativeAway) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X :=
  robust_finite_bound_from_K_bessel_offdiag
    (K_bessel_offdiag_from_poisson_terms hpoisson hnonpos hnegative)

theorem robust_finite_bound_from_poisson_and_nonpos
    (hpoisson : K_besselPoissonFormula)
    (hnonpos : TtermNonposAway) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X :=
  robust_finite_bound_from_poisson_terms hpoisson hnonpos Tterm_exists_negative_away

theorem robust_finite_bound_from_poisson
    (hpoisson : K_besselPoissonFormula) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X :=
  robust_finite_bound_from_poisson_and_nonpos hpoisson Tterm_nonpos_away

end Erdos953Formalization
