import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Erdos953Formalization

/-- The Euclidean plane, represented as finite-dimensional real Euclidean space. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Logical form of distance from the integer lattice: every integer is at least `δ` away. -/
def AwayFromIntegers (δ t : ℝ) : Prop :=
  ∀ n : ℤ, δ ≤ |t - (n : ℝ)|

/-- Logical form of distance from the positive integer radii. -/
def AwayFromPositiveIntegers (η t : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → η ≤ |t - (n : ℝ)|

/-- Finite robust point sets used in the Delsarte reduction. -/
def RobustFiniteSet (X δ : ℝ) (P : Finset Plane) : Prop :=
  (∀ p ∈ P, dist p 0 ≤ X) ∧
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q → AwayFromIntegers δ (dist p q))

/-- Measurable sets with no positive integer distances between distinct points. -/
def NoPositiveIntegerDistances (A : Set Plane) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ n : ℕ, 0 < n → dist x y ≠ (n : ℝ)

/-- Closed-ball version of the admissible sets for the upper-bound theorem. -/
def AdmissibleSet (R : ℝ) (A : Set Plane) : Prop :=
  MeasurableSet A ∧ A ⊆ Metric.closedBall (0 : Plane) R ∧ NoPositiveIntegerDistances A

/-- Lebesgue area of a set in the plane, as a real number. -/
noncomputable def area (A : Set Plane) : ℝ :=
  (volume A).toReal

/-- Extremal area of an admissible subset of the closed radius-`R` ball. -/
noncomputable def M (R : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ A : Set Plane, AdmissibleSet R A ∧ area A = a}

lemma noPositiveIntegerDistances_empty : NoPositiveIntegerDistances (∅ : Set Plane) := by
  intro x hx
  simp at hx

lemma admissibleSet_empty (R : ℝ) : AdmissibleSet R (∅ : Set Plane) := by
  refine ⟨MeasurableSet.empty, ?_, noPositiveIntegerDistances_empty⟩
  intro x hx
  simp at hx

lemma NoPositiveIntegerDistances.mono {A B : Set Plane}
    (hA : NoPositiveIntegerDistances A) (hBA : B ⊆ A) :
    NoPositiveIntegerDistances B := by
  intro x hx y hy hxy n hn
  exact hA x (hBA hx) y (hBA hy) hxy n hn

lemma AdmissibleSet.noPositiveIntegerDistances {R : ℝ} {A : Set Plane}
    (hA : AdmissibleSet R A) : NoPositiveIntegerDistances A :=
  hA.2.2

lemma AdmissibleSet.subset_closedBall {R : ℝ} {A : Set Plane}
    (hA : AdmissibleSet R A) : A ⊆ Metric.closedBall (0 : Plane) R :=
  hA.2.1

lemma AdmissibleSet.mono_set {R : ℝ} {A B : Set Plane}
    (hA : AdmissibleSet R A) (hBmeas : MeasurableSet B) (hBA : B ⊆ A) :
    AdmissibleSet R B := by
  exact ⟨hBmeas, hBA.trans hA.subset_closedBall,
    hA.noPositiveIntegerDistances.mono hBA⟩

lemma area_empty : area (∅ : Set Plane) = 0 := by
  unfold area
  simp

lemma zero_mem_M_definingSet (R : ℝ) :
    0 ∈ {a : ℝ | ∃ A : Set Plane, AdmissibleSet R A ∧ area A = a} := by
  refine ⟨∅, admissibleSet_empty R, ?_⟩
  simp [area_empty]

/-- The reciprocal square-root weight appearing in the off-diagonal kernel bound. -/
def invSqrtOnePlus (t : ℝ) : ℝ :=
  (Real.sqrt (1 + t))⁻¹

lemma invSqrtOnePlus_nonneg (t : ℝ) : 0 ≤ invSqrtOnePlus t := by
  unfold invSqrtOnePlus
  positivity

lemma invSqrtOnePlus_pos {t : ℝ} (ht : -1 < t) : 0 < invSqrtOnePlus t := by
  unfold invSqrtOnePlus
  exact inv_pos.mpr (Real.sqrt_pos.2 (by linarith))

lemma away_mono {δ η t : ℝ} (hδη : δ ≤ η)
    (h : AwayFromIntegers η t) : AwayFromIntegers δ t := by
  intro n
  exact hδη.trans (h n)

lemma away_pos_mono {δ η t : ℝ} (hδη : δ ≤ η)
    (h : AwayFromPositiveIntegers η t) : AwayFromPositiveIntegers δ t := by
  intro n hn
  exact hδη.trans (h n hn)

lemma away_zero_le_abs {δ t : ℝ} (h : AwayFromIntegers δ t) : δ ≤ |t| := by
  simpa using h 0

lemma away_of_away_pos_and_ge_delta
    {δ η t : ℝ} (hδη : δ ≤ η) (ht0 : 0 ≤ t) (hδt : δ ≤ t)
    (hpos : AwayFromPositiveIntegers η t) :
    AwayFromIntegers δ t := by
  intro n
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          simpa [abs_of_nonneg ht0] using hδt
      | succ k =>
          exact hδη.trans (by simpa using hpos (k + 1) (Nat.succ_pos k))
  | negSucc k =>
      have hn_nonpos : (((Int.negSucc k : ℤ) : ℝ) ≤ 0) := by
        rw [Int.cast_negSucc]
        have hk_nonneg : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
        linarith
      have hnonneg : 0 ≤ t - ((Int.negSucc k : ℤ) : ℝ) := by
        linarith
      rw [abs_of_nonneg hnonneg]
      have ht_le : t ≤ t - ((Int.negSucc k : ℤ) : ℝ) := by
        linarith
      exact hδt.trans ht_le

lemma robustFiniteSet_of_positive_integer_separation
    {X δ η : ℝ} {P : Finset Plane}
    (hδη : δ ≤ η)
    (hbound : ∀ p ∈ P, dist p 0 ≤ X)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q)
    (hawaypos :
      ∀ p ∈ P, ∀ q ∈ P, p ≠ q → AwayFromPositiveIntegers η (dist p q)) :
    RobustFiniteSet X δ P := by
  refine ⟨hbound, ?_⟩
  intro p hp q hq hpq
  exact away_of_away_pos_and_ge_delta hδη dist_nonneg
    (hsep p hp q hq hpq) (hawaypos p hp q hq hpq)

end Erdos953Formalization
