import FormalConjecturesBench.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.MetricSpace.CoveringNumbers

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos953Formalization

lemma volume_closedBall_plane_lt_top (x : Plane) (R : ℝ) :
    volume (Metric.closedBall x R) < ∞ := by
  rw [EuclideanSpace.volume_closedBall]
  finiteness

lemma admissibleSet_volume_lt_top {R : ℝ} {A : Set Plane} (hA : AdmissibleSet R A) :
    volume A < ∞ := by
  exact lt_of_le_of_lt (measure_mono hA.subset_closedBall) (volume_closedBall_plane_lt_top 0 R)

lemma area_nonneg (A : Set Plane) : 0 ≤ area A := by
  unfold area
  positivity

lemma area_mono_of_subset_of_finite {A B : Set Plane}
    (hAB : A ⊆ B) (hBfin : volume B < ∞) : area A ≤ area B := by
  unfold area
  exact ENNReal.toReal_mono (ne_of_lt hBfin) (measure_mono hAB)

lemma area_mono_of_subset_admissible {R : ℝ} {A B : Set Plane}
    (hB : AdmissibleSet R B) (hAB : A ⊆ B) : area A ≤ area B := by
  exact area_mono_of_subset_of_finite hAB (admissibleSet_volume_lt_top hB)

lemma area_le_of_compact_subsets_area_le
    {A : Set Plane} {C : ℝ} (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ∞)
    (hCnonneg : 0 ≤ C)
    (hcompact : ∀ K : Set Plane, IsCompact K → K ⊆ A → area K ≤ C) :
    area A ≤ C := by
  have hμA_le : volume A ≤ ENNReal.ofReal C := by
    rw [hAmeas.measure_eq_iSup_isCompact_of_ne_top hAfin]
    refine iSup_le ?_
    intro K
    refine iSup_le ?_
    intro hKA
    refine iSup_le ?_
    intro hKcompact
    have hKfin : volume K ≠ ∞ := ne_of_lt hKcompact.measure_lt_top
    exact (ENNReal.le_ofReal_iff_toReal_le hKfin hCnonneg).2 (hcompact K hKcompact hKA)
  unfold area
  exact ENNReal.toReal_le_of_le_ofReal hCnonneg hμA_le

lemma area_closedBall_plane_eq_pi_mul_sq (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    area (Metric.closedBall x r) = Real.pi * r ^ 2 := by
  unfold area
  rw [EuclideanSpace.volume_closedBall]
  change (ENNReal.ofReal r ^ 2 *
      ENNReal.ofReal (√Real.pi ^ 2 / Real.Gamma ((2 : ℝ) / 2 + 1))).toReal =
    Real.pi * r ^ 2
  norm_num [Real.Gamma_nat_eq_factorial]
  rw [Real.sq_sqrt Real.pi_pos.le]
  simp [ENNReal.toReal_ofReal, hr]
  ring

lemma area_le_card_mul_ball_area
    {K : Set Plane} {P : Finset Plane} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hcover : K ⊆ ⋃ p ∈ P, Metric.closedBall p δ) :
    area K ≤ (P.card : ℝ) * Real.pi * δ ^ 2 := by
  have hmeasure : volume K ≤ ∑ p ∈ P, volume (Metric.closedBall p δ) := by
    exact (measure_mono hcover).trans
      (MeasureTheory.measure_biUnion_finset_le P (fun p => Metric.closedBall p δ))
  have hsum_finite : (∑ p ∈ P, volume (Metric.closedBall p δ)) ≠ ∞ := by
    exact ne_of_lt ((ENNReal.sum_lt_top).2
      (fun p _hp => volume_closedBall_plane_lt_top p δ))
  calc
    area K = (volume K).toReal := rfl
    _ ≤ (∑ p ∈ P, volume (Metric.closedBall p δ)).toReal :=
      ENNReal.toReal_mono hsum_finite hmeasure
    _ = ∑ p ∈ P, area (Metric.closedBall p δ) := by
      rw [ENNReal.toReal_sum]
      · rfl
      · intro p _hp
        exact ne_of_lt (volume_closedBall_plane_lt_top p δ)
    _ = ∑ _p ∈ P, Real.pi * δ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro p _hp
      exact area_closedBall_plane_eq_pi_mul_sq p hδ
    _ = (P.card : ℝ) * Real.pi * δ ^ 2 := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
      ring

/-- Final supremum step: a uniform area bound for admissible sets bounds `M`. -/
lemma M_le_of_admissible_area_bound
    {R C : ℝ} (hbound : ∀ A : Set Plane, AdmissibleSet R A → area A ≤ C) :
    M R ≤ C := by
  unfold M
  refine csSup_le ?_ ?_
  · exact ⟨0, zero_mem_M_definingSet R⟩
  · intro a ha
    rcases ha with ⟨A, hA, rfl⟩
    exact hbound A hA

lemma M_le_sqrt_of_admissible_area_bound {C : ℝ}
    (hbound : ∀ R : ℝ, ∀ A : Set Plane, 1 ≤ R → AdmissibleSet R A →
      area A ≤ C * Real.sqrt R) :
    ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  intro R hR
  exact M_le_of_admissible_area_bound (R := R) (C := C * Real.sqrt R)
    (fun A hA => hbound R A hR hA)

theorem erdos953_upper_from_admissible_area_bound
    (harea : ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, ∀ A : Set Plane, 1 ≤ R → AdmissibleSet R A →
        area A ≤ C * Real.sqrt R) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  rcases harea with ⟨C, hCpos, hbound⟩
  exact ⟨C, hCpos, M_le_sqrt_of_admissible_area_bound hbound⟩

/--
A finite separated subset of a compact/admissible set is robust once the compact
set has uniform separation from positive integer distances.
-/
lemma robust_of_compact_net
    {R δ η : ℝ} {K : Set Plane} {P : Finset Plane}
    (hδη : δ ≤ η)
    (hPsub : ∀ p ∈ P, p ∈ K)
    (hPsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hKaway :
      ∀ x ∈ K, ∀ y ∈ K, x ≠ y → AwayFromPositiveIntegers η (dist x y)) :
    RobustFiniteSet R δ P := by
  refine robustFiniteSet_of_positive_integer_separation hδη ?_ hPsep ?_
  · intro p hp
    have hpball := hKsub (hPsub p hp)
    simpa [Metric.mem_closedBall] using hpball
  · intro p hp q hq hpq
    exact hKaway p (hPsub p hp) q (hPsub q hq) hpq

lemma packingNumber_ne_top_of_isCompact_nnreal {K : Set Plane} {ε : ℝ≥0}
    (hε : ε ≠ 0) (hK : IsCompact K) :
    Metric.packingNumber ε K ≠ ⊤ := by
  have hε2 : ε / 2 ≠ 0 := by
    exact div_ne_zero hε (by norm_num : (2 : ℝ≥0) ≠ 0)
  rcases Metric.exists_finite_isCover_of_isCompact (ε := ε / 2) hε2 hK with
    ⟨N, _hNK, hNfin, hcover⟩
  have hcover_lt_top : Metric.externalCoveringNumber (ε / 2) K < ⊤ := by
    have hle := Metric.IsCover.externalCoveringNumber_le_encard (A := K) (C := N) hcover
    exact lt_of_le_of_lt hle (by simpa using hNfin.encard_lt_top)
  have hp_le : Metric.packingNumber ε K ≤ Metric.externalCoveringNumber (ε / 2) K := by
    simpa [show (2 : ℝ≥0) * (ε / 2) = ε by field_simp] using
      Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) K
  exact ne_of_lt (lt_of_le_of_lt hp_le hcover_lt_top)

lemma finite_maximalSeparatedSet_of_packing_ne_top {K : Set Plane} {ε : ℝ≥0}
    (hpack : Metric.packingNumber ε K ≠ ⊤) :
    (Metric.maximalSeparatedSet ε K).Finite := by
  refine Set.encard_lt_top_iff.mp ?_
  rw [Metric.encard_maximalSeparatedSet hpack]
  exact lt_top_iff_ne_top.mpr hpack

/--
Compact metric sets have finite separated nets.  We use mathlib's maximal
separated set at radius `δ`; compactness makes its packing number finite, and
maximality makes it a closed-ball cover.
-/
lemma exists_finite_separated_net_of_isCompact
    {K : Set Plane} {δ : ℝ} (hK : IsCompact K) (hδpos : 0 < δ) :
    ∃ P : Finset Plane,
      (∀ p ∈ P, p ∈ K) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q) ∧
      K ⊆ ⋃ p ∈ P, Metric.closedBall p δ := by
  let ε : ℝ≥0 := Real.toNNReal δ
  have hε_ne : ε ≠ 0 := by
    apply ne_of_gt
    exact Real.toNNReal_pos.mpr hδpos
  have hpack : Metric.packingNumber ε K ≠ ⊤ :=
    packingNumber_ne_top_of_isCompact_nnreal hε_ne hK
  let S : Set Plane := Metric.maximalSeparatedSet ε K
  have hSfin : S.Finite := finite_maximalSeparatedSet_of_packing_ne_top hpack
  let P : Finset Plane := hSfin.toFinset
  refine ⟨P, ?_, ?_, ?_⟩
  · intro p hp
    have hpS : p ∈ S := by simpa [P] using (hSfin.mem_toFinset).mp hp
    exact Metric.maximalSeparatedSet_subset hpS
  · intro p hp q hq hpq
    have hpS : p ∈ S := by simpa [P] using (hSfin.mem_toFinset).mp hp
    have hqS : q ∈ S := by simpa [P] using (hSfin.mem_toFinset).mp hq
    have hsep := Metric.isSeparated_maximalSeparatedSet (A := K) (ε := ε) hpS hqS hpq
    have hdist_lt : δ < dist p q := by
      have hsep' : ENNReal.ofReal δ < edist p q := by
        simpa [ε, Real.coe_toNNReal δ hδpos.le] using hsep
      rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδpos.le] at hsep'
    exact le_of_lt hdist_lt
  · have hcover := Metric.isCover_maximalSeparatedSet (A := K) (ε := ε) hpack
    have hsub := Metric.IsCover.subset_iUnion_closedBall hcover
    intro x hx
    have hxunion := hsub hx
    simp only [Set.mem_iUnion, exists_prop] at hxunion
    rcases hxunion with ⟨p, hpS, hxp⟩
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨(hSfin.mem_toFinset).mpr hpS,
      by simpa [ε, Real.coe_toNNReal δ hδpos.le] using hxp⟩⟩

/--
If a compact set has a finite `δ`-net whose points remain `δ`-separated and
the set stays `η` away from positive integer distances, the robust finite-set
estimate bounds its area.
-/
lemma compact_area_le_of_net_and_robust_bound
    {Crob R δ η : ℝ} {K : Set Plane} {P : Finset Plane}
    (hCrobpos : 0 < Crob)
    (hrob : ∀ (X δ : ℝ) (P : Finset Plane),
      1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
      (P.card : ℝ) ≤ Crob * (δ ^ 2)⁻¹ * Real.sqrt X)
    (hR : 1 ≤ R) (hδpos : 0 < δ) (hδsmall : δ < 1 / 10)
    (hδη : δ ≤ η)
    (hPsub : ∀ p ∈ P, p ∈ K)
    (hPsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hKaway : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → AwayFromPositiveIntegers η (dist x y))
    (hcover : K ⊆ ⋃ p ∈ P, Metric.closedBall p δ) :
    area K ≤ Real.pi * Crob * Real.sqrt R := by
  have hP : RobustFiniteSet R δ P :=
    robust_of_compact_net hδη hPsub hPsep hKsub hKaway
  have hcard := hrob R δ P hR hδpos hδsmall hP
  have harea := area_le_card_mul_ball_area hδpos.le hcover
  have hfactor_nonneg : 0 ≤ Real.pi * δ ^ 2 := by positivity
  have hmul : (P.card : ℝ) * (Real.pi * δ ^ 2) ≤
      (Crob * (δ ^ 2)⁻¹ * Real.sqrt R) * (Real.pi * δ ^ 2) :=
    mul_le_mul_of_nonneg_right hcard hfactor_nonneg
  calc
    area K ≤ (P.card : ℝ) * Real.pi * δ ^ 2 := harea
    _ ≤ (Crob * (δ ^ 2)⁻¹ * Real.sqrt R) * Real.pi * δ ^ 2 := by
      convert hmul using 1 <;> ring
    _ = Real.pi * Crob * Real.sqrt R := by
      have hδsq : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδpos.ne'
      field_simp [hδsq]

/--
Compact-set area bound obtained by constructing the separated net internally.
The only geometric hypothesis still external here is the uniform margin `η`
from all positive integer distances inside `K`.
-/
lemma compact_area_le_of_robust_bound
    {Crob R δ η : ℝ} {K : Set Plane}
    (hCrobpos : 0 < Crob)
    (hrob : ∀ (X δ : ℝ) (P : Finset Plane),
      1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
      (P.card : ℝ) ≤ Crob * (δ ^ 2)⁻¹ * Real.sqrt X)
    (hKcompact : IsCompact K)
    (hR : 1 ≤ R) (hδpos : 0 < δ) (hδsmall : δ < 1 / 10)
    (hδη : δ ≤ η)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hKaway : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → AwayFromPositiveIntegers η (dist x y)) :
    area K ≤ Real.pi * Crob * Real.sqrt R := by
  rcases exists_finite_separated_net_of_isCompact hKcompact hδpos with
    ⟨P, hPsub, hPsep, hcover⟩
  exact compact_area_le_of_net_and_robust_bound hCrobpos hrob hR hδpos hδsmall hδη
    hPsub hPsep hKsub hKaway hcover

/-- Version of the compact area bound that chooses the net scale from `η`. -/
lemma compact_area_le_of_robust_bound_with_eta
    {Crob R η : ℝ} {K : Set Plane}
    (hCrobpos : 0 < Crob)
    (hrob : ∀ (X δ : ℝ) (P : Finset Plane),
      1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
      (P.card : ℝ) ≤ Crob * (δ ^ 2)⁻¹ * Real.sqrt X)
    (hKcompact : IsCompact K)
    (hR : 1 ≤ R) (hηpos : 0 < η)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hKaway : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → AwayFromPositiveIntegers η (dist x y)) :
    area K ≤ Real.pi * Crob * Real.sqrt R := by
  let δ : ℝ := min (η / 2) (1 / 20)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδsmall : δ < 1 / 10 := by
    dsimp [δ]
    have hmin : min (η / 2) (1 / 20 : ℝ) ≤ 1 / 20 := min_le_right _ _
    linarith
  have hδη : δ ≤ η := by
    dsimp [δ]
    have hmin : min (η / 2) (1 / 20 : ℝ) ≤ η / 2 := min_le_left _ _
    linarith
  exact compact_area_le_of_robust_bound hCrobpos hrob hKcompact hR hδpos hδsmall hδη
    hKsub hKaway

/--
For one fixed positive integer radius, compactness upgrades pointwise avoidance
of that radius into a uniform positive distance from it.
-/
lemma exists_pos_lower_abs_dist_nat_of_compact
    {K : Set Plane} (hKcompact : IsCompact K) (hno : NoPositiveIntegerDistances K)
    (n : ℕ) (hn : 0 < n) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ y ∈ K, η ≤ |dist x y - (n : ℝ)| := by
  by_cases hKnonempty : K.Nonempty
  · let S : Set (Plane × Plane) := K ×ˢ K
    have hScompact : IsCompact S := hKcompact.prod hKcompact
    have hSnonempty : S.Nonempty := by
      rcases hKnonempty with ⟨x, hx⟩
      exact ⟨(x, x), hx, hx⟩
    let f : Plane × Plane → ℝ := fun z => |dist z.1 z.2 - (n : ℝ)|
    have hfcont : ContinuousOn f S := by
      exact ((continuous_dist.sub continuous_const).abs).continuousOn
    rcases hScompact.exists_isMinOn hSnonempty hfcont with ⟨z, hzS, hzmin⟩
    have hzpos : 0 < f z := by
      have hzne : dist z.1 z.2 ≠ (n : ℝ) := by
        intro hdist
        have hneq : z.1 ≠ z.2 := by
          intro hzy
          have hzero : (0 : ℝ) = (n : ℝ) := by simpa [hzy] using hdist
          exact (ne_of_gt (Nat.cast_pos.mpr hn : (0 : ℝ) < n)) hzero.symm
        exact hno z.1 hzS.1 z.2 hzS.2 hneq n hn hdist
      exact abs_pos.mpr (sub_ne_zero.mpr hzne)
    refine ⟨f z, hzpos, ?_⟩
    intro x hx y hy
    exact (isMinOn_iff.mp hzmin) (x, y) ⟨hx, hy⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hKnonempty ⟨x, hx⟩)

/-- Uniform lower bound over a finite set of positive integer radii. -/
lemma exists_pos_lower_abs_dist_nat_finset_of_compact
    {K : Set Plane} (hKcompact : IsCompact K) (hno : NoPositiveIntegerDistances K)
    (F : Finset ℕ) (hFpos : ∀ n ∈ F, 0 < n) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ n ∈ F, η ≤ |dist x y - (n : ℝ)| := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro x hx y hy n hn
      simp at hn
  | insert a s has ih =>
      have hapos : 0 < a := hFpos a (by simp)
      rcases exists_pos_lower_abs_dist_nat_of_compact hKcompact hno a hapos with
        ⟨ηa, hηapos, hηa⟩
      have hspos : ∀ n ∈ s, 0 < n := by
        intro n hn
        exact hFpos n (by simp [hn])
      rcases ih hspos with ⟨ηs, hηspos, hηs⟩
      refine ⟨min ηa ηs, lt_min hηapos hηspos, ?_⟩
      intro x hx y hy n hn
      rw [Finset.mem_insert] at hn
      rcases hn with rfl | hn
      · exact (min_le_left _ _).trans (hηa x hx y hy)
      · exact (min_le_right _ _).trans (hηs x hx y hy n hn)

lemma dist_le_two_mul_of_mem_closedBall
    {R : ℝ} {K : Set Plane} (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    {x y : Plane} (hx : x ∈ K) (hy : y ∈ K) :
    dist x y ≤ 2 * R := by
  have hxR : dist x 0 ≤ R := by
    simpa [Metric.mem_closedBall] using hKsub hx
  have hyR : dist y 0 ≤ R := by
    simpa [Metric.mem_closedBall] using hKsub hy
  calc
    dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
    _ = dist x 0 + dist y 0 := by rw [dist_comm 0 y]
    _ ≤ R + R := add_le_add hxR hyR
    _ = 2 * R := by ring

/--
A compact set in a bounded ball with no positive integer distances has a
uniform positive margin from all positive integer distances.
-/
lemma exists_eta_away_positive_integers_of_compact
    {R : ℝ} {K : Set Plane} (hKcompact : IsCompact K)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hno : NoPositiveIntegerDistances K) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ K, ∀ y ∈ K, x ≠ y → AwayFromPositiveIntegers η (dist x y) := by
  classical
  let N : ℕ := Nat.ceil (2 * R)
  let F : Finset ℕ := Finset.Icc 1 N
  have hFpos : ∀ n ∈ F, 0 < n := by
    intro n hn
    exact lt_of_lt_of_le (by norm_num : 0 < 1) (Finset.mem_Icc.mp hn).1
  rcases exists_pos_lower_abs_dist_nat_finset_of_compact hKcompact hno F hFpos with
    ⟨ηF, hηFpos, hηF⟩
  refine ⟨min ηF 1, lt_min hηFpos (by norm_num), ?_⟩
  intro x hx y hy _hxy n hnpos
  by_cases hnF : n ∈ F
  · exact (min_le_left _ _).trans (hηF x hx y hy n hnF)
  · have hn_ge_one : 1 ≤ n := Nat.succ_le_iff.mpr hnpos
    have hN_lt_n : N < n := by
      by_contra hnot
      have hn_le_N : n ≤ N := le_of_not_gt hnot
      exact hnF (Finset.mem_Icc.mpr ⟨hn_ge_one, hn_le_N⟩)
    have hNsucc_le_n : N + 1 ≤ n := Nat.succ_le_of_lt hN_lt_n
    have hNsucc_le_n_real : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hNsucc_le_n
    have hdist_le_2R : dist x y ≤ 2 * R := dist_le_two_mul_of_mem_closedBall hKsub hx hy
    have h2R_le_N : 2 * R ≤ (N : ℝ) := by
      exact Nat.le_ceil (2 * R)
    have hdist_le_N : dist x y ≤ (N : ℝ) := hdist_le_2R.trans h2R_le_N
    have hdiff_ge_one : 1 ≤ (n : ℝ) - dist x y := by linarith
    have hnonpos : dist x y - (n : ℝ) ≤ 0 := by linarith
    have habs_ge_one : 1 ≤ |dist x y - (n : ℝ)| := by
      rw [abs_of_nonpos hnonpos]
      linarith
    exact (min_le_right _ _).trans habs_ge_one

/--
Compact no-integer-distance sets satisfy the area bound supplied by the robust
finite theorem.
-/
lemma compact_area_le_of_robust_bound_no_int
    {Crob R : ℝ} {K : Set Plane}
    (hCrobpos : 0 < Crob)
    (hrob : ∀ (X δ : ℝ) (P : Finset Plane),
      1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
      (P.card : ℝ) ≤ Crob * (δ ^ 2)⁻¹ * Real.sqrt X)
    (hKcompact : IsCompact K) (hR : 1 ≤ R)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hno : NoPositiveIntegerDistances K) :
    area K ≤ Real.pi * Crob * Real.sqrt R := by
  rcases exists_eta_away_positive_integers_of_compact hKcompact hKsub hno with
    ⟨η, hηpos, hKaway⟩
  exact compact_area_le_of_robust_bound_with_eta hCrobpos hrob hKcompact hR hηpos hKsub hKaway

/--
Measurable reduction: a robust finite-set theorem implies the corresponding
area bound for every admissible measurable set.
-/
lemma admissible_area_le_of_robust_bound
    {Crob R : ℝ}
    (hCrobpos : 0 < Crob)
    (hrob : ∀ (X δ : ℝ) (P : Finset Plane),
      1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
      (P.card : ℝ) ≤ Crob * (δ ^ 2)⁻¹ * Real.sqrt X)
    (hR : 1 ≤ R) (A : Set Plane) (hA : AdmissibleSet R A) :
    area A ≤ Real.pi * Crob * Real.sqrt R := by
  refine area_le_of_compact_subsets_area_le hA.1 (ne_of_lt (admissibleSet_volume_lt_top hA)) ?_ ?_
  · positivity
  · intro K hKcompact hKA
    exact compact_area_le_of_robust_bound_no_int hCrobpos hrob hKcompact hR
      (hKA.trans hA.subset_closedBall)
      (hA.noPositiveIntegerDistances.mono hKA)

/--
Full measurable-set reduction from the robust finite estimate to the stated
upper bound for `M(R)`.
-/
theorem erdos953_upper_from_robust_finite_bound
    (hrobust : ∃ Crob : ℝ, 0 < Crob ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ Crob * (δ ^ 2)⁻¹ * Real.sqrt X) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  rcases hrobust with ⟨Crob, hCrobpos, hrob⟩
  refine erdos953_upper_from_admissible_area_bound ⟨Real.pi * Crob, ?_, ?_⟩
  · positivity
  · intro R A hR hA
    simpa [mul_assoc] using admissible_area_le_of_robust_bound hCrobpos hrob hR A hA

end Erdos953Formalization
