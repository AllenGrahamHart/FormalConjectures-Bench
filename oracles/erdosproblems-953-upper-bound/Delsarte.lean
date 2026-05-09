import FormalConjecturesBench.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.CastCard
import Mathlib.Tactic

noncomputable section

open Finset
open scoped BigOperators

namespace Erdos953Formalization

/--
Abstract Delsarte package for a radial kernel.  The analytic part of the
Poisson-Bessel proof will instantiate this structure for `K_bessel`.
-/
structure DelsarteKernelPackage where
  K : ℝ → ℝ → ℝ
  A : ℝ
  cneg : ℝ
  Cdiag : ℝ
  s0 : ℝ
  A_pos : 0 < A
  cneg_pos : 0 < cneg
  Cdiag_pos : 0 < Cdiag
  s0_pos : 0 < s0
  pos_def :
    ∀ (s : ℝ), 0 < s → s < s0 →
      ∀ (P : Finset Plane),
        0 ≤ (∑ p ∈ P, ∑ q ∈ P, K s (dist p q))
  diag_bound :
    ∀ (s : ℝ), 0 < s → s < s0 → K s 0 ≤ Cdiag * (s ^ 2)⁻¹
  offdiag_bound :
    ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A * s) t →
      K s t ≤ -cneg * invSqrtOnePlus t

lemma invSqrtOnePlus_anti {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    invSqrtOnePlus v ≤ invSqrtOnePlus u := by
  unfold invSqrtOnePlus
  have hu_pos : 0 < Real.sqrt (1 + u) := Real.sqrt_pos.2 (by linarith)
  have hv_pos : 0 < Real.sqrt (1 + v) := Real.sqrt_pos.2 (by linarith)
  have hsqrt : Real.sqrt (1 + u) ≤ Real.sqrt (1 + v) :=
    Real.sqrt_le_sqrt (by linarith)
  exact (inv_le_inv₀ hv_pos hu_pos).2 hsqrt

lemma dist_le_two_mul_of_dist_le
    {X : ℝ} {p q : Plane} (hp : dist p 0 ≤ X) (hq : dist q 0 ≤ X) :
    dist p q ≤ 2 * X := by
  calc
    dist p q ≤ dist p 0 + dist 0 q := dist_triangle p 0 q
    _ = dist p 0 + dist q 0 := by rw [dist_comm 0 q]
    _ ≤ X + X := add_le_add hp hq
    _ = 2 * X := by ring

lemma sum_mem_eq_self_add_sum_erase {α : Type*} [DecidableEq α]
    (s : Finset α) {a : α} (ha : a ∈ s) (f : α → ℝ) :
    (∑ x ∈ s, f x) = f a + ∑ x ∈ s.erase a, f x := by
  rw [← Finset.insert_erase ha]
  simp

lemma sum_pair_split_diag_offdiag (P : Finset Plane) (F : Plane → Plane → ℝ) :
    (∑ p ∈ P, ∑ q ∈ P, F p q) =
      (∑ p ∈ P, F p p) + (∑ p ∈ P, ∑ q ∈ P.erase p, F p q) := by
  classical
  calc
    (∑ p ∈ P, ∑ q ∈ P, F p q)
        = ∑ p ∈ P, (F p p + ∑ q ∈ P.erase p, F p q) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact sum_mem_eq_self_add_sum_erase P hp (F p)
    _ = (∑ p ∈ P, F p p) + (∑ p ∈ P, ∑ q ∈ P.erase p, F p q) := by
      rw [Finset.sum_add_distrib]

lemma sum_mem_const (P : Finset Plane) (c : ℝ) :
    (∑ _p ∈ P, c) = (P.card : ℝ) * c := by
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

lemma sum_mem_erase_const_of_mem (P : Finset Plane) {p : Plane} (hp : p ∈ P) (c : ℝ) :
    (∑ _q ∈ P.erase p, c) = ((P.card : ℝ) - 1) * c := by
  rw [Finset.sum_const]
  simp [nsmul_eq_mul, Finset.cast_card_erase_of_mem hp]

lemma robustFiniteSet_mono_delta {X δ η : ℝ} {P : Finset Plane}
    (hηδ : η ≤ δ) (hP : RobustFiniteSet X δ P) :
    RobustFiniteSet X η P := by
  refine ⟨hP.1, ?_⟩
  intro p hp q hq hpq
  exact away_mono hηδ (hP.2 p hp q hq hpq)

lemma diag_sum_bound (pkg : DelsarteKernelPackage) {s : ℝ}
    (hs : 0 < s) (hss0 : s < pkg.s0) (P : Finset Plane) :
    (∑ p ∈ P, pkg.K s (dist p p)) ≤
      (P.card : ℝ) * pkg.Cdiag * (s ^ 2)⁻¹ := by
  have hdiag := pkg.diag_bound s hs hss0
  calc
    (∑ p ∈ P, pkg.K s (dist p p))
        = ∑ _p ∈ P, pkg.K s 0 := by simp
    _ ≤ ∑ _p ∈ P, pkg.Cdiag * (s ^ 2)⁻¹ := by
      refine Finset.sum_le_sum ?_
      intro p hp
      exact hdiag
    _ = (P.card : ℝ) * pkg.Cdiag * (s ^ 2)⁻¹ := by
      rw [sum_mem_const]
      ring

lemma offdiag_term_bound (pkg : DelsarteKernelPackage) {X δ s : ℝ}
    {P : Finset Plane} (hP : RobustFiniteSet X δ P) (hs : 0 < s)
    (hss0 : s < pkg.s0) (hAs : pkg.A * s ≤ δ)
    {p q : Plane} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    pkg.K s (dist p q) ≤ -pkg.cneg * invSqrtOnePlus (2 * X) := by
  have hawayδ : AwayFromIntegers δ (dist p q) := hP.2 p hp q hq hpq
  have hawayAs : AwayFromIntegers (pkg.A * s) (dist p q) :=
    away_mono hAs hawayδ
  have hdist_nonneg : 0 ≤ dist p q := dist_nonneg
  have hkernel :=
    pkg.offdiag_bound s (dist p q) hs hss0 hdist_nonneg hawayAs
  have hdist_le : dist p q ≤ 2 * X :=
    dist_le_two_mul_of_dist_le (hP.1 p hp) (hP.1 q hq)
  have hanti : invSqrtOnePlus (2 * X) ≤ invSqrtOnePlus (dist p q) :=
    invSqrtOnePlus_anti hdist_nonneg hdist_le
  have hmul :
      -pkg.cneg * invSqrtOnePlus (dist p q) ≤
        -pkg.cneg * invSqrtOnePlus (2 * X) := by
    exact mul_le_mul_of_nonpos_left hanti (by linarith [pkg.cneg_pos])
  exact hkernel.trans hmul

lemma offdiag_sum_bound (pkg : DelsarteKernelPackage) {X δ s : ℝ}
    {P : Finset Plane} (hP : RobustFiniteSet X δ P) (hs : 0 < s)
    (hss0 : s < pkg.s0) (hAs : pkg.A * s ≤ δ) :
    (∑ p ∈ P, ∑ q ∈ P.erase p, pkg.K s (dist p q)) ≤
      (P.card : ℝ) * ((P.card : ℝ) - 1) *
        (-pkg.cneg * invSqrtOnePlus (2 * X)) := by
  classical
  calc
    (∑ p ∈ P, ∑ q ∈ P.erase p, pkg.K s (dist p q))
        ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, -pkg.cneg * invSqrtOnePlus (2 * X) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          refine Finset.sum_le_sum ?_
          intro q hqerase
          have hq_data := Finset.mem_erase.mp hqerase
          exact offdiag_term_bound pkg hP hs hss0 hAs hp hq_data.2 hq_data.1.symm
    _ = ∑ p ∈ P, ((P.card : ℝ) - 1) *
          (-pkg.cneg * invSqrtOnePlus (2 * X)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact sum_mem_erase_const_of_mem P hp (-pkg.cneg * invSqrtOnePlus (2 * X))
    _ = (P.card : ℝ) * ((P.card : ℝ) - 1) *
          (-pkg.cneg * invSqrtOnePlus (2 * X)) := by
          rw [sum_mem_const]
          ring

lemma invSqrtOnePlus_two_mul_pos {X : ℝ} (hX : 1 ≤ X) :
    0 < invSqrtOnePlus (2 * X) := by
  apply invSqrtOnePlus_pos
  linarith

lemma sqrt_one_add_two_mul_le_two_mul_sqrt {X : ℝ} (hX : 1 ≤ X) :
    Real.sqrt (1 + 2 * X) ≤ 2 * Real.sqrt X := by
  have h_nonneg : 0 ≤ X := le_trans (by norm_num) hX
  have hsq : 1 + 2 * X ≤ 4 * X := by linarith
  calc
    Real.sqrt (1 + 2 * X) ≤ Real.sqrt (4 * X) :=
      Real.sqrt_le_sqrt hsq
    _ = 2 * Real.sqrt X := by
      rw [show (4 : ℝ) * X = (2 : ℝ) ^ 2 * X by ring]
      rw [Real.sqrt_mul (sq_nonneg (2 : ℝ)), Real.sqrt_sq (by norm_num)]

lemma inv_invSqrtOnePlus_le_two_sqrt {X : ℝ} (hX : 1 ≤ X) :
    (invSqrtOnePlus (2 * X))⁻¹ ≤ 2 * Real.sqrt X := by
  unfold invSqrtOnePlus
  rw [inv_inv]
  exact sqrt_one_add_two_mul_le_two_mul_sqrt hX

lemma quadratic_card_bound {n α β : ℝ} (hn2 : 2 ≤ n) (hβ : 0 < β)
    (hquad : 0 ≤ n * α + n * (n - 1) * (-β)) :
    n ≤ 2 * α / β := by
  have hnpos : 0 < n := by linarith
  have hle_raw : n * ((n - 1) * β) ≤ n * α := by
    nlinarith
  have hle : (n - 1) * β ≤ α := by
    exact le_of_mul_le_mul_left hle_raw hnpos
  have hn_le_two_nm1 : n ≤ 2 * (n - 1) := by linarith
  have hβ_nonneg : 0 ≤ β := hβ.le
  have hnβ_le : n * β ≤ 2 * α := by
    calc
      n * β ≤ (2 * (n - 1)) * β :=
        mul_le_mul_of_nonneg_right hn_le_two_nm1 hβ_nonneg
      _ = 2 * ((n - 1) * β) := by ring
      _ ≤ 2 * α := by linarith
  exact (le_div_iff₀ hβ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hnβ_le)

lemma robust_finite_bound_at_scale (pkg : DelsarteKernelPackage)
    {X δ s : ℝ} {P : Finset Plane}
    (hX : 1 ≤ X) (hs : 0 < s) (hss0 : s < pkg.s0)
    (hAs : pkg.A * s ≤ δ) (hP : RobustFiniteSet X δ P) :
    (P.card : ℝ) ≤
      max 1
        (2 * (pkg.Cdiag * (s ^ 2)⁻¹) /
          (pkg.cneg * invSqrtOnePlus (2 * X))) := by
  classical
  by_cases hsmall : P.card ≤ 1
  · have hcast : (P.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
    exact hcast.trans (le_max_left _ _)
  · have hcard2_nat : 2 ≤ P.card :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hsmall)
    have hn2 : 2 ≤ (P.card : ℝ) := by exact_mod_cast hcard2_nat
    let n : ℝ := P.card
    let α : ℝ := pkg.Cdiag * (s ^ 2)⁻¹
    let β : ℝ := pkg.cneg * invSqrtOnePlus (2 * X)
    have hβpos : 0 < β := by
      exact mul_pos pkg.cneg_pos (invSqrtOnePlus_two_mul_pos hX)
    have hpos := pkg.pos_def s hs hss0 P
    have hsplit :
        (∑ p ∈ P, ∑ q ∈ P, pkg.K s (dist p q)) =
          (∑ p ∈ P, pkg.K s (dist p p)) +
            (∑ p ∈ P, ∑ q ∈ P.erase p, pkg.K s (dist p q)) :=
      sum_pair_split_diag_offdiag P (fun p q => pkg.K s (dist p q))
    have htotal_le :
        (∑ p ∈ P, ∑ q ∈ P, pkg.K s (dist p q)) ≤
          n * α + n * (n - 1) * (-β) := by
      rw [hsplit]
      have hdiag := diag_sum_bound pkg hs hss0 P
      have hoff := offdiag_sum_bound pkg hP hs hss0 hAs
      have hadd := add_le_add hdiag hoff
      simpa [n, α, β, mul_assoc] using hadd
    have hquad : 0 ≤ n * α + n * (n - 1) * (-β) :=
      hpos.trans htotal_le
    have hbound : n ≤ 2 * α / β :=
      quadratic_card_bound hn2 hβpos hquad
    exact hbound.trans (le_max_right _ _)

/--
Finite robust estimate from an abstract positive-definite kernel with diagonal
and off-diagonal bounds.  This is Milestone 1 in the implementation plan.
-/
theorem robust_finite_bound_from_kernel
    (pkg : DelsarteKernelPackage) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X := by
  classical
  let B : ℝ := pkg.A + pkg.s0⁻¹ + 1
  let C : ℝ := 1 + 4 * pkg.Cdiag * B ^ 2 / pkg.cneg
  have hs0_inv_pos : 0 < pkg.s0⁻¹ := inv_pos.mpr pkg.s0_pos
  have hBpos : 0 < B := by
    unfold B
    linarith [pkg.A_pos, hs0_inv_pos]
  have hB_A : pkg.A ≤ B := by
    unfold B
    linarith [hs0_inv_pos, pkg.A_pos]
  have hB_s0_inv : pkg.s0⁻¹ ≤ B := by
    unfold B
    linarith [pkg.A_pos]
  have hBsq_nonneg : 0 ≤ B ^ 2 := sq_nonneg B
  have hBsq_pos : 0 < B ^ 2 := sq_pos_of_ne_zero hBpos.ne'
  have hbigCoeff_nonneg : 0 ≤ 4 * pkg.Cdiag * B ^ 2 / pkg.cneg := by
    have hnum1 : 0 ≤ (4 : ℝ) * pkg.Cdiag :=
      mul_nonneg (by norm_num) pkg.Cdiag_pos.le
    have hnum : 0 ≤ (4 : ℝ) * pkg.Cdiag * B ^ 2 :=
      mul_nonneg hnum1 hBsq_nonneg
    exact div_nonneg hnum pkg.cneg_pos.le
  have hCpos : 0 < C := by
    unfold C
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro X δ P hX hδpos hδsmall hP
  let s : ℝ := δ / B
  have hspos : 0 < s := by
    unfold s
    positivity
  have hAs : pkg.A * s ≤ δ := by
    have hAdiv : pkg.A / B ≤ 1 := by
      exact (div_le_iff₀ hBpos).2 (by simpa using hB_A)
    calc
      pkg.A * s = δ * (pkg.A / B) := by
        unfold s
        field_simp [hBpos.ne']
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hAdiv hδpos.le
      _ = δ := by ring
  have hss0 : s < pkg.s0 := by
    have hs0B_ge_one : 1 ≤ pkg.s0 * B := by
      have hmul := mul_le_mul_of_nonneg_left hB_s0_inv pkg.s0_pos.le
      have hs0_mul_inv : pkg.s0 * pkg.s0⁻¹ = 1 := by
        exact mul_inv_cancel₀ pkg.s0_pos.ne'
      linarith
    have hδ_lt_s0B : δ < pkg.s0 * B := by
      linarith
    unfold s
    exact (div_lt_iff₀ hBpos).2 hδ_lt_s0B
  have hscale := robust_finite_bound_at_scale pkg hX hspos hss0 hAs hP
  have hδ_lt_one : δ < 1 := by linarith
  have hδ_sq_pos : 0 < δ ^ 2 := sq_pos_of_ne_zero hδpos.ne'
  have hδ_sq_le_one : δ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg δ, hδ_lt_one.le, hδpos.le]
  have hδinv_ge_one : 1 ≤ (δ ^ 2)⁻¹ :=
    (one_le_inv₀ hδ_sq_pos).2 hδ_sq_le_one
  have hsqrt_ge_one : 1 ≤ Real.sqrt X := by
    simpa using Real.sqrt_le_sqrt hX
  have hC_ge_one : 1 ≤ C := by
    unfold C
    linarith
  have hone :
      (1 : ℝ) ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X := by
    have hCnonneg : 0 ≤ C := le_trans zero_le_one hC_ge_one
    have hDnonneg : 0 ≤ (δ ^ 2)⁻¹ := by positivity
    have hstep1 : C ≤ C * (δ ^ 2)⁻¹ := by
      calc
        C = C * 1 := by ring
        _ ≤ C * (δ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hδinv_ge_one hCnonneg
    have hstep2 : C * (δ ^ 2)⁻¹ ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X := by
      calc
        C * (δ ^ 2)⁻¹ = C * (δ ^ 2)⁻¹ * 1 := by ring
        _ ≤ C * (δ ^ 2)⁻¹ * Real.sqrt X :=
          mul_le_mul_of_nonneg_left hsqrt_ge_one (mul_nonneg hCnonneg hDnonneg)
    exact hC_ge_one.trans (hstep1.trans hstep2)
  have hs_sq_inv : (s ^ 2)⁻¹ = B ^ 2 * (δ ^ 2)⁻¹ := by
    unfold s
    field_simp [hBpos.ne', hδpos.ne']
  have hinv_pos : 0 < invSqrtOnePlus (2 * X) :=
    invSqrtOnePlus_two_mul_pos hX
  have hterm_expr :
      2 * (pkg.Cdiag * (s ^ 2)⁻¹) /
          (pkg.cneg * invSqrtOnePlus (2 * X)) =
        (2 * pkg.Cdiag * B ^ 2 / pkg.cneg) *
          (δ ^ 2)⁻¹ * (invSqrtOnePlus (2 * X))⁻¹ := by
    rw [hs_sq_inv]
    field_simp [pkg.cneg_pos.ne', hinv_pos.ne']
  have hterm :
      2 * (pkg.Cdiag * (s ^ 2)⁻¹) /
          (pkg.cneg * invSqrtOnePlus (2 * X)) ≤
        C * (δ ^ 2)⁻¹ * Real.sqrt X := by
    rw [hterm_expr]
    have hcoeff_nonneg : 0 ≤ (2 * pkg.Cdiag * B ^ 2 / pkg.cneg) * (δ ^ 2)⁻¹ := by
      have hleft : 0 ≤ 2 * pkg.Cdiag * B ^ 2 / pkg.cneg := by
        have hnum1 : 0 ≤ (2 : ℝ) * pkg.Cdiag :=
          mul_nonneg (by norm_num) pkg.Cdiag_pos.le
        have hnum : 0 ≤ (2 : ℝ) * pkg.Cdiag * B ^ 2 :=
          mul_nonneg hnum1 hBsq_nonneg
        exact div_nonneg hnum pkg.cneg_pos.le
      have hright : 0 ≤ (δ ^ 2)⁻¹ := by
        positivity
      exact mul_nonneg hleft hright
    have hfirst :
        (2 * pkg.Cdiag * B ^ 2 / pkg.cneg) *
            (δ ^ 2)⁻¹ * (invSqrtOnePlus (2 * X))⁻¹ ≤
          (2 * pkg.Cdiag * B ^ 2 / pkg.cneg) *
            (δ ^ 2)⁻¹ * (2 * Real.sqrt X) := by
      exact mul_le_mul_of_nonneg_left
        (inv_invSqrtOnePlus_le_two_sqrt hX) hcoeff_nonneg
    have hcoeff_le : 4 * pkg.Cdiag * B ^ 2 / pkg.cneg ≤ C := by
      unfold C
      linarith
    have htail_nonneg : 0 ≤ (δ ^ 2)⁻¹ * Real.sqrt X := by
      positivity
    have hsecond :
        (2 * pkg.Cdiag * B ^ 2 / pkg.cneg) *
            (δ ^ 2)⁻¹ * (2 * Real.sqrt X) ≤
          C * (δ ^ 2)⁻¹ * Real.sqrt X := by
      calc
        (2 * pkg.Cdiag * B ^ 2 / pkg.cneg) *
            (δ ^ 2)⁻¹ * (2 * Real.sqrt X)
            = (4 * pkg.Cdiag * B ^ 2 / pkg.cneg) *
                ((δ ^ 2)⁻¹ * Real.sqrt X) := by ring
        _ ≤ C * ((δ ^ 2)⁻¹ * Real.sqrt X) :=
          mul_le_mul_of_nonneg_right hcoeff_le htail_nonneg
        _ = C * (δ ^ 2)⁻¹ * Real.sqrt X := by ring
    exact hfirst.trans hsecond
  exact hscale.trans (max_le hone hterm)

end Erdos953Formalization
