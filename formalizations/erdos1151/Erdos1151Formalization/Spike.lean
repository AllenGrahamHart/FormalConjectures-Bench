import Erdos1151Formalization.Basic
import Mathlib.Data.Real.Sign
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Arithmetic spike infrastructure for Erdős Problem 1151

This file starts the concrete block-spike side of the proof.  It contains the
primitive row index set, the signed primitive mass normalization, and the real
Möbius divisor sum used in the finite cancellation argument.
-/

noncomputable section

open scoped BigOperators Topology

namespace Erdos1151Formalization

/-- A natural number which is a power of two. -/
def IsPowTwo (n : ℕ) : Prop :=
  ∃ r : ℕ, n = 2 ^ r

/-- Primitive numerator indices for order `d`. -/
def primIdx (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun k => Nat.Coprime (2 * k + 1) d

lemma mem_primIdx_iff {d k : ℕ} :
    k ∈ primIdx d ↔ k < d ∧ Nat.Coprime (2 * k + 1) d := by
  simp [primIdx]

/-- If an order-`d` primitive node is viewed in row `d * s`, this is its row index. -/
def occurrenceIndex (s k : ℕ) : ℕ :=
  (((2 * k + 1) * s - 1) / 2)

lemma occurrenceIndex_eq_of_odd_aux (k t : ℕ) :
    occurrenceIndex (2 * t + 1) k = 2 * k * t + k + t := by
  unfold occurrenceIndex
  have hnum :
      (2 * k + 1) * (2 * t + 1) - 1 =
        2 * (2 * k * t + k + t) := by
    have hle : 1 ≤ (2 * k + 1) * (2 * t + 1) := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    rw [Nat.sub_eq_iff_eq_add hle]
    ring
  rw [hnum]
  exact Nat.mul_div_right (2 * k * t + k + t) (by norm_num : 0 < 2)

lemma two_mul_occurrenceIndex_add_one {s k : ℕ} (hsodd : Odd s) :
    2 * occurrenceIndex s k + 1 = (2 * k + 1) * s := by
  rcases hsodd with ⟨t, ht⟩
  rw [ht, occurrenceIndex_eq_of_odd_aux]
  ring

lemma occurrenceIndex_lt_mul {d s k : ℕ}
    (hk : k < d) (hsodd : Odd s) :
    occurrenceIndex s k < d * s := by
  have hspos : 0 < s := hsodd.pos
  have htwo : 2 * occurrenceIndex s k + 1 = (2 * k + 1) * s :=
    two_mul_occurrenceIndex_add_one hsodd
  have hlin : 2 * k + 1 < 2 * d := by
    omega
  have hmul : (2 * k + 1) * s < (2 * d) * s :=
    Nat.mul_lt_mul_of_pos_right hlin hspos
  have htarget : 2 * occurrenceIndex s k + 1 < 2 * (d * s) := by
    rw [htwo]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  omega

lemma occurrenceIndex_mem_range_mul {d s k : ℕ}
    (hk : k < d) (hsodd : Odd s) :
    occurrenceIndex s k ∈ Finset.range (d * s) := by
  exact Finset.mem_range.mpr (occurrenceIndex_lt_mul hk hsodd)

lemma thetaNode_mul_occurrenceIndex {d s k : ℕ}
    (hk : k < d) (hsodd : Odd s) :
    thetaNode (d * s) (occurrenceIndex s k) = thetaNode d k := by
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hspos : 0 < s := hsodd.pos
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdpos)
  have hsne : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hspos)
  have hdsne : ((d * s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hdpos) (Nat.ne_of_gt hspos))
  have htwo_real :
      2 * (occurrenceIndex s k : ℝ) + 1 =
        (((2 * k + 1) * s : ℕ) : ℝ) := by
    exact_mod_cast (two_mul_occurrenceIndex_add_one (s := s) (k := k) hsodd)
  unfold thetaNode
  rw [htwo_real]
  field_simp [hdne, hsne, hdsne]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

lemma exists_row_index_for_odd_multiple {d s k : ℕ}
    (hk : k < d) (hsodd : Odd s) :
    ∃ l ∈ Finset.range (d * s), thetaNode (d * s) l = thetaNode d k :=
  ⟨occurrenceIndex s k, occurrenceIndex_mem_range_mul hk hsodd,
    thetaNode_mul_occurrenceIndex hk hsodd⟩

lemma thetaNode_eq_cross {a b k l : ℕ}
    (hapos : 0 < a) (hbpos : 0 < b)
    (hθ : thetaNode a k = thetaNode b l) :
    (2 * k + 1) * b = (2 * l + 1) * a := by
  have hane : (a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hapos)
  have hbne : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbpos)
  have hapos_real : 0 < (a : ℝ) := by
    exact_mod_cast hapos
  have hreal :
      (((2 * k + 1) * b : ℕ) : ℝ) =
        (((2 * l + 1) * a : ℕ) : ℝ) := by
    unfold thetaNode at hθ
    have h := hθ
    field_simp [hane, hbne, Real.pi_ne_zero] at h
    norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
    nlinarith [h, hapos_real]
  exact_mod_cast hreal

lemma primitive_node_occurs_of_theta_eq {d k j l : ℕ}
    (hdpos : 0 < d) (hjpos : 0 < j)
    (hkcop : Nat.Coprime (2 * k + 1) d)
    (hθ : thetaNode j l = thetaNode d k) :
    d ∣ j ∧ Odd (j / d) := by
  have hcross := thetaNode_eq_cross hjpos hdpos hθ
  have hdvd : d ∣ j := by
    have hdiv : d ∣ (2 * k + 1) * j := by
      rw [← hcross]
      exact dvd_mul_left d (2 * l + 1)
    exact hkcop.symm.dvd_of_dvd_mul_left hdiv
  refine ⟨hdvd, ?_⟩
  rcases hdvd with ⟨q, hq⟩
  have hqeq : j / d = q := by
    rw [hq, Nat.mul_div_right q hdpos]
  rw [hqeq]
  have hcross2 : (2 * l + 1) * d = (2 * k + 1) * (d * q) := by
    simpa [hq] using hcross
  have hcancel : 2 * l + 1 = (2 * k + 1) * q := by
    have hright : (2 * k + 1) * (d * q) = d * ((2 * k + 1) * q) := by
      ring
    rw [hright] at hcross2
    have hleft : (2 * l + 1) * d = d * (2 * l + 1) := by
      ring
    rw [hleft] at hcross2
    exact Nat.eq_of_mul_eq_mul_left hdpos hcross2
  have hodd_left : Odd (2 * l + 1) := odd_two_mul_add_one l
  rw [hcancel] at hodd_left
  rcases Nat.even_or_odd q with hqeven | hqodd
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hodd_left) (hqeven.mul_left (2 * k + 1))
  · exact hqodd

lemma thetaNode_base_mul_eq_cross {n s t k l : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (htpos : 0 < t)
    (hθ : thetaNode (n * s) k = thetaNode (n * t) l) :
    (2 * k + 1) * t = (2 * l + 1) * s := by
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hnpos_real : 0 < (n : ℝ) := by
    exact_mod_cast hnpos
  have hsne : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hspos)
  have htne : (t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt htpos)
  have hreal :
      (((2 * k + 1) * t : ℕ) : ℝ) =
        (((2 * l + 1) * s : ℕ) : ℝ) := by
    unfold thetaNode at hθ
    have h := hθ
    field_simp [hnne, hsne, htne, Real.pi_ne_zero] at h
    norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
    nlinarith [h, hnpos_real]
  exact_mod_cast hreal

lemma primitive_order_unique_of_theta_eq {n s t k l : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (htpos : 0 < t)
    (hkcop : Nat.Coprime (2 * k + 1) (n * s))
    (hlcop : Nat.Coprime (2 * l + 1) (n * t))
    (hθ : thetaNode (n * s) k = thetaNode (n * t) l) :
    s = t := by
  have hcross := thetaNode_base_mul_eq_cross hnpos hspos htpos hθ
  have hs_dvd_ns : s ∣ n * s :=
    ⟨n, by rw [mul_comm]⟩
  have ht_dvd_nt : t ∣ n * t :=
    ⟨n, by rw [mul_comm]⟩
  have hcop_s : s.Coprime (2 * k + 1) :=
    (Nat.Coprime.coprime_dvd_right hs_dvd_ns hkcop).symm
  have hcop_t : t.Coprime (2 * l + 1) :=
    (Nat.Coprime.coprime_dvd_right ht_dvd_nt hlcop).symm
  have hs_dvd_t : s ∣ t := by
    have hdiv : s ∣ (2 * k + 1) * t := by
      rw [hcross]
      exact dvd_mul_left s (2 * l + 1)
    exact hcop_s.dvd_of_dvd_mul_left hdiv
  have ht_dvd_s : t ∣ s := by
    have hdiv : t ∣ (2 * l + 1) * s := by
      rw [← hcross]
      exact dvd_mul_left t (2 * k + 1)
    exact hcop_t.dvd_of_dvd_mul_left hdiv
  exact Nat.dvd_antisymm hs_dvd_t ht_dvd_s

lemma primitive_node_unique_of_theta_eq {n s t k l : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (htpos : 0 < t)
    (hk : k ∈ primIdx (n * s)) (hl : l ∈ primIdx (n * t))
    (hθ : thetaNode (n * s) k = thetaNode (n * t) l) :
    s = t ∧ k = l := by
  have hkcop : Nat.Coprime (2 * k + 1) (n * s) :=
    (mem_primIdx_iff.mp hk).2
  have hlcop : Nat.Coprime (2 * l + 1) (n * t) :=
    (mem_primIdx_iff.mp hl).2
  have hst :=
    primitive_order_unique_of_theta_eq hnpos hspos htpos hkcop hlcop hθ
  subst t
  have hcross := thetaNode_base_mul_eq_cross hnpos hspos hspos hθ
  have hnum : 2 * k + 1 = 2 * l + 1 :=
    Nat.eq_of_mul_eq_mul_right hspos hcross
  have hkl : k = l := by
    omega
  exact ⟨rfl, hkl⟩

/-- Total variation of the primitive part of row `d`. -/
def Vprim (theta0 : ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ primIdx d, |lambdaWeight theta0 d k|

lemma Vprim_nonneg (theta0 : ℝ) (d : ℕ) :
    0 ≤ Vprim theta0 d := by
  unfold Vprim
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Odd integers in `[1, R]`. -/
def oddUpTo (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter Odd

lemma mem_oddUpTo_iff {R s : ℕ} :
    s ∈ oddUpTo R ↔ 1 ≤ s ∧ s ≤ R ∧ Odd s := by
  simp [oddUpTo, and_assoc, and_comm]

/-- The quadratic character appearing in the row-occurrence sign. -/
def chi (s : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((s - 1) / 2)

lemma chi_one : chi 1 = 1 := by
  simp [chi]

lemma chi_sq_eq_one (s : ℕ) :
    chi s ^ 2 = 1 := by
  unfold chi
  rw [← pow_mul]
  have hEven : Even (((s - 1) / 2) * 2) :=
    ⟨(s - 1) / 2, by ring⟩
  exact hEven.neg_one_pow

lemma abs_chi (s : ℕ) :
    |chi s| = 1 := by
  unfold chi
  rw [abs_pow, abs_neg, abs_one, one_pow]

lemma odd_mul_sub_one_div_two (a b : ℕ) :
    (((2 * a + 1) * (2 * b + 1) - 1) / 2) = 2 * a * b + a + b := by
  have hnum :
      (2 * a + 1) * (2 * b + 1) - 1 =
        2 * (2 * a * b + a + b) := by
    have hle : 1 ≤ (2 * a + 1) * (2 * b + 1) := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    rw [Nat.sub_eq_iff_eq_add hle]
    ring
  rw [hnum]
  exact Nat.mul_div_right (2 * a * b + a + b) (by norm_num : 0 < 2)

lemma chi_mul {s t : ℕ} (hs : Odd s) (ht : Odd t) :
    chi (s * t) = chi s * chi t := by
  rcases hs with ⟨a, rfl⟩
  rcases ht with ⟨b, rfl⟩
  simp [chi, odd_mul_sub_one_div_two]
  rw [pow_add, pow_add]
  have hEven : Even (2 * a * b) :=
    ⟨a * b, by ring⟩
  rw [hEven.neg_one_pow]
  ring

lemma odd_of_mul_right {a b : ℕ} (h : Odd (a * b)) :
    Odd a := by
  rcases Nat.even_or_odd a with ha | ha
  · exfalso
    exact (Nat.not_even_iff_odd.mpr h) (ha.mul_right b)
  · exact ha

lemma odd_of_mul_left {a b : ℕ} (h : Odd (a * b)) :
    Odd b := by
  rcases Nat.even_or_odd b with hb | hb
  · exfalso
    exact (Nat.not_even_iff_odd.mpr h) (hb.mul_left a)
  · exact hb

lemma odd_of_dvd_odd {s u : ℕ} (hu : Odd u) (hdiv : s ∣ u) :
    Odd s := by
  rcases hdiv with ⟨t, rfl⟩
  exact odd_of_mul_right hu

lemma odd_div_of_dvd {s u : ℕ} (hu : Odd u) (hdiv : s ∣ u) :
    Odd (u / s) := by
  rcases hdiv with ⟨t, rfl⟩
  have hsodd : Odd s := odd_of_mul_right hu
  rw [Nat.mul_div_right t hsodd.pos]
  exact odd_of_mul_left hu

lemma chi_div_mul_eq_chi {s u : ℕ} (hu : Odd u) (hdiv : s ∣ u) :
    chi (u / s) * chi s = chi u := by
  have hsodd : Odd s := odd_of_dvd_odd hu hdiv
  have hqodd : Odd (u / s) := odd_div_of_dvd hu hdiv
  have h := chi_mul hqodd hsodd
  have hmul : (u / s) * s = u := Nat.div_mul_cancel hdiv
  rw [hmul] at h
  exact h.symm

lemma neg_one_pow_occurrenceIndex {s k : ℕ} (hsodd : Odd s) :
    (-1 : ℝ) ^ occurrenceIndex s k = chi s * (-1 : ℝ) ^ k := by
  rcases hsodd with ⟨t, ht⟩
  rw [ht, occurrenceIndex_eq_of_odd_aux]
  simp [chi]
  rw [pow_add, pow_add]
  have hEven : Even (2 * k * t) :=
    ⟨k * t, by ring⟩
  rw [hEven.neg_one_pow]
  ring

/-- Row occurrence multiplier between order `d` and row `n`. -/
def gamma (theta0 : ℝ) (n d : ℕ) : ℝ :=
  (d : ℝ) / (n : ℝ) * chi (n / d) *
    Real.cos ((n : ℝ) * theta0) / Real.cos ((d : ℝ) * theta0)

lemma gamma_self {theta0 : ℝ} {d : ℕ}
    (hdpos : 0 < d)
    (hcos : Real.cos ((d : ℝ) * theta0) ≠ 0) :
    gamma theta0 d d = 1 := by
  unfold gamma
  have hdne_nat : d ≠ 0 := Nat.ne_of_gt hdpos
  have hdne_real : (d : ℝ) ≠ 0 := by
    exact_mod_cast hdne_nat
  simp [Nat.div_self hdpos, chi_one, hcos, hdne_real]

lemma lambdaWeight_occurrenceIndex_eq_gamma_mul
    {theta0 : ℝ} {d s k : ℕ}
    (hk : k < d) (hsodd : Odd s)
    (hcosd : Real.cos ((d : ℝ) * theta0) ≠ 0) :
    lambdaWeight theta0 (d * s) (occurrenceIndex s k) =
      gamma theta0 (d * s) d * lambdaWeight theta0 d k := by
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hspos : 0 < s := hsodd.pos
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdpos)
  have hsne : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hspos)
  have hdsne : ((d * s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hdpos) (Nat.ne_of_gt hspos))
  have hdiv : (d * s) / d = s :=
    Nat.mul_div_right s hdpos
  have htheta :=
    thetaNode_mul_occurrenceIndex (d := d) (s := s) (k := k) hk hsodd
  have hsign :=
    neg_one_pow_occurrenceIndex (s := s) (k := k) hsodd
  have hcosd_comm :
      Real.cos (theta0 * (d : ℝ)) = Real.cos ((d : ℝ) * theta0) := by
    congr 1
    ring
  have hcosd_ne_comm : Real.cos (theta0 * (d : ℝ)) ≠ 0 := by
    rw [hcosd_comm]
    exact hcosd
  unfold lambdaWeight gamma
  rw [hdiv, htheta, hsign]
  field_simp [hdne, hsne, hdsne, hcosd, hcosd_ne_comm]

lemma lambdaWeight_occurrenceIndex_eq_gamma_mul_of_not_isNodeRow
    {theta0 : ℝ} {d s k : ℕ}
    (hk : k < d) (hsodd : Odd s)
    (hnotd : ¬ IsNodeRow theta0 d) :
    lambdaWeight theta0 (d * s) (occurrenceIndex s k) =
      gamma theta0 (d * s) d * lambdaWeight theta0 d k := by
  exact lambdaWeight_occurrenceIndex_eq_gamma_mul hk hsodd hnotd

/-- The Möbius function, coerced to real values. -/
def muR (s : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) s : ℤ) : ℝ)

lemma muR_one : muR 1 = 1 := by
  simp [muR]

lemma abs_muR_le_one (s : ℕ) :
    |muR s| ≤ 1 := by
  unfold muR
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := s))

/-- Real-valued Möbius divisor sum. -/
lemma sum_muR_divisors_eq_ite {u : ℕ} (_hu : 0 < u) :
    (∑ s ∈ Nat.divisors u, muR s) = if u = 1 then 1 else 0 := by
  have h :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) u =
        (1 : ArithmeticFunction ℝ) u := by
    rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  simpa [muR, ArithmeticFunction.intCoe_apply] using h

lemma sum_muR_divisors_one :
    (∑ s ∈ Nat.divisors 1, muR s) = 1 := by
  simpa using sum_muR_divisors_eq_ite (u := 1) (by norm_num)

lemma sum_muR_divisors_eq_zero_of_ne_one {u : ℕ}
    (hu : 0 < u) (hu_ne : u ≠ 1) :
    (∑ s ∈ Nat.divisors u, muR s) = 0 := by
  simpa [hu_ne] using sum_muR_divisors_eq_ite (u := u) hu

/-- Algebraic coefficient assigned to primitive order `n * s`. -/
def spikeCoeff (theta0 : ℝ) (n s : ℕ) : ℝ :=
  muR s * chi s * Real.cos (((n * s : ℕ) : ℝ) * theta0) /
    ((s : ℝ) * Real.cos ((n : ℝ) * theta0))

lemma spikeCoeff_one {theta0 : ℝ} {n : ℕ}
    (hcos : Real.cos ((n : ℝ) * theta0) ≠ 0) :
    spikeCoeff theta0 n 1 = 1 := by
  unfold spikeCoeff
  simp [muR_one, chi_one, hcos]

lemma gamma_mul_spikeCoeff_eq_prefactor_mul_muR
    {theta0 : ℝ} {n u s : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hdiv : s ∣ u)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s =
      (chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
          ((u : ℝ) * Real.cos ((n : ℝ) * theta0))) * muR s := by
  have hsodd : Odd s := odd_of_dvd_odd huodd hdiv
  have hupos : 0 < u := huodd.pos
  have hspos : 0 < s := hsodd.pos
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hunne : ((n * u : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hnpos) (Nat.ne_of_gt hupos))
  have hnsne : ((n * s : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hnpos) (Nat.ne_of_gt hspos))
  have hsne : (s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hspos)
  have hune : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hupos)
  have hquot : (n * u) / (n * s) = u / s := by
    exact Nat.mul_div_mul_left u s hnpos
  have hchi : chi (u / s) * chi s = chi u :=
    chi_div_mul_eq_chi huodd hdiv
  have hcosn_comm :
      Real.cos (theta0 * (n : ℝ)) = Real.cos ((n : ℝ) * theta0) := by
    congr 1
    ring
  have hcosn_ne_comm : Real.cos (theta0 * (n : ℝ)) ≠ 0 := by
    rw [hcosn_comm]
    exact hcosn
  unfold gamma spikeCoeff
  rw [hquot]
  field_simp [hnne, hunne, hnsne, hsne, hune, hcosn, hcosns, hcosn_ne_comm]
  norm_num [Nat.cast_mul]
  rw [← hchi]
  ring

lemma sum_divisors_gamma_mul_spikeCoeff
    {theta0 : ℝ} {n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    (∑ s ∈ Nat.divisors u,
      gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s) =
      (chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
          ((u : ℝ) * Real.cos ((n : ℝ) * theta0))) *
        (if u = 1 then 1 else 0) := by
  let P : ℝ :=
    chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
      ((u : ℝ) * Real.cos ((n : ℝ) * theta0))
  have hsum_eq :
      (∑ s ∈ Nat.divisors u,
        gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s) =
        ∑ s ∈ Nat.divisors u, P * muR s := by
    apply Finset.sum_congr rfl
    intro s hs
    have hdiv : s ∣ u := (Nat.mem_divisors.mp hs).1
    exact gamma_mul_spikeCoeff_eq_prefactor_mul_muR
      (theta0 := theta0) (n := n) (u := u) (s := s)
      hnpos huodd hdiv hcosn (hcosns s hdiv)
  rw [hsum_eq]
  rw [← Finset.mul_sum]
  rw [sum_muR_divisors_eq_ite (u := u) huodd.pos]

lemma sum_divisors_gamma_mul_spikeCoeff_eq_zero_of_ne_one
    {theta0 : ℝ} {n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    (∑ s ∈ Nat.divisors u,
      gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s) = 0 := by
  simpa [hu_ne] using
    sum_divisors_gamma_mul_spikeCoeff
      (theta0 := theta0) (n := n) (u := u)
      hnpos huodd hcosn hcosns

lemma sum_divisors_gamma_mul_spikeCoeff_eq_one
    {theta0 : ℝ} {n : ℕ}
    (hnpos : 0 < n)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0) :
    (∑ s ∈ Nat.divisors 1,
      gamma theta0 (n * 1) (n * s) * spikeCoeff theta0 n s) = 1 := by
  have hcosns : ∀ s : ℕ, s ∣ 1 →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0 := by
    intro s hs
    have hs1 : s = 1 := Nat.dvd_one.mp hs
    simpa [hs1] using hcosn
  have h :=
    sum_divisors_gamma_mul_spikeCoeff
      (theta0 := theta0) (n := n) (u := 1)
      hnpos (by norm_num : Odd 1) hcosn hcosns
  simpa [chi_one, hcosn] using h

lemma sum_divisors_gamma_mul_spikeCoeff_eq_ite
    {theta0 : ℝ} {n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    (∑ s ∈ Nat.divisors u,
      gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s) =
        if u = 1 then 1 else 0 := by
  by_cases hu1 : u = 1
  · subst u
    simpa using sum_divisors_gamma_mul_spikeCoeff_eq_one
      (theta0 := theta0) (n := n) hnpos hcosn
  · simpa [hu1] using
      sum_divisors_gamma_mul_spikeCoeff_eq_zero_of_ne_one
        (theta0 := theta0) (n := n) (u := u)
        hnpos huodd hu1 hcosn hcosns

lemma real_mul_sign_eq_abs (x : ℝ) :
    x * Real.sign x = |x| := by
  by_cases hneg : x < 0
  · rw [Real.sign_of_neg hneg, mul_neg, mul_one]
    exact (abs_of_neg hneg).symm
  · by_cases hpos : 0 < x
    · rw [Real.sign_of_pos hpos, mul_one]
      exact (abs_of_pos hpos).symm
    · have hx : x = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      simp [hx]

lemma real_sign_mul_eq_abs (x : ℝ) :
    Real.sign x * x = |x| := by
  rw [mul_comm]
  exact real_mul_sign_eq_abs x

/-- Indices `(s, k)` for primitive nodes of order `n * s`. -/
def spikeIdx (n R : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (oddUpTo R).sigma fun s => primIdx (n * s)

lemma mem_spikeIdx_iff {n R : ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ spikeIdx n R ↔ p.1 ∈ oddUpTo R ∧ p.2 ∈ primIdx (n * p.1) := by
  simp [spikeIdx]

/-- Value assigned to a primitive node in the finite algebraic spike. -/
def finiteSpikeValueAtPrimitive (theta0 : ℝ) (n s k : ℕ) : ℝ :=
  spikeCoeff theta0 n s / Vprim theta0 (n * s) *
    Real.sign (lambdaWeight theta0 (n * s) k)

/-- The finite algebraic spike as a raw function, supported on primitive nodes
of the orders `n * s` with odd `s ≤ R`. -/
def finiteSpikeRaw (theta0 : ℝ) (R n : ℕ) : ℝ → ℝ :=
  fun theta =>
    ∑ p ∈ spikeIdx n R,
      if theta = thetaNode (n * p.1) p.2 then
        finiteSpikeValueAtPrimitive theta0 n p.1 p.2
      else 0

lemma finiteSpikeRaw_at_primitive
    {theta0 : ℝ} {R n s k : ℕ}
    (hnpos : 0 < n)
    (hs : s ∈ oddUpTo R)
    (hk : k ∈ primIdx (n * s)) :
    finiteSpikeRaw theta0 R n (thetaNode (n * s) k) =
      finiteSpikeValueAtPrimitive theta0 n s k := by
  classical
  let p : Σ _ : ℕ, ℕ := ⟨s, k⟩
  have hp : p ∈ spikeIdx n R := by
    simpa [p, spikeIdx] using And.intro hs hk
  unfold finiteSpikeRaw
  rw [Finset.sum_eq_single p]
  · simp [p]
  · intro q hq hqne
    by_cases htheta : thetaNode (n * s) k = thetaNode (n * q.1) q.2
    · have hqmem := mem_spikeIdx_iff.mp hq
      have hqpos : 0 < q.1 := by
        have hodd : Odd q.1 := (mem_oddUpTo_iff.mp hqmem.1).2.2
        exact hodd.pos
      have huniq :=
        primitive_node_unique_of_theta_eq
          (n := n) (s := s) (t := q.1) (k := k) (l := q.2)
          hnpos (by exact (mem_oddUpTo_iff.mp hs).2.2.pos)
          hqpos hk hqmem.2 htheta
      have hqeq : q = p := by
        cases q with
        | mk qs qk =>
            dsimp [p] at huniq ⊢
            rcases huniq with ⟨hsq, hkq⟩
            subst qk
            subst qs
            rfl
      exact False.elim (hqne hqeq)
    · simp [htheta]
  · intro hpnot
    exact False.elim (hpnot hp)

lemma mul_divisor_base_eq {n u s : ℕ} (hdiv : s ∣ u) :
    (n * s) * (u / s) = n * u := by
  rw [mul_assoc, mul_comm s (u / s)]
  rw [Nat.div_mul_cancel hdiv]

lemma finiteSpikeRaw_at_divisor_occurrence
    {theta0 : ℝ} {R n u s k : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hdiv : s ∣ u)
    (hsR : s ∈ oddUpTo R) (hk : k ∈ primIdx (n * s)) :
    finiteSpikeRaw theta0 R n
        (thetaNode (n * u) (occurrenceIndex (u / s) k)) =
      finiteSpikeValueAtPrimitive theta0 n s k := by
  have hqodd : Odd (u / s) := odd_div_of_dvd huodd hdiv
  have hklt : k < n * s := (mem_primIdx_iff.mp hk).1
  have htheta :=
    thetaNode_mul_occurrenceIndex
      (d := n * s) (s := u / s) (k := k) hklt hqodd
  have hmul : (n * s) * (u / s) = n * u :=
    mul_divisor_base_eq (n := n) hdiv
  rw [← hmul]
  rw [htheta]
  exact finiteSpikeRaw_at_primitive hnpos hsR hk

lemma occurrenceIndex_mem_range_base_mul {n u s k : ℕ}
    (hk : k < n * s) (huodd : Odd u) (hdiv : s ∣ u) :
    occurrenceIndex (u / s) k ∈ Finset.range (n * u) := by
  have hqodd : Odd (u / s) := odd_div_of_dvd huodd hdiv
  have hmem :=
    occurrenceIndex_mem_range_mul (d := n * s) (s := u / s) (k := k) hk hqodd
  have hmul : (n * s) * (u / s) = n * u :=
    mul_divisor_base_eq (n := n) hdiv
  simpa [hmul] using hmem

lemma sum_row_single_support_of_dvd
    {theta0 : ℝ} {n u s k : ℕ} (huodd : Odd u)
    (hdiv : s ∣ u) (hk : k ∈ primIdx (n * s)) {a : ℝ} :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        (if thetaNode (n * u) l = thetaNode (n * s) k then a else 0)) =
      lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) * a := by
  classical
  have hklt : k < n * s := (mem_primIdx_iff.mp hk).1
  have hocc_mem : occurrenceIndex (u / s) k ∈ Finset.range (n * u) :=
    occurrenceIndex_mem_range_base_mul hklt huodd hdiv
  have hqodd : Odd (u / s) := odd_div_of_dvd huodd hdiv
  have htheta_occ : thetaNode (n * u) (occurrenceIndex (u / s) k) =
      thetaNode (n * s) k := by
    have htheta :=
      thetaNode_mul_occurrenceIndex
        (d := n * s) (s := u / s) (k := k) hklt hqodd
    have hmul : (n * s) * (u / s) = n * u :=
      mul_divisor_base_eq (n := n) hdiv
    simpa [hmul] using htheta
  rw [Finset.sum_eq_single (occurrenceIndex (u / s) k)]
  · simp [htheta_occ]
  · intro l hl hlne
    by_cases htheta : thetaNode (n * u) l = thetaNode (n * s) k
    · have hsame :
          thetaNode (n * u) l = thetaNode (n * u) (occurrenceIndex (u / s) k) := by
        rw [htheta, htheta_occ]
      have hinj : Set.InjOn (thetaNode (n * u)) (Finset.range (n * u)) :=
        (thetaNode_strictMonoOn (n * u)).injOn
      have hleq := hinj hl hocc_mem hsame
      exact False.elim (hlne hleq)
    · simp [htheta]
  · intro hnot
    exact False.elim (hnot hocc_mem)

lemma base_dvd_of_mul_dvd_mul {n s u : ℕ} (hnpos : 0 < n)
    (hdiv : n * s ∣ n * u) :
    s ∣ u := by
  rcases hdiv with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have h : n * u = n * (s * q) := by
    calc
      n * u = (n * s) * q := hq
      _ = n * (s * q) := by ring
  exact Nat.eq_of_mul_eq_mul_left hnpos h

lemma support_order_dvd_of_row_hit
    {n u s k l : ℕ} (hnpos : 0 < n) (huodd : Odd u) (hspos : 0 < s)
    (hk : k ∈ primIdx (n * s))
    (hθ : thetaNode (n * u) l = thetaNode (n * s) k) :
    s ∣ u := by
  have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
  have hjpos : 0 < n * u := Nat.mul_pos hnpos huodd.pos
  have hkcop : Nat.Coprime (2 * k + 1) (n * s) :=
    (mem_primIdx_iff.mp hk).2
  have hocc :=
    primitive_node_occurs_of_theta_eq
      (d := n * s) (k := k) (j := n * u) (l := l)
      hdpos hjpos hkcop hθ
  exact base_dvd_of_mul_dvd_mul hnpos hocc.1

lemma sum_row_single_support_of_not_dvd
    {theta0 : ℝ} {n u s k : ℕ} (hnpos : 0 < n) (huodd : Odd u)
    (hspos : 0 < s) (hndiv : ¬ s ∣ u)
    (hk : k ∈ primIdx (n * s)) {a : ℝ} :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        (if thetaNode (n * u) l = thetaNode (n * s) k then a else 0)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro l hl
  by_cases htheta : thetaNode (n * u) l = thetaNode (n * s) k
  · have hdiv := support_order_dvd_of_row_hit hnpos huodd hspos hk htheta
    exact False.elim (hndiv hdiv)
  · simp [htheta]

lemma row_sum_finiteSpikeRaw_eq_support_sum
    (theta0 : ℝ) (R n j : ℕ) :
    (∑ l ∈ Finset.range j,
      lambdaWeight theta0 j l * finiteSpikeRaw theta0 R n (thetaNode j l)) =
    ∑ p ∈ spikeIdx n R,
      ∑ l ∈ Finset.range j,
        lambdaWeight theta0 j l *
          (if thetaNode j l = thetaNode (n * p.1) p.2 then
            finiteSpikeValueAtPrimitive theta0 n p.1 p.2
          else 0) := by
  classical
  unfold finiteSpikeRaw
  calc
    (∑ l ∈ Finset.range j,
      lambdaWeight theta0 j l *
        (∑ p ∈ spikeIdx n R,
          if thetaNode j l = thetaNode (n * p.1) p.2 then
            finiteSpikeValueAtPrimitive theta0 n p.1 p.2
          else 0)) =
        ∑ l ∈ Finset.range j,
          ∑ p ∈ spikeIdx n R,
            lambdaWeight theta0 j l *
              (if thetaNode j l = thetaNode (n * p.1) p.2 then
                finiteSpikeValueAtPrimitive theta0 n p.1 p.2
              else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.mul_sum]
    _ = ∑ p ∈ spikeIdx n R,
      ∑ l ∈ Finset.range j,
        lambdaWeight theta0 j l *
          (if thetaNode j l = thetaNode (n * p.1) p.2 then
            finiteSpikeValueAtPrimitive theta0 n p.1 p.2
          else 0) := by
          rw [Finset.sum_comm]

lemma row_sum_finiteSpikeRaw_eq_support_sigma_sum
    (theta0 : ℝ) (R n j : ℕ) :
    (∑ l ∈ Finset.range j,
      lambdaWeight theta0 j l * finiteSpikeRaw theta0 R n (thetaNode j l)) =
    ∑ s ∈ oddUpTo R,
      ∑ k ∈ primIdx (n * s),
        ∑ l ∈ Finset.range j,
          lambdaWeight theta0 j l *
            (if thetaNode j l = thetaNode (n * s) k then
              finiteSpikeValueAtPrimitive theta0 n s k
            else 0) := by
  rw [row_sum_finiteSpikeRaw_eq_support_sum]
  rw [spikeIdx, Finset.sum_sigma]

lemma Vprim_eq_sum_lambdaWeight_mul_sign (theta0 : ℝ) (d : ℕ) :
    (∑ k ∈ primIdx d,
      lambdaWeight theta0 d k * Real.sign (lambdaWeight theta0 d k)) =
        Vprim theta0 d := by
  simp [Vprim, real_mul_sign_eq_abs]

lemma sum_lambdaWeight_mul_signed_normalized
    {theta0 : ℝ} {d : ℕ} {a : ℝ}
    (hV : Vprim theta0 d ≠ 0) :
    (∑ k ∈ primIdx d,
      lambdaWeight theta0 d k *
        (a / Vprim theta0 d * Real.sign (lambdaWeight theta0 d k))) = a := by
  calc
    (∑ k ∈ primIdx d,
      lambdaWeight theta0 d k *
        (a / Vprim theta0 d * Real.sign (lambdaWeight theta0 d k))) =
        (a / Vprim theta0 d) *
          (∑ k ∈ primIdx d,
            lambdaWeight theta0 d k * Real.sign (lambdaWeight theta0 d k)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (a / Vprim theta0 d) * Vprim theta0 d := by
          rw [Vprim_eq_sum_lambdaWeight_mul_sign]
    _ = a := by
          field_simp [hV]

lemma sum_lambdaWeight_mul_finiteSpikeValueAtPrimitive
    {theta0 : ℝ} {n s : ℕ}
    (hV : Vprim theta0 (n * s) ≠ 0) :
    (∑ k ∈ primIdx (n * s),
      lambdaWeight theta0 (n * s) k *
        finiteSpikeValueAtPrimitive theta0 n s k) =
      spikeCoeff theta0 n s := by
  simpa [finiteSpikeValueAtPrimitive] using
    (sum_lambdaWeight_mul_signed_normalized
      (theta0 := theta0) (d := n * s) (a := spikeCoeff theta0 n s) hV)

lemma sum_occurrence_contribution
    {theta0 : ℝ} {R n u s : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hdiv : s ∣ u)
    (hsR : s ∈ oddUpTo R)
    (hcosns : Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : Vprim theta0 (n * s) ≠ 0) :
    (∑ k ∈ primIdx (n * s),
      lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
        finiteSpikeRaw theta0 R n
          (thetaNode (n * u) (occurrenceIndex (u / s) k))) =
      gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s := by
  have hqodd : Odd (u / s) := odd_div_of_dvd huodd hdiv
  have hmul : (n * s) * (u / s) = n * u :=
    mul_divisor_base_eq (n := n) hdiv
  calc
    (∑ k ∈ primIdx (n * s),
      lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
        finiteSpikeRaw theta0 R n
          (thetaNode (n * u) (occurrenceIndex (u / s) k))) =
        ∑ k ∈ primIdx (n * s),
          (gamma theta0 (n * u) (n * s) * lambdaWeight theta0 (n * s) k) *
            finiteSpikeValueAtPrimitive theta0 n s k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt : k < n * s := (mem_primIdx_iff.mp hk).1
          have hweight :=
            lambdaWeight_occurrenceIndex_eq_gamma_mul
              (theta0 := theta0) (d := n * s) (s := u / s) (k := k)
              hklt hqodd hcosns
          have hraw :=
            finiteSpikeRaw_at_divisor_occurrence
              (theta0 := theta0) (R := R) (n := n) (u := u) (s := s) (k := k)
              hnpos huodd hdiv hsR hk
          rw [← hmul] at hraw ⊢
          rw [hweight, hraw]
    _ = gamma theta0 (n * u) (n * s) *
          (∑ k ∈ primIdx (n * s),
            lambdaWeight theta0 (n * s) k *
              finiteSpikeValueAtPrimitive theta0 n s k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s := by
          rw [sum_lambdaWeight_mul_finiteSpikeValueAtPrimitive hV]

lemma row_sum_finiteSpikeRaw_eq_oddUpTo_if
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∣ u → Vprim theta0 (n * s) ≠ 0) :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        finiteSpikeRaw theta0 R n (thetaNode (n * u) l)) =
    ∑ s ∈ oddUpTo R,
      if s ∣ u then
        gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s
      else 0 := by
  classical
  rw [row_sum_finiteSpikeRaw_eq_support_sigma_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hdiv : s ∣ u
  · have hinner_value :
      (∑ k ∈ primIdx (n * s),
        ∑ l ∈ Finset.range (n * u),
          lambdaWeight theta0 (n * u) l *
            (if thetaNode (n * u) l = thetaNode (n * s) k then
              finiteSpikeValueAtPrimitive theta0 n s k else 0)) =
        ∑ k ∈ primIdx (n * s),
          lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
            finiteSpikeValueAtPrimitive theta0 n s k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_row_single_support_of_dvd
          (theta0 := theta0) (n := n) (u := u) (s := s) (k := k)
          huodd hdiv hk
    have hinner_value' :
      (∑ k ∈ primIdx (n * s),
        ∑ l ∈ Finset.range (n * u),
          (if thetaNode (n * u) l = thetaNode (n * s) k then
            lambdaWeight theta0 (n * u) l *
              finiteSpikeValueAtPrimitive theta0 n s k else 0)) =
        ∑ k ∈ primIdx (n * s),
          lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
            finiteSpikeValueAtPrimitive theta0 n s k := by
        simpa [mul_ite] using hinner_value
    have hinner_raw :
      (∑ k ∈ primIdx (n * s),
          lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
            finiteSpikeValueAtPrimitive theta0 n s k) =
        ∑ k ∈ primIdx (n * s),
          lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
            finiteSpikeRaw theta0 R n
              (thetaNode (n * u) (occurrenceIndex (u / s) k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [finiteSpikeRaw_at_divisor_occurrence
          (theta0 := theta0) (R := R) (n := n) (u := u) (s := s) (k := k)
          hnpos huodd hdiv hs hk]
    have hcontrib :=
      sum_occurrence_contribution
        (theta0 := theta0) (R := R) (n := n) (u := u) (s := s)
        hnpos huodd hdiv hs (hcosns s hdiv) (hV s hdiv)
    simp [hdiv]
    calc
      (∑ k ∈ primIdx (n * s),
        ∑ l ∈ Finset.range (n * u),
          (if thetaNode (n * u) l = thetaNode (n * s) k then
            lambdaWeight theta0 (n * u) l *
              finiteSpikeValueAtPrimitive theta0 n s k else 0)) =
          ∑ k ∈ primIdx (n * s),
            lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
              finiteSpikeValueAtPrimitive theta0 n s k := hinner_value'
      _ = ∑ k ∈ primIdx (n * s),
            lambdaWeight theta0 (n * u) (occurrenceIndex (u / s) k) *
              finiteSpikeRaw theta0 R n
                (thetaNode (n * u) (occurrenceIndex (u / s) k)) := hinner_raw
      _ = gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s := hcontrib
  · have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hzero :
      (∑ k ∈ primIdx (n * s),
        ∑ l ∈ Finset.range (n * u),
          lambdaWeight theta0 (n * u) l *
            (if thetaNode (n * u) l = thetaNode (n * s) k then
              finiteSpikeValueAtPrimitive theta0 n s k else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact sum_row_single_support_of_not_dvd
        (theta0 := theta0) (n := n) (u := u) (s := s) (k := k)
        hnpos huodd hspos hdiv hk
    have hzero' :
      (∑ k ∈ primIdx (n * s),
        ∑ l ∈ Finset.range (n * u),
          (if thetaNode (n * u) l = thetaNode (n * s) k then
            lambdaWeight theta0 (n * u) l *
              finiteSpikeValueAtPrimitive theta0 n s k else 0)) = 0 := by
      simpa [mul_ite] using hzero
    simp [hdiv]
    exact hzero'

lemma divisors_subset_oddUpTo {R u : ℕ} (huodd : Odd u) (huR : u ≤ R) :
    Nat.divisors u ⊆ oddUpTo R := by
  intro s hs
  have hdiv : s ∣ u := (Nat.mem_divisors.mp hs).1
  have hspos : 0 < s := Nat.pos_of_mem_divisors hs
  have hsleu : s ≤ u := Nat.le_of_dvd huodd.pos hdiv
  have hsodd : Odd s := odd_of_dvd_odd huodd hdiv
  exact mem_oddUpTo_iff.mpr ⟨hspos, hsleu.trans huR, hsodd⟩

lemma sum_oddUpTo_if_dvd_eq_sum_divisors
    {R u : ℕ} (huodd : Odd u) (huR : u ≤ R) (G : ℕ → ℝ) :
    (∑ s ∈ oddUpTo R, if s ∣ u then G s else 0) =
      ∑ s ∈ Nat.divisors u, G s := by
  classical
  have hsubset : Nat.divisors u ⊆ oddUpTo R :=
    divisors_subset_oddUpTo huodd huR
  have houtside :
      ∀ x ∈ oddUpTo R, x ∉ Nat.divisors u →
        (if x ∣ u then G x else 0) = 0 := by
    intro x hx hnot
    by_cases hdiv : x ∣ u
    · have hxdiv : x ∈ Nat.divisors u :=
        Nat.mem_divisors.mpr ⟨hdiv, Nat.ne_of_gt huodd.pos⟩
      exact False.elim (hnot hxdiv)
    · simp [hdiv]
  calc
    (∑ s ∈ oddUpTo R, if s ∣ u then G s else 0) =
        ∑ s ∈ Nat.divisors u, if s ∣ u then G s else 0 := by
          exact (Finset.sum_subset hsubset houtside).symm
    _ = ∑ s ∈ Nat.divisors u, G s := by
          apply Finset.sum_congr rfl
          intro s hs
          have hdiv : s ∣ u := (Nat.mem_divisors.mp hs).1
          simp [hdiv]

lemma row_sum_finiteSpikeRaw_eq_sum_divisors_gamma
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (huR : u ≤ R)
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∣ u → Vprim theta0 (n * s) ≠ 0) :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        finiteSpikeRaw theta0 R n (thetaNode (n * u) l)) =
    ∑ s ∈ Nat.divisors u,
      gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s := by
  rw [row_sum_finiteSpikeRaw_eq_oddUpTo_if hnpos huodd hcosns hV]
  exact sum_oddUpTo_if_dvd_eq_sum_divisors huodd huR
    (fun s => gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s)

lemma row_sum_finiteSpikeRaw_eq_ite
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (huR : u ≤ R)
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∣ u → Vprim theta0 (n * s) ≠ 0) :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        finiteSpikeRaw theta0 R n (thetaNode (n * u) l)) =
      if u = 1 then 1 else 0 := by
  rw [row_sum_finiteSpikeRaw_eq_sum_divisors_gamma hnpos huodd huR hcosns hV]
  have hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0 := by
    simpa using hcosns 1 (one_dvd u)
  exact sum_divisors_gamma_mul_spikeCoeff_eq_ite
    (theta0 := theta0) (n := n) (u := u) hnpos huodd hcosn hcosns

lemma rowEval_finiteSpikeRaw_of_not_isNodeRow_odd
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (huR : u ≤ R)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∣ u → Vprim theta0 (n * s) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) =
      if u = 1 then 1 else 0 := by
  have hrowpos : 0 < n * u := Nat.mul_pos hnpos huodd.pos
  have hrowne : n * u ≠ 0 := Nat.ne_of_gt hrowpos
  rw [rowEval, if_neg hrowne, if_neg hnot]
  exact row_sum_finiteSpikeRaw_eq_ite hnpos huodd huR hcosns hV

lemma finiteSpikeRaw_eq_zero_of_no_support
    {theta0 : ℝ} {R n : ℕ}
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    finiteSpikeRaw theta0 R n theta0 = 0 := by
  classical
  unfold finiteSpikeRaw
  apply Finset.sum_eq_zero
  intro p hp
  by_cases htheta : theta0 = thetaNode (n * p.1) p.2
  · have hp_mem := mem_spikeIdx_iff.mp hp
    have hklt : p.2 < n * p.1 := (mem_primIdx_iff.mp hp_mem.2).1
    have hnode : IsNodeRow theta0 (n * p.1) := by
      rw [htheta]
      exact isNodeRow_thetaNode hklt
    exact False.elim ((hcos p.1 hp_mem.1) hnode)
  · simp [htheta]

lemma rowEval_finiteSpikeRaw_of_isNodeRow_odd
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hnode : IsNodeRow theta0 (n * u))
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) = 0 := by
  have hrowpos : 0 < n * u := Nat.mul_pos hnpos huodd.pos
  have hrowne : n * u ≠ 0 := Nat.ne_of_gt hrowpos
  rw [rowEval, if_neg hrowne, if_pos hnode]
  exact finiteSpikeRaw_eq_zero_of_no_support hcos

lemma rowEval_finiteSpikeRaw_odd
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (huR : u ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∣ u → Vprim theta0 (n * s) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) =
      if u = 1 then 1 else 0 := by
  classical
  have hcosns : ∀ s : ℕ, s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0 := by
    intro s hdiv
    have hsdiv : s ∈ Nat.divisors u :=
      Nat.mem_divisors.mpr ⟨hdiv, Nat.ne_of_gt huodd.pos⟩
    exact hcos s (divisors_subset_oddUpTo huodd huR hsdiv)
  by_cases hnode : IsNodeRow theta0 (n * u)
  · rw [rowEval_finiteSpikeRaw_of_isNodeRow_odd hnpos huodd hnode hcos]
    by_cases hu1 : u = 1
    · exfalso
      subst u
      have h1mem : 1 ∈ oddUpTo R :=
        mem_oddUpTo_iff.mpr ⟨by norm_num, huR, by norm_num⟩
      exact (hcos 1 h1mem) hnode
    · simp [hu1]
  · exact rowEval_finiteSpikeRaw_of_not_isNodeRow_odd
      hnpos huodd huR hnode hcosns hV

lemma row_sum_finiteSpikeRaw_eq_zero_of_base_not_dvd
    {theta0 : ℝ} {R n j : ℕ}
    (hnpos : 0 < n) (hjpos : 0 < j) (hndiv : ¬ n ∣ j) :
    (∑ l ∈ Finset.range j,
      lambdaWeight theta0 j l *
        finiteSpikeRaw theta0 R n (thetaNode j l)) = 0 := by
  classical
  rw [row_sum_finiteSpikeRaw_eq_support_sigma_sum]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  by_cases htheta : thetaNode j l = thetaNode (n * s) k
  · have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hkcop : Nat.Coprime (2 * k + 1) (n * s) :=
      (mem_primIdx_iff.mp hk).2
    have hocc :=
      primitive_node_occurs_of_theta_eq
        (d := n * s) (k := k) (j := j) (l := l)
        hdpos hjpos hkcop htheta
    have hndiv' : n ∣ j :=
      dvd_trans (dvd_mul_right n s) hocc.1
    exact False.elim (hndiv hndiv')
  · simp [htheta]

lemma row_sum_finiteSpikeRaw_eq_zero_of_not_odd_multiple
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (hupos : 0 < u) (hu_not_odd : ¬ Odd u) :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        finiteSpikeRaw theta0 R n (thetaNode (n * u) l)) = 0 := by
  classical
  rw [row_sum_finiteSpikeRaw_eq_support_sigma_sum]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  by_cases htheta : thetaNode (n * u) l = thetaNode (n * s) k
  · have hsodd : Odd s := (mem_oddUpTo_iff.mp hs).2.2
    have hspos : 0 < s := hsodd.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hjpos : 0 < n * u := Nat.mul_pos hnpos hupos
    have hkcop : Nat.Coprime (2 * k + 1) (n * s) :=
      (mem_primIdx_iff.mp hk).2
    have hocc :=
      primitive_node_occurs_of_theta_eq
        (d := n * s) (k := k) (j := n * u) (l := l)
        hdpos hjpos hkcop htheta
    have hdiv : s ∣ u := base_dvd_of_mul_dvd_mul hnpos hocc.1
    have hquot : (n * u) / (n * s) = u / s :=
      Nat.mul_div_mul_left u s hnpos
    have hqodd : Odd (u / s) := by
      simpa [hquot] using hocc.2
    have hprod : Odd ((u / s) * s) := by
      rcases hqodd with ⟨a, ha⟩
      rcases hsodd with ⟨b, hb⟩
      rw [ha, hb]
      exact ⟨2 * a * b + a + b, by ring⟩
    have huodd : Odd u := by
      simpa [Nat.div_mul_cancel hdiv] using hprod
    exact False.elim (hu_not_odd huodd)
  · simp [htheta]

lemma rowEval_finiteSpikeRaw_eq_zero_of_base_not_dvd
    {theta0 : ℝ} {R n j : ℕ}
    (hnpos : 0 < n) (hjpos : 0 < j) (hndiv : ¬ n ∣ j)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 j (finiteSpikeRaw theta0 R n) = 0 := by
  have hjne : j ≠ 0 := Nat.ne_of_gt hjpos
  by_cases hnode : IsNodeRow theta0 j
  · rw [rowEval, if_neg hjne, if_pos hnode]
    exact finiteSpikeRaw_eq_zero_of_no_support hcos
  · rw [rowEval, if_neg hjne, if_neg hnode]
    exact row_sum_finiteSpikeRaw_eq_zero_of_base_not_dvd hnpos hjpos hndiv

lemma rowEval_finiteSpikeRaw_eq_zero_of_not_odd_multiple
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (hupos : 0 < u) (hu_not_odd : ¬ Odd u)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) = 0 := by
  have hrowpos : 0 < n * u := Nat.mul_pos hnpos hupos
  have hrowne : n * u ≠ 0 := Nat.ne_of_gt hrowpos
  by_cases hnode : IsNodeRow theta0 (n * u)
  · rw [rowEval, if_neg hrowne, if_pos hnode]
    exact finiteSpikeRaw_eq_zero_of_no_support hcos
  · rw [rowEval, if_neg hrowne, if_neg hnode]
    exact row_sum_finiteSpikeRaw_eq_zero_of_not_odd_multiple
      hnpos hupos hu_not_odd

lemma rowEval_finiteSpikeRaw_eq_zero_of_le_mul_ne
    {theta0 : ℝ} {R n j : ℕ}
    (hnpos : 0 < n) (hjpos : 0 < j) (hjle : j ≤ R * n)
    (hjne : j ≠ n)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0) :
    rowEval theta0 j (finiteSpikeRaw theta0 R n) = 0 := by
  classical
  by_cases hndiv : n ∣ j
  · rcases hndiv with ⟨u, hju⟩
    have hupos : 0 < u := by
      by_contra hnot
      have hu0 : u = 0 := Nat.eq_zero_of_not_pos hnot
      have hj0 : j = 0 := by
        simpa [hu0] using hju
      exact (Nat.ne_of_gt hjpos) hj0
    have hmul_le : n * u ≤ n * R := by
      rw [← hju]
      simpa [Nat.mul_comm] using hjle
    have huR : u ≤ R := le_of_mul_le_mul_left hmul_le hnpos
    by_cases huodd : Odd u
    · have hu_ne : u ≠ 1 := by
        intro hu1
        apply hjne
        simp [hju, hu1]
      have hVdiv : ∀ s : ℕ, s ∣ u → Vprim theta0 (n * s) ≠ 0 := by
        intro s hdiv
        have hsdiv : s ∈ Nat.divisors u :=
          Nat.mem_divisors.mpr ⟨hdiv, Nat.ne_of_gt huodd.pos⟩
        exact hV s (divisors_subset_oddUpTo huodd huR hsdiv)
      rw [hju]
      simpa [hu_ne] using
        rowEval_finiteSpikeRaw_odd
          (theta0 := theta0) (R := R) (n := n) (u := u)
          hnpos huodd huR hcos hVdiv
    · rw [hju]
      exact rowEval_finiteSpikeRaw_eq_zero_of_not_odd_multiple
        hnpos hupos huodd hcos
  · exact rowEval_finiteSpikeRaw_eq_zero_of_base_not_dvd
      hnpos hjpos hndiv hcos

lemma rowEval_finiteSpikeRaw_self
    {theta0 : ℝ} {R n : ℕ}
    (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV1 : Vprim theta0 n ≠ 0) :
    rowEval theta0 n (finiteSpikeRaw theta0 R n) = 1 := by
  have hVdiv : ∀ s : ℕ, s ∣ 1 → Vprim theta0 (n * s) ≠ 0 := by
    intro s hdiv
    have hs1 : s = 1 := Nat.dvd_one.mp hdiv
    simpa [hs1] using hV1
  simpa using
    rowEval_finiteSpikeRaw_odd
      (theta0 := theta0) (R := R) (n := n) (u := 1)
      hnpos (by norm_num : Odd 1) hR hcos hVdiv

lemma rowEval_finiteSpikeRaw_block_rows
    {theta0 : ℝ} {R n : ℕ}
    (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0) :
    rowEval theta0 n (finiteSpikeRaw theta0 R n) = 1 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        rowEval theta0 j (finiteSpikeRaw theta0 R n) = 0 := by
  have h1mem : 1 ∈ oddUpTo R :=
    mem_oddUpTo_iff.mpr ⟨by norm_num, hR, by norm_num⟩
  have hV1 : Vprim theta0 n ≠ 0 := by
    simpa using hV 1 h1mem
  refine ⟨rowEval_finiteSpikeRaw_self hnpos hR hcos hV1, ?_⟩
  intro j hjpos hjle hjne
  exact rowEval_finiteSpikeRaw_eq_zero_of_le_mul_ne
    hnpos hjpos hjle hjne hcos hV

/-- A triangular tent of height `a`, centered at `p`, with radius `r`. -/
def tent (p r a : ℝ) : ℝ → ℝ :=
  fun theta => a * max 0 (1 - |theta - p| / r)

lemma continuous_tent (p r a : ℝ) :
    Continuous (tent p r a) := by
  unfold tent
  have hinner : Continuous fun theta : ℝ => 1 - |theta - p| / r := by
    continuity
  exact continuous_const.mul (continuous_const.max hinner)

lemma tent_apply_center {p r a : ℝ} (_hr : r ≠ 0) :
    tent p r a p = a := by
  simp [tent]

lemma tent_eq_zero_of_radius_le {p r a theta : ℝ}
    (hr : 0 < r) (h : r ≤ |theta - p|) :
    tent p r a theta = 0 := by
  have hratio : 1 ≤ |theta - p| / r := by
    rw [le_div_iff₀ hr]
    simpa using h
  have hinner : 1 - |theta - p| / r ≤ 0 := by
    linarith
  rw [tent, max_eq_left hinner, mul_zero]

/-- A finite continuous spike as a sum of triangular tents. -/
def continuousSpikeRaw (P : Finset ℝ) (radius height : ℝ → ℝ) : ℝ → ℝ :=
  fun theta => ∑ p ∈ P, tent p (radius p) (height p) theta

lemma continuous_continuousSpikeRaw
    (P : Finset ℝ) (radius height : ℝ → ℝ) :
    Continuous (continuousSpikeRaw P radius height) := by
  unfold continuousSpikeRaw
  exact continuous_finset_sum P fun p _hp =>
    continuous_tent p (radius p) (height p)

/-- The same finite tent spike, restricted to the angle interval. -/
def continuousSpike (P : Finset ℝ) (radius height : ℝ → ℝ) : AngleFun where
  toFun x := continuousSpikeRaw P radius height x.1
  continuous_toFun :=
    (continuous_continuousSpikeRaw P radius height).comp continuous_subtype_val

/-- The set of primitive support angles used by the algebraic finite spike. -/
def spikePoints (n R : ℕ) : Finset ℝ :=
  by
    classical
    exact (spikeIdx n R).image fun p => thetaNode (n * p.1) p.2

lemma mem_spikePoints_of_mem
    {R n s k : ℕ} (hs : s ∈ oddUpTo R) (hk : k ∈ primIdx (n * s)) :
    thetaNode (n * s) k ∈ spikePoints n R := by
  classical
  refine Finset.mem_image.mpr ?_
  exact ⟨⟨s, k⟩, by simpa [spikeIdx] using And.intro hs hk, rfl⟩

lemma finiteSpikeRaw_eq_zero_of_not_mem_spikePoints
    {theta0 theta : ℝ} {R n : ℕ}
    (hnot : theta ∉ spikePoints n R) :
    finiteSpikeRaw theta0 R n theta = 0 := by
  classical
  unfold finiteSpikeRaw
  apply Finset.sum_eq_zero
  intro p hp
  by_cases htheta : theta = thetaNode (n * p.1) p.2
  · have hp_point : theta ∈ spikePoints n R := by
      refine Finset.mem_image.mpr ?_
      exact ⟨p, hp, htheta.symm⟩
    exact False.elim (hnot hp_point)
  · simp [htheta]

/-- All Chebyshev-root angles in rows `1, ..., K`. -/
def nodesUpTo (K : ℕ) : Finset ℝ :=
  by
    classical
    exact ((Finset.Icc 1 K).sigma fun j => Finset.range j).image fun p =>
      thetaNode p.1 p.2

lemma mem_nodesUpTo_of_row
    {K j k : ℕ} (hjpos : 1 ≤ j) (hjK : j ≤ K) (hk : k < j) :
    thetaNode j k ∈ nodesUpTo K := by
  classical
  unfold nodesUpTo
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨j, k⟩, ?_, rfl⟩
  simp [hjpos, hjK, hk]

lemma spikePoints_subset_nodesUpTo
    {R n : ℕ} (hnpos : 0 < n) :
    spikePoints n R ⊆ nodesUpTo (R * n) := by
  classical
  intro theta htheta
  rcases Finset.mem_image.mp htheta with ⟨p, hp, rfl⟩
  have hp_mem := mem_spikeIdx_iff.mp hp
  have hs_info := mem_oddUpTo_iff.mp hp_mem.1
  have hspos : 0 < p.1 := hs_info.2.2.pos
  have hklt : p.2 < n * p.1 := (mem_primIdx_iff.mp hp_mem.2).1
  have hjpos : 1 ≤ n * p.1 :=
    Nat.succ_le_of_lt (Nat.mul_pos hnpos hspos)
  have hjK : n * p.1 ≤ R * n := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hs_info.2.1
  exact mem_nodesUpTo_of_row hjpos hjK hklt

lemma theta0_not_mem_spikePoints_of_good_rows
    {theta0 : ℝ} {R n : ℕ}
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    theta0 ∉ spikePoints n R := by
  classical
  intro htheta
  rcases Finset.mem_image.mp htheta with ⟨p, hp, hp_eq⟩
  have hp_mem := mem_spikeIdx_iff.mp hp
  have hklt : p.2 < n * p.1 := (mem_primIdx_iff.mp hp_mem.2).1
  have hnode : IsNodeRow theta0 (n * p.1) := by
    rw [← hp_eq]
    exact isNodeRow_thetaNode hklt
  exact (hcos p.1 hp_mem.1) hnode

lemma finite_set_positive_separation
    {P : Finset ℝ} {x0 : ℝ}
    (hdisj : ∀ x : ℝ, x ∈ P → x ≠ x0) :
    ∃ rho > 0, ∀ x : ℝ, x ∈ P → rho ≤ |x0 - x| := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | insert a P haP ih =>
      have ha_ne : a ≠ x0 := hdisj a (Finset.mem_insert_self a P)
      have hPdisj : ∀ x : ℝ, x ∈ P → x ≠ x0 := by
        intro x hx
        exact hdisj x (Finset.mem_insert_of_mem hx)
      rcases ih hPdisj with ⟨rhoP, hrhoP, hP⟩
      have ha_pos : 0 < |x0 - a| := by
        exact abs_pos.mpr (sub_ne_zero.mpr ha_ne.symm)
      refine ⟨min |x0 - a| rhoP, lt_min ha_pos hrhoP, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxP
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hP x hxP)

lemma finite_set_pair_positive_separation (E : Finset ℝ) :
    ∃ rho > 0, ∀ x : ℝ, x ∈ E → ∀ y : ℝ, y ∈ E → x ≠ y →
      rho ≤ |x - y| := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | insert a E haE ih =>
      rcases ih with ⟨rhoE, hrhoE, hE⟩
      have hdisj : ∀ x : ℝ, x ∈ E → x ≠ a := by
        intro x hx hxa
        exact haE (by simpa [hxa] using hx)
      rcases finite_set_positive_separation (P := E) (x0 := a) hdisj with
        ⟨rhoA, hrhoA, hA⟩
      refine ⟨min rhoE rhoA, lt_min hrhoE hrhoA, ?_⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hxE
      · rcases Finset.mem_insert.mp hy with rfl | hyE
        · exact False.elim (hxy rfl)
        · exact (min_le_right _ _).trans (hA y hyE)
      · rcases Finset.mem_insert.mp hy with rfl | hyE
        · rw [abs_sub_comm]
          exact (min_le_right _ _).trans (hA x hxE)
        · exact (min_le_left _ _).trans (hE x hxE y hyE hxy)

lemma exists_constant_isolating_radius
    {P E : Finset ℝ} {theta0 : ℝ}
    (hPE : P ⊆ E) (hthetaE : theta0 ∈ E) (hthetaP : theta0 ∉ P) :
    ∃ radius : ℝ → ℝ,
      (∀ p : ℝ, p ∈ P → 0 < radius p) ∧
      (∀ p : ℝ, p ∈ P → ∀ e : ℝ, e ∈ E → e ≠ p →
        radius p ≤ |e - p|) ∧
      (∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps →
        ∀ p : ℝ, p ∈ P → radius p ≤ |theta - p|) := by
  classical
  rcases finite_set_pair_positive_separation E with ⟨rho, hrho, hpair⟩
  let radius : ℝ → ℝ := fun _ => rho / 4
  refine ⟨radius, ?_, ?_, ?_⟩
  · intro p hp
    dsimp [radius]
    positivity
  · intro p hp e he hne
    have hpE : p ∈ E := hPE hp
    have hle : rho ≤ |e - p| := hpair e he p hpE hne
    dsimp [radius]
    linarith
  · refine ⟨rho / 4, by positivity, ?_⟩
    intro theta _htheta hdist p hp
    have hpE : p ∈ E := hPE hp
    have hne : theta0 ≠ p := by
      intro h
      exact hthetaP (h ▸ hp)
    have hdist0 : rho ≤ |theta0 - p| :=
      hpair theta0 hthetaE p hpE hne
    have htri : |theta0 - p| ≤ |theta - theta0| + |theta - p| := by
      have h := abs_add_le (theta0 - theta) (theta - p)
      have hsum : theta0 - theta + (theta - p) = theta0 - p := by ring
      simpa [hsum, abs_sub_comm theta0 theta] using h
    have hle : rho ≤ |theta - theta0| + |theta - p| :=
      hdist0.trans htri
    dsimp [radius]
    linarith

lemma continuousSpikeRaw_apply_eq_height
    {P : Finset ℝ} {radius height : ℝ → ℝ} {x : ℝ}
    (hxP : x ∈ P)
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ P → p ≠ x → radius p ≤ |x - p|) :
    continuousSpikeRaw P radius height x = height x := by
  classical
  unfold continuousSpikeRaw
  rw [Finset.sum_eq_single x]
  · exact tent_apply_center (ne_of_gt (hradpos x hxP))
  · intro p hp hne
    exact tent_eq_zero_of_radius_le (hradpos p hp) (hsep p hp hne)
  · intro hxnot
    exact False.elim (hxnot hxP)

lemma continuousSpikeRaw_apply_eq_zero_of_far
    {P : Finset ℝ} {radius height : ℝ → ℝ} {x : ℝ}
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p)
    (hfar : ∀ p : ℝ, p ∈ P → radius p ≤ |x - p|) :
    continuousSpikeRaw P radius height x = 0 := by
  classical
  unfold continuousSpikeRaw
  apply Finset.sum_eq_zero
  intro p hp
  exact tent_eq_zero_of_radius_le (hradpos p hp) (hfar p hp)

lemma continuousSpikeRaw_eq_finiteSpikeRaw_of_isolated_at
    {theta0 theta : ℝ} {R n : ℕ} {E : Finset ℝ} {radius : ℝ → ℝ}
    (hthetaE : theta ∈ E)
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R → ∀ e : ℝ, e ∈ E → e ≠ p →
      radius p ≤ |e - p|) :
    continuousSpikeRaw (spikePoints n R) radius (finiteSpikeRaw theta0 R n) theta =
      finiteSpikeRaw theta0 R n theta := by
  classical
  by_cases hthetaP : theta ∈ spikePoints n R
  · exact continuousSpikeRaw_apply_eq_height hthetaP hradpos
      (fun p hp hne => hsep p hp theta hthetaE hne.symm)
  · rw [continuousSpikeRaw_apply_eq_zero_of_far hradpos
      (fun p hp => hsep p hp theta hthetaE (fun h => hthetaP (h ▸ hp)))]
    exact (finiteSpikeRaw_eq_zero_of_not_mem_spikePoints hthetaP).symm

lemma rowEval_congr_on_nodes
    {theta0 : ℝ} {j : ℕ} {g h : ℝ → ℝ}
    (hbase : g theta0 = h theta0)
    (hnodes : ∀ k : ℕ, k < j → g (thetaNode j k) = h (thetaNode j k)) :
    rowEval theta0 j g = rowEval theta0 j h := by
  classical
  by_cases hj0 : j = 0
  · simp [rowEval, hj0]
  · by_cases hnode : IsNodeRow theta0 j
    · simp [rowEval, hj0, hnode, hbase]
    · simp [rowEval, hj0, hnode]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hnodes k (Finset.mem_range.mp hk)]

lemma rowEval_continuousSpike_eq_finiteSpikeRaw
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K j : ℕ} (hjK : j ≤ K) {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo K) → e ≠ p →
        radius p ≤ |e - p|) :
    rowEval theta0 j
        (angleFunToRaw
          (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n))) =
      rowEval theta0 j (finiteSpikeRaw theta0 R n) := by
  classical
  apply rowEval_congr_on_nodes
  · have hraw :=
      continuousSpikeRaw_eq_finiteSpikeRaw_of_isolated_at
        (theta0 := theta0) (theta := theta0) (R := R) (n := n)
        (E := insert theta0 (nodesUpTo K)) (radius := radius)
        (by simp) hradpos hsep
    rw [angleFunToRaw_of_mem _ htheta0]
    simpa [continuousSpike] using hraw
  · intro k hk
    have htheta_mem : thetaNode j k ∈ AngleI := thetaNode_mem_angleI hk
    have hjpos : 1 ≤ j := by omega
    have hnodeE : thetaNode j k ∈ insert theta0 (nodesUpTo K) := by
      simp [mem_nodesUpTo_of_row hjpos hjK hk]
    have hraw :=
      continuousSpikeRaw_eq_finiteSpikeRaw_of_isolated_at
        (theta0 := theta0) (theta := thetaNode j k) (R := R) (n := n)
        (E := insert theta0 (nodesUpTo K)) (radius := radius)
        hnodeE hradpos hsep
    rw [angleFunToRaw_of_mem _ htheta_mem]
    simpa [continuousSpike] using hraw

lemma F_continuousSpike_eq_rowEval_finiteSpikeRaw
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K j : ℕ} (hjK : j ≤ K) {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo K) → e ≠ p →
        radius p ≤ |e - p|) :
    F theta0 j
        (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)) =
      rowEval theta0 j (finiteSpikeRaw theta0 R n) := by
  exact rowEval_continuousSpike_eq_finiteSpikeRaw htheta0 hjK hradpos hsep

lemma F_continuousSpike_block_rows
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R) {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo (R * n)) → e ≠ p →
        radius p ≤ |e - p|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0) :
    F theta0 n
        (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)) = 1 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j
          (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)) = 0 := by
  have hraw := rowEval_finiteSpikeRaw_block_rows hnpos hR hcos hV
  have hn_le : n ≤ R * n := by
    simpa [one_mul] using Nat.mul_le_mul_right n hR
  refine ⟨?_, ?_⟩
  · rw [F_continuousSpike_eq_rowEval_finiteSpikeRaw
      htheta0 hn_le hradpos hsep]
    exact hraw.1
  · intro j hjpos hjle hjne
    rw [F_continuousSpike_eq_rowEval_finiteSpikeRaw
      htheta0 hjle hradpos hsep]
    exact hraw.2 j hjpos hjle hjne

lemma continuousSpike_vanishesNear_of_radius_away
    {theta0 : ℝ} {P : Finset ℝ} {radius height : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p)
    (haway : ∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps →
      ∀ p : ℝ, p ∈ P → radius p ≤ |theta - p|) :
    VanishesNear theta0
      (angleFunToRaw (continuousSpike P radius height)) := by
  rcases haway with ⟨eps, heps, hfar⟩
  refine ⟨eps, heps, ?_⟩
  intro theta htheta hdist
  rw [angleFunToRaw_of_mem _ htheta]
  simpa [continuousSpike] using
    continuousSpikeRaw_apply_eq_zero_of_far hradpos (hfar theta htheta hdist)

lemma abs_tent_le_abs_height {p r a theta : ℝ} (hr : 0 < r) :
    |tent p r a theta| ≤ |a| := by
  have hdiv_nonneg : 0 ≤ |theta - p| / r :=
    div_nonneg (abs_nonneg _) (le_of_lt hr)
  have hinner_le : 1 - |theta - p| / r ≤ 1 := by
    linarith
  have hmax_nonneg : 0 ≤ max 0 (1 - |theta - p| / r) :=
    le_max_left _ _
  have hmax_le : max 0 (1 - |theta - p| / r) ≤ 1 :=
    max_le (by norm_num) hinner_le
  calc
    |tent p r a theta| =
        |a| * |max 0 (1 - |theta - p| / r)| := by
          simp [tent, abs_mul]
    _ = |a| * max 0 (1 - |theta - p| / r) := by
          rw [abs_of_nonneg hmax_nonneg]
    _ ≤ |a| * 1 := by
          exact mul_le_mul_of_nonneg_left hmax_le (abs_nonneg a)
    _ = |a| := by ring

lemma abs_continuousSpikeRaw_le_sum_abs_height
    {P : Finset ℝ} {radius height : ℝ → ℝ} {theta : ℝ}
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p) :
    |continuousSpikeRaw P radius height theta| ≤ ∑ p ∈ P, |height p| := by
  unfold continuousSpikeRaw
  calc
    |∑ p ∈ P, tent p (radius p) (height p) theta| ≤
        ∑ p ∈ P, |tent p (radius p) (height p) theta| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, |height p| := by
          apply Finset.sum_le_sum
          intro p hp
          exact abs_tent_le_abs_height (hradpos p hp)

lemma norm_continuousSpike_le_sum_abs_height
    {P : Finset ℝ} {radius height : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p) :
    ‖continuousSpike P radius height‖ ≤ ∑ p ∈ P, |height p| := by
  rw [ContinuousMap.norm_le _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  intro theta
  simpa [Real.norm_eq_abs, continuousSpike] using
    abs_continuousSpikeRaw_le_sum_abs_height
      (P := P) (radius := radius) (height := height) (theta := theta.1) hradpos

lemma exists_continuousSpike_exact_block
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R) {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo (R * n)) → e ≠ p →
        radius p ≤ |e - p|)
    (haway : ∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps →
      ∀ p : ℝ, p ∈ spikePoints n R → radius p ≤ |theta - p|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ ∑ p ∈ spikePoints n R, |finiteSpikeRaw theta0 R n p| := by
  let psi : AngleFun :=
    continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)
  have hblock :=
    F_continuousSpike_block_rows
      (theta0 := theta0) htheta0 hnpos hR hradpos hsep hcos hV
  refine ⟨psi, ?_, hblock.1, hblock.2, ?_⟩
  · exact continuousSpike_vanishesNear_of_radius_away hradpos haway
  · exact norm_continuousSpike_le_sum_abs_height hradpos

lemma exists_continuousSpike_exact_block_of_good_rows
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ ∑ p ∈ spikePoints n R, |finiteSpikeRaw theta0 R n p| := by
  classical
  let E : Finset ℝ := insert theta0 (nodesUpTo (R * n))
  have hPE : spikePoints n R ⊆ E := by
    intro p hp
    exact Finset.mem_insert.mpr
      (Or.inr (spikePoints_subset_nodesUpTo hnpos hp))
  have hthetaE : theta0 ∈ E := Finset.mem_insert_self _ _
  have hthetaP : theta0 ∉ spikePoints n R :=
    theta0_not_mem_spikePoints_of_good_rows hcos
  rcases exists_constant_isolating_radius
      (P := spikePoints n R) (E := E) (theta0 := theta0)
      hPE hthetaE hthetaP with
    ⟨radius, hradpos, hsep, haway⟩
  exact exists_continuousSpike_exact_block
    htheta0 hnpos hR hradpos hsep haway hcos hV

end Erdos1151Formalization

end
