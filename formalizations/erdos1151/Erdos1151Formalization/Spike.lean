import Erdos1151Formalization.Basic
import Mathlib.Data.Real.Sign
import Mathlib.NumberTheory.Harmonic.Bounds
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

/-- Odd integers in `[1, R]`. -/
def oddUpTo (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter Odd

lemma mem_oddUpTo_iff {R s : ℕ} :
    s ∈ oddUpTo R ↔ 1 ≤ s ∧ s ≤ R ∧ Odd s := by
  simp [oddUpTo, and_assoc, and_comm]

lemma one_half_le_abs_cos_or_one_half_le_abs_cos_two_mul (x : ℝ) :
    (1 / 2 : ℝ) ≤ |Real.cos x| ∨
      (1 / 2 : ℝ) ≤ |Real.cos (2 * x)| := by
  by_cases h : (1 / 2 : ℝ) ≤ |Real.cos x|
  · exact Or.inl h
  · right
    have hlt : |Real.cos x| < (1 / 2 : ℝ) := lt_of_not_ge h
    have hsq_lt : Real.cos x ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      rw [sq_lt_sq]
      simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hlt
    have hcos_le : Real.cos (2 * x) ≤ -(1 / 2 : ℝ) := by
      rw [Real.cos_two_mul]
      nlinarith
    have hcos_nonpos : Real.cos (2 * x) ≤ 0 := by
      nlinarith
    rw [abs_of_nonpos hcos_nonpos]
    nlinarith

lemma exists_large_pow_two_abs_cos_ge_half (theta : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ IsPowTwo n ∧ 0 < n ∧
      (1 / 2 : ℝ) ≤ |Real.cos ((n : ℝ) * theta)| := by
  let x : ℝ := ((2 ^ N : ℕ) : ℝ) * theta
  rcases one_half_le_abs_cos_or_one_half_le_abs_cos_two_mul x with h | h
  · refine ⟨2 ^ N, ?_, ?_, ?_, ?_⟩
    · exact Nat.lt_two_pow_self.le
    · exact ⟨N, rfl⟩
    · exact Nat.pow_pos (by norm_num : 0 < 2)
    · simpa [x] using h
  · refine ⟨2 ^ (N + 1), ?_, ?_, ?_, ?_⟩
    · have hpowle : 2 ^ N ≤ 2 ^ (N + 1) :=
        pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (Nat.le_succ N)
      exact ((Nat.lt_two_pow_self (n := N)).trans_le hpowle).le
    · exact ⟨N + 1, rfl⟩
    · exact Nat.pow_pos (by norm_num : 0 < 2)
    · have hangle :
          2 * (((2 ^ N : ℕ) : ℝ) * theta) =
            ((2 ^ (N + 1) : ℕ) : ℝ) * theta := by
        rw [pow_succ]
        norm_num [Nat.cast_mul]
        ring
      rw [← hangle]
      simpa [x] using h

lemma cos_two_mul_eq_neg_one_of_cos_eq_zero {x : ℝ}
    (h : Real.cos x = 0) :
    Real.cos (2 * x) = -1 := by
  rw [Real.cos_two_mul, h]
  norm_num

lemma cos_two_mul_eq_one_of_cos_eq_one {x : ℝ}
    (h : Real.cos x = 1) :
    Real.cos (2 * x) = 1 := by
  rw [Real.cos_two_mul, h]
  norm_num

lemma cos_four_mul_eq_one_of_cos_eq_zero {x : ℝ}
    (h : Real.cos x = 0) :
    Real.cos (4 * x) = 1 := by
  have h2 : Real.cos (2 * x) = -1 :=
    cos_two_mul_eq_neg_one_of_cos_eq_zero h
  have hangle : 4 * x = 2 * (2 * x) := by ring
  rw [hangle, Real.cos_two_mul, h2]
  norm_num

lemma cos_two_pow_succ_succ_mul_eq_one_of_cos_eq_zero {x : ℝ}
    (h : Real.cos x = 0) (m : ℕ) :
    Real.cos (((2 ^ (m + 2) : ℕ) : ℝ) * x) = 1 := by
  induction m with
  | zero =>
      simpa using cos_four_mul_eq_one_of_cos_eq_zero h
  | succ m ih =>
      have hangle :
          ((2 ^ (m.succ + 2) : ℕ) : ℝ) * x =
            2 * (((2 ^ (m + 2) : ℕ) : ℝ) * x) := by
        have hexp : m.succ + 2 = (m + 2) + 1 := by omega
        rw [hexp, pow_succ]
        norm_num [Nat.cast_mul]
        ring
      rw [hangle]
      exact cos_two_mul_eq_one_of_cos_eq_one ih

lemma cos_two_pow_mul_ne_zero_of_cos_eq_zero {x : ℝ} {m : ℕ}
    (hm : 0 < m) (h : Real.cos x = 0) :
    Real.cos (((2 ^ m : ℕ) : ℝ) * x) ≠ 0 := by
  rcases m with _ | m
  · exact False.elim (Nat.lt_irrefl 0 hm)
  rcases m with _ | m
  · have h2 : Real.cos (((2 ^ 1 : ℕ) : ℝ) * x) = -1 := by
      simpa using cos_two_mul_eq_neg_one_of_cos_eq_zero h
    intro hz
    rw [h2] at hz
    norm_num at hz
  · have hpow :
        Real.cos (((2 ^ (m.succ + 1) : ℕ) : ℝ) * x) = 1 := by
      have hexp : m.succ + 1 = m + 2 := by omega
      simpa [hexp] using
        cos_two_pow_succ_succ_mul_eq_one_of_cos_eq_zero h m
    intro hz
    rw [hpow] at hz
    norm_num at hz

lemma cos_two_pow_mul_ne_zero_of_lt_of_cos_two_pow_mul_eq_zero
    {theta : ℝ} {r q : ℕ} (hrq : r < q)
    (hzero : Real.cos (((2 ^ r : ℕ) : ℝ) * theta) = 0) :
    Real.cos (((2 ^ q : ℕ) : ℝ) * theta) ≠ 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (le_of_lt hrq)
  have hmpos : 0 < m := by omega
  have hangle :
      ((2 ^ q : ℕ) : ℝ) * theta =
        ((2 ^ m : ℕ) : ℝ) * (((2 ^ r : ℕ) : ℝ) * theta) := by
    rw [hm, pow_add]
    norm_num [Nat.cast_mul]
    ring
  rw [hangle]
  exact cos_two_pow_mul_ne_zero_of_cos_eq_zero hmpos hzero

lemma cos_two_pow_mul_odd_factor_ne_zero_of_lt_of_eq_zero
    {theta : ℝ} {s r q : ℕ} (hrq : r < q)
    (hzero : Real.cos ((((2 ^ r) * s : ℕ) : ℝ) * theta) = 0) :
    Real.cos ((((2 ^ q) * s : ℕ) : ℝ) * theta) ≠ 0 := by
  have hzero' :
      Real.cos (((2 ^ r : ℕ) : ℝ) * ((s : ℝ) * theta)) = 0 := by
    simpa [Nat.cast_mul, mul_assoc] using hzero
  have hne :=
    cos_two_pow_mul_ne_zero_of_lt_of_cos_two_pow_mul_eq_zero
      (theta := (s : ℝ) * theta) hrq hzero'
  simpa [Nat.cast_mul, mul_assoc] using hne

lemma exists_large_dyadic_exponent_abs_cos_ge_half (theta : ℝ) (M : ℕ) :
    ∃ r : ℕ, M ≤ r ∧
      (1 / 2 : ℝ) ≤ |Real.cos (((2 ^ r : ℕ) : ℝ) * theta)| := by
  let x : ℝ := ((2 ^ M : ℕ) : ℝ) * theta
  rcases one_half_le_abs_cos_or_one_half_le_abs_cos_two_mul x with h | h
  · exact ⟨M, le_rfl, by simpa [x] using h⟩
  · refine ⟨M + 1, by omega, ?_⟩
    have hangle :
        2 * (((2 ^ M : ℕ) : ℝ) * theta) =
          ((2 ^ (M + 1) : ℕ) : ℝ) * theta := by
      rw [pow_succ]
      norm_num [Nat.cast_mul]
      ring
    rw [← hangle]
    simpa [x] using h

lemma exists_dyadic_exponent_after_no_cos_zero_for_factor
    (theta : ℝ) (s : ℕ) :
    ∃ M : ℕ, ∀ r : ℕ, M ≤ r →
      Real.cos ((((2 ^ r) * s : ℕ) : ℝ) * theta) ≠ 0 := by
  classical
  by_cases hbad :
      ∃ r : ℕ, Real.cos ((((2 ^ r) * s : ℕ) : ℝ) * theta) = 0
  · rcases hbad with ⟨r0, hr0⟩
    refine ⟨r0 + 1, ?_⟩
    intro r hr
    exact cos_two_pow_mul_odd_factor_ne_zero_of_lt_of_eq_zero
      (theta := theta) (s := s) (r := r0) (q := r) (by omega) hr0
  · refine ⟨0, ?_⟩
    intro r _hr hz
    exact hbad ⟨r, hz⟩

lemma exists_dyadic_exponent_after_no_cos_zero_for_finset
    (theta : ℝ) (S : Finset ℕ) :
    ∃ M : ℕ, ∀ r : ℕ, M ≤ r → ∀ s : ℕ, s ∈ S →
      Real.cos ((((2 ^ r) * s : ℕ) : ℝ) * theta) ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | insert a S haS ih =>
      rcases exists_dyadic_exponent_after_no_cos_zero_for_factor theta a with
        ⟨Ma, hMa⟩
      rcases ih with ⟨MS, hMS⟩
      refine ⟨max Ma MS, ?_⟩
      intro r hr s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hsS
      · exact hMa r ((le_max_left Ma MS).trans hr)
      · exact hMS r ((le_max_right Ma MS).trans hr) s hsS

lemma exists_large_dyadic_exponent_good_cos_oddUpTo
    (theta : ℝ) (R N : ℕ) :
    ∃ r : ℕ, N ≤ r ∧
      (1 / 2 : ℝ) ≤ |Real.cos (((2 ^ r : ℕ) : ℝ) * theta)| ∧
      ∀ s : ℕ, s ∈ oddUpTo R →
        Real.cos ((((2 ^ r) * s : ℕ) : ℝ) * theta) ≠ 0 := by
  rcases exists_dyadic_exponent_after_no_cos_zero_for_finset
      theta (oddUpTo R) with
    ⟨M, hM⟩
  rcases exists_large_dyadic_exponent_abs_cos_ge_half theta (max N M) with
    ⟨r, hr, hcos⟩
  refine ⟨r, (le_max_left N M).trans hr, hcos, ?_⟩
  intro s hs
  exact hM r ((le_max_right N M).trans hr) s hs

lemma exists_large_pow_two_good_cos_oddUpTo
    (theta : ℝ) (R N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ IsPowTwo n ∧ 0 < n ∧
      (1 / 2 : ℝ) ≤ |Real.cos ((n : ℝ) * theta)| ∧
      ∀ s : ℕ, s ∈ oddUpTo R →
        Real.cos (((n * s : ℕ) : ℝ) * theta) ≠ 0 := by
  rcases exists_large_dyadic_exponent_good_cos_oddUpTo theta R N with
    ⟨r, hNr, hcos, hnonzero⟩
  refine ⟨2 ^ r, ?_, ⟨r, rfl⟩, ?_, hcos, ?_⟩
  · exact hNr.trans (Nat.lt_two_pow_self (n := r)).le
  · exact Nat.pow_pos (by norm_num : 0 < 2)
  · intro s hs
    exact hnonzero s hs

/-- Primitive numerator indices for order `d`. -/
def primIdx (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter fun k => Nat.Coprime (2 * k + 1) d

lemma mem_primIdx_iff {d k : ℕ} :
    k ∈ primIdx d ↔ k < d ∧ Nat.Coprime (2 * k + 1) d := by
  simp [primIdx]

lemma odd_coprime_pow_two {a r : ℕ} (ha : Odd a) :
    Nat.Coprime a (2 ^ r) := by
  rcases r with _ | r
  · simp
  · rw [Nat.coprime_pow_right_iff (Nat.succ_pos r)]
    exact Nat.coprime_two_right.mpr ha

lemma odd_num_coprime_pow_two (k r : ℕ) :
    Nat.Coprime (2 * k + 1) (2 ^ r) :=
  odd_coprime_pow_two (odd_two_mul_add_one k)

lemma IsPowTwo.odd_num_coprime {n k : ℕ} (hn : IsPowTwo n) :
    Nat.Coprime (2 * k + 1) n := by
  rcases hn with ⟨r, rfl⟩
  exact odd_num_coprime_pow_two k r

lemma coprime_odd_num_mul_powTwo_iff
    {n s k : ℕ} (hn : IsPowTwo n) :
    Nat.Coprime (2 * k + 1) (n * s) ↔
      Nat.Coprime (2 * k + 1) s := by
  constructor
  · intro h
    exact (h.symm.coprime_mul_left).symm
  · intro h
    exact (hn.odd_num_coprime (k := k)).mul_right h

lemma mem_primIdx_mul_powTwo_iff
    {n s k : ℕ} (hn : IsPowTwo n) :
    k ∈ primIdx (n * s) ↔
      k < n * s ∧ Nat.Coprime (2 * k + 1) s := by
  rw [mem_primIdx_iff, coprime_odd_num_mul_powTwo_iff hn]

lemma coprime_progression_odd_num (s t : ℕ) :
    Nat.Coprime (2 * (s * t) + 1) s := by
  have h :
      Nat.Coprime (s * (2 * t) + 1) s := by
    have hbase : Nat.Coprime 1 s := by simp
    exact (Nat.coprime_mul_left_add_left (m := 1) (n := s) (k := 2 * t)).mpr hbase
  convert h using 1
  ring

lemma progression_mem_primIdx_mul_powTwo
    {n s t : ℕ} (hn : IsPowTwo n) (hspos : 0 < s) (ht : t < n) :
    s * t ∈ primIdx (n * s) := by
  rw [mem_primIdx_mul_powTwo_iff hn]
  constructor
  · have hlt : s * t < s * n := Nat.mul_lt_mul_of_pos_left ht hspos
    simpa [Nat.mul_comm] using hlt
  · exact coprime_progression_odd_num s t

lemma progression_image_subset_primIdx_mul_powTwo
    {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s) :
    (Finset.range n).image (fun t => s * t) ⊆ primIdx (n * s) := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨t, ht, rfl⟩
  exact progression_mem_primIdx_mul_powTwo hn hspos (Finset.mem_range.mp ht)

lemma mul_left_injOn_range {n s : ℕ} (hspos : 0 < s) :
    Set.InjOn (fun t => s * t) (Finset.range n : Set ℕ) := by
  intro a _ha b _hb h
  exact Nat.mul_left_cancel hspos h

lemma thetaNode_progression_lt_mul {n s t : ℕ}
    (hspos : 0 < s) (ht : t < n) :
    s * t < n * s := by
  have hlt : s * t < s * n := Nat.mul_lt_mul_of_pos_left ht hspos
  simpa [Nat.mul_comm] using hlt

lemma thetaNode_progression_mem_angleI {n s t : ℕ}
    (hspos : 0 < s) (ht : t < n) :
    thetaNode (n * s) (s * t) ∈ AngleI :=
  thetaNode_mem_angleI (thetaNode_progression_lt_mul hspos ht)

lemma sin_thetaNode_progression_pos {n s t : ℕ}
    (hspos : 0 < s) (ht : t < n) :
    0 < Real.sin (thetaNode (n * s) (s * t)) :=
  sin_thetaNode_pos (thetaNode_progression_lt_mul hspos ht)

lemma thetaNode_progression_strictMonoOn {n s : ℕ} (hspos : 0 < s) :
    StrictMonoOn (fun t : ℕ => thetaNode (n * s) (s * t))
      (Finset.range n) := by
  intro a ha b hb hab
  have hak : s * a < n * s :=
    thetaNode_progression_lt_mul hspos (Finset.mem_range.mp ha)
  have hbk : s * b < n * s :=
    thetaNode_progression_lt_mul hspos (Finset.mem_range.mp hb)
  have hmul : s * a < s * b :=
    Nat.mul_lt_mul_of_pos_left hab hspos
  exact thetaNode_strictMonoOn (n * s)
    (Finset.mem_range.mpr hak) (Finset.mem_range.mpr hbk) hmul

lemma thetaNode_progression_eq_linear {n s t : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    thetaNode (n * s) (s * t) =
      (t : ℝ) * (Real.pi / (n : ℝ)) +
        Real.pi / (2 * ((n * s : ℕ) : ℝ)) := by
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hspos)
  unfold thetaNode
  field_simp [hnne, hsne]
  norm_num [Nat.cast_mul]
  ring

lemma thetaNode_progression_succ_sub {n s t : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    thetaNode (n * s) (s * (t + 1)) -
        thetaNode (n * s) (s * t) =
      Real.pi / (n : ℝ) := by
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hspos)
  unfold thetaNode
  field_simp [hnne, hsne]
  norm_num [Nat.cast_mul, Nat.cast_add]
  ring

lemma thetaNode_progression_le_pi_div_two_of_lt_half {n s t : ℕ}
    (hspos : 0 < s) (ht : t < n / 2) :
    thetaNode (n * s) (s * t) ≤ Real.pi / 2 := by
  have hdpos_nat : 0 < n * s := by
    have hnpos : 0 < n := by omega
    exact Nat.mul_pos hnpos hspos
  have hdpos : 0 < ((n * s : ℕ) : ℝ) := by exact_mod_cast hdpos_nat
  have hnum_le_nat : 2 * (s * t) + 1 ≤ n * s := by
    have h2t : 2 * t + 1 ≤ n := by omega
    nlinarith [Nat.mul_le_mul_right s h2t, hspos]
  have hnum_le : 2 * ((s * t : ℕ) : ℝ) + 1 ≤ ((n * s : ℕ) : ℝ) := by
    exact_mod_cast hnum_le_nat
  unfold thetaNode
  calc
    ((2 * ((s * t : ℕ) : ℝ) + 1) * Real.pi) /
        (2 * ((n * s : ℕ) : ℝ))
        ≤ (((n * s : ℕ) : ℝ) * Real.pi) /
            (2 * ((n * s : ℕ) : ℝ)) := by gcongr
    _ = Real.pi / 2 := by field_simp [ne_of_gt hdpos]

lemma thetaNode_progression_le_succ_mul_pi_div {n s t : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    thetaNode (n * s) (s * t) ≤
      ((t + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
  have hnpos_real : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hspos_real : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hnum_le_nat : 2 * (s * t) + 1 ≤ 2 * s * (t + 1) := by
    have h1 : 1 ≤ 2 * s := by omega
    nlinarith
  have hnum_le :
      2 * ((s * t : ℕ) : ℝ) + 1 ≤
        2 * (s : ℝ) * ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnum_le_nat
  unfold thetaNode
  calc
    ((2 * ((s * t : ℕ) : ℝ) + 1) * Real.pi) /
        (2 * ((n * s : ℕ) : ℝ))
        ≤ ((2 * (s : ℝ) * ((t + 1 : ℕ) : ℝ)) * Real.pi) /
            (2 * ((n * s : ℕ) : ℝ)) := by gcongr
    _ = ((t + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
        field_simp [ne_of_gt hnpos_real, ne_of_gt hspos_real]
        norm_num [Nat.cast_mul]
        ring

lemma thetaNode_progression_ge_mul_pi_div {n s t : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    (t : ℝ) * Real.pi / (n : ℝ) ≤ thetaNode (n * s) (s * t) := by
  rw [thetaNode_progression_eq_linear hnpos hspos]
  have hnonneg : 0 ≤ Real.pi / (2 * (((n * s : ℕ) : ℝ))) := by
    positivity
  calc
    (t : ℝ) * Real.pi / (n : ℝ) =
        (t : ℝ) * (Real.pi / (n : ℝ)) := by ring
    _ ≤ (t : ℝ) * (Real.pi / (n : ℝ)) +
        Real.pi / (2 * (((n * s : ℕ) : ℝ))) :=
      le_add_of_nonneg_right hnonneg

lemma floor_scaled_theta0_mul_pi_div_le
    {theta0 : ℝ} {n : ℕ} (htheta0_nonneg : 0 ≤ theta0)
    (hnpos : 0 < n) :
    ((Nat.floor (((n : ℝ) * theta0) / Real.pi) : ℕ) : ℝ) *
        Real.pi / (n : ℝ) ≤ theta0 := by
  let x : ℝ := ((n : ℝ) * theta0) / Real.pi
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx_nonneg
  have hscale_nonneg : 0 ≤ Real.pi / (n : ℝ) := by
    positivity
  have hmul :
      ((Nat.floor x : ℕ) : ℝ) * (Real.pi / (n : ℝ)) ≤
        x * (Real.pi / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hfloor hscale_nonneg
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hxscale : x * (Real.pi / (n : ℝ)) = theta0 := by
    dsimp [x]
    field_simp [Real.pi_ne_zero, hnne]
  change ((Nat.floor x : ℕ) : ℝ) * Real.pi / (n : ℝ) ≤ theta0
  calc
    ((Nat.floor x : ℕ) : ℝ) * Real.pi / (n : ℝ) =
        ((Nat.floor x : ℕ) : ℝ) * (Real.pi / (n : ℝ)) := by ring
    _ ≤ x * (Real.pi / (n : ℝ)) := hmul
    _ = theta0 := hxscale

lemma theta0_lt_floor_scaled_succ_mul_pi_div
    {theta0 : ℝ} {n : ℕ} (hnpos : 0 < n) :
    theta0 <
      (((Nat.floor (((n : ℝ) * theta0) / Real.pi) + 1 : ℕ) : ℝ) *
        Real.pi / (n : ℝ)) := by
  let x : ℝ := ((n : ℝ) * theta0) / Real.pi
  have hfloor : x < (Nat.floor x : ℕ) + 1 :=
    Nat.lt_floor_add_one x
  have hscale_pos : 0 < Real.pi / (n : ℝ) := by
    positivity
  have hmul :
      x * (Real.pi / (n : ℝ)) <
        (((Nat.floor x : ℕ) : ℝ) + 1) *
          (Real.pi / (n : ℝ)) :=
    mul_lt_mul_of_pos_right hfloor hscale_pos
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hxscale : x * (Real.pi / (n : ℝ)) = theta0 := by
    dsimp [x]
    field_simp [Real.pi_ne_zero, hnne]
  change theta0 <
    (((Nat.floor x + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ))
  calc
    theta0 = x * (Real.pi / (n : ℝ)) := hxscale.symm
    _ < (((Nat.floor x : ℕ) : ℝ) + 1) *
          (Real.pi / (n : ℝ)) := hmul
    _ = (((Nat.floor x + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) := by
        norm_num [Nat.cast_add]
        ring

lemma interior_floor_shift_distance_bound
    {theta0 : ℝ} {n s q : ℕ}
    (htheta0_nonneg : 0 ≤ theta0) (hnpos : 0 < n) (hspos : 0 < s) :
    let m : ℕ := Nat.floor (((n : ℝ) * theta0) / Real.pi)
    |thetaNode (n * s) (s * (m + q)) - theta0| ≤
      ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
  intro m
  subst m
  have hnode_low :=
    thetaNode_progression_ge_mul_pi_div (n := n) (s := s)
      (t := Nat.floor (((n : ℝ) * theta0) / Real.pi) + q)
      hnpos hspos
  have hnode_up :=
    thetaNode_progression_le_succ_mul_pi_div (n := n) (s := s)
      (t := Nat.floor (((n : ℝ) * theta0) / Real.pi) + q)
      hnpos hspos
  have htheta_low :=
    floor_scaled_theta0_mul_pi_div_le (theta0 := theta0) (n := n)
      htheta0_nonneg hnpos
  have htheta_up :=
    theta0_lt_floor_scaled_succ_mul_pi_div (theta0 := theta0)
      (n := n) hnpos
  rw [abs_le]
  constructor
  · have hdiff_left :
        (((Nat.floor (((n : ℝ) * theta0) / Real.pi) + 1 : ℕ) : ℝ) *
              Real.pi / (n : ℝ)) -
            (((Nat.floor (((n : ℝ) * theta0) / Real.pi) + q : ℕ) : ℝ) *
              Real.pi / (n : ℝ)) ≤
          ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
      norm_num [Nat.cast_add]
      ring_nf
      have htail : 0 ≤ Real.pi * (n : ℝ)⁻¹ * (q : ℝ) * 2 := by
        positivity
      nlinarith
    nlinarith
  · have hdiff :
        (((Nat.floor (((n : ℝ) * theta0) / Real.pi) + q + 1 : ℕ) : ℝ) *
              Real.pi / (n : ℝ)) -
            ((Nat.floor (((n : ℝ) * theta0) / Real.pi) : ℕ) : ℝ) *
              Real.pi / (n : ℝ) =
          ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
      norm_num [Nat.cast_add]
      ring
    nlinarith

lemma floor_shift_range_of_add_le {theta0 : ℝ} {n M q : ℕ}
    (hrangeM : Nat.floor (((n : ℝ) * theta0) / Real.pi) + M ≤ n)
    (hq : q < M) :
    Nat.floor (((n : ℝ) * theta0) / Real.pi) + q < n := by
  omega

lemma floor_shift_distance_lt_of_lt
    {theta0 rho : ℝ} {n s M q : ℕ}
    (htheta0_nonneg : 0 ≤ theta0) (hnpos : 0 < n) (hspos : 0 < s)
    (hq : q < M) (hclose : (M : ℝ) * Real.pi / (n : ℝ) < rho) :
    |thetaNode (n * s)
        (s * (Nat.floor (((n : ℝ) * theta0) / Real.pi) + q)) -
        theta0| < rho := by
  have hdist :=
    interior_floor_shift_distance_bound
      (theta0 := theta0) (n := n) (s := s) (q := q)
      htheta0_nonneg hnpos hspos
  change |thetaNode (n * s)
        (s * (Nat.floor (((n : ℝ) * theta0) / Real.pi) + q)) -
        theta0| ≤
      ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) at hdist
  have hqM_nat : q + 1 ≤ M := Nat.succ_le_of_lt hq
  have hqM : ((q + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hqM_nat
  have hscale_nonneg : 0 ≤ Real.pi / (n : ℝ) := by
    positivity
  have hgrid :
      ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) ≤
        (M : ℝ) * Real.pi / (n : ℝ) := by
    calc
      ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) =
          ((q + 1 : ℕ) : ℝ) * (Real.pi / (n : ℝ)) := by ring
      _ ≤ (M : ℝ) * (Real.pi / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hqM hscale_nonneg
      _ = (M : ℝ) * Real.pi / (n : ℝ) := by ring
  exact lt_of_le_of_lt (hdist.trans hgrid) hclose

lemma floor_shift_range_div_of_add_inv_le
    {theta0 : ℝ} {n Q : ℕ}
    (htheta0_nonneg : 0 ≤ theta0)
    (hrange : theta0 / Real.pi + 1 / (Q : ℝ) ≤ 1) :
    Nat.floor (((n : ℝ) * theta0) / Real.pi) + n / Q ≤ n := by
  let x : ℝ := ((n : ℝ) * theta0) / Real.pi
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx_nonneg
  have hdiv : ((n / Q : ℕ) : ℝ) ≤ (n : ℝ) / (Q : ℝ) :=
    Nat.cast_div_le
  have hsum_real :
      ((Nat.floor x + n / Q : ℕ) : ℝ) ≤ (n : ℝ) := by
    calc
      ((Nat.floor x + n / Q : ℕ) : ℝ) =
          ((Nat.floor x : ℕ) : ℝ) + ((n / Q : ℕ) : ℝ) := by
            norm_num
      _ ≤ x + (n : ℝ) / (Q : ℝ) := add_le_add hfloor hdiv
      _ = (n : ℝ) * (theta0 / Real.pi + 1 / (Q : ℝ)) := by
          dsimp [x]
          ring
      _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hrange (by positivity)
      _ = (n : ℝ) := by ring
  exact_mod_cast hsum_real

lemma div_block_close_of_pi_div_lt
    {rho : ℝ} {n Q : ℕ}
    (hnpos : 0 < n) (hQpos : 0 < Q)
    (hQrho : Real.pi / (Q : ℝ) < rho) :
    ((n / Q : ℕ) : ℝ) * Real.pi / (n : ℝ) < rho := by
  have hdiv : ((n / Q : ℕ) : ℝ) ≤ (n : ℝ) / (Q : ℝ) :=
    Nat.cast_div_le
  have hscale_nonneg : 0 ≤ Real.pi / (n : ℝ) := by
    positivity
  have hle :
      ((n / Q : ℕ) : ℝ) * Real.pi / (n : ℝ) ≤
        ((n : ℝ) / (Q : ℝ)) * Real.pi / (n : ℝ) := by
    calc
      ((n / Q : ℕ) : ℝ) * Real.pi / (n : ℝ) =
          ((n / Q : ℕ) : ℝ) * (Real.pi / (n : ℝ)) := by ring
      _ ≤ ((n : ℝ) / (Q : ℝ)) * (Real.pi / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hdiv hscale_nonneg
      _ = ((n : ℝ) / (Q : ℝ)) * Real.pi / (n : ℝ) := by ring
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hQne : (Q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hQpos)
  have hright :
      ((n : ℝ) / (Q : ℝ)) * Real.pi / (n : ℝ) =
        Real.pi / (Q : ℝ) := by
    field_simp [hnne, hQne]
  exact lt_of_le_of_lt (by simpa [hright] using hle) hQrho

lemma grid_inv_le_inv_thetaNode_progression {n s t : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (ht : t < n) :
    (n : ℝ) / (((t + 1 : ℕ) : ℝ) * Real.pi) ≤
      1 / thetaNode (n * s) (s * t) := by
  have htheta_pos : 0 < thetaNode (n * s) (s * t) := by
    exact thetaNode_pos (thetaNode_progression_lt_mul hspos ht)
  have hupper := thetaNode_progression_le_succ_mul_pi_div
    (n := n) (s := s) (t := t) hnpos hspos
  have h := one_div_le_one_div_of_le htheta_pos hupper
  have heq :
      1 / (((t + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) =
        (n : ℝ) / (((t + 1 : ℕ) : ℝ) * Real.pi) := by
    field_simp
      [ne_of_gt (by positivity :
        0 < ((t + 1 : ℕ) : ℝ) * Real.pi),
       ne_of_gt (by positivity : 0 < (n : ℝ))]
  simpa [heq] using h

lemma one_sub_cos_eq_two_sin_sq_half (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have hs : Real.sin (x / 2) ^ 2 = 1 / 2 - Real.cos x / 2 := by
    have hangle : 2 * (x / 2) = x := by ring
    have := Real.sin_sq_eq_half_sub (x / 2)
    rw [hangle] at this
    simpa using this
  nlinarith

lemma one_sub_cos_le_sq_half (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  have hid := one_sub_cos_eq_two_sin_sq_half x
  have hsin_abs : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have hsin_sq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
    rw [← sq_abs, ← sq_abs (x / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) hsin_abs 2
  rw [hid]
  nlinarith

lemma zero_endpoint_kernel_ge_inv {theta : ℝ}
    (hpos : 0 < theta) (hle : theta ≤ Real.pi / 2) :
    1 / theta ≤ Real.sin theta / |1 - Real.cos theta| := by
  have hle_pi : theta ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcoslt : Real.cos theta < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := theta)
      (le_refl 0) hle_pi hpos
    simpa using h
  have hdenpos_raw : 0 < 1 - Real.cos theta := sub_pos.mpr hcoslt
  have hdenpos : 0 < |1 - Real.cos theta| := by
    rwa [abs_of_pos hdenpos_raw]
  rw [le_div_iff₀ hdenpos]
  have hden_le : |1 - Real.cos theta| ≤ theta ^ 2 / 2 := by
    rw [abs_of_pos hdenpos_raw]
    exact one_sub_cos_le_sq_half theta
  have hinv_nonneg : 0 ≤ 1 / theta := by positivity
  have hmul_le : (1 / theta) * |1 - Real.cos theta| ≤
      (1 / theta) * (theta ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hden_le hinv_nonneg
  have hsimpl : (1 / theta) * (theta ^ 2 / 2) = theta / 2 := by
    field_simp [ne_of_gt hpos]
  have hhalf_const : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_le_four]
  have hhalf_le : theta / 2 ≤ (2 / Real.pi) * theta := by
    have htheta_nonneg : 0 ≤ theta := le_of_lt hpos
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hhalf_const htheta_nonneg
  have hsin_lower : (2 / Real.pi) * theta ≤ Real.sin theta :=
    Real.mul_le_sin (le_of_lt hpos) hle
  calc
    (1 / theta) * |1 - Real.cos theta| ≤
        (1 / theta) * (theta ^ 2 / 2) := hmul_le
    _ = theta / 2 := hsimpl
    _ ≤ (2 / Real.pi) * theta := hhalf_le
    _ ≤ Real.sin theta := hsin_lower

lemma pi_endpoint_kernel_ge_inv {theta : ℝ}
    (hlt : theta < Real.pi) (hhalf : Real.pi / 2 ≤ theta) :
    1 / (Real.pi - theta) ≤
      Real.sin theta / |Real.cos Real.pi - Real.cos theta| := by
  have hpos : 0 < Real.pi - theta := sub_pos.mpr hlt
  have hle : Real.pi - theta ≤ Real.pi / 2 := by linarith
  have h := zero_endpoint_kernel_ge_inv (theta := Real.pi - theta) hpos hle
  calc
    1 / (Real.pi - theta) ≤
        Real.sin (Real.pi - theta) /
          |1 - Real.cos (Real.pi - theta)| := h
    _ = Real.sin theta / |Real.cos Real.pi - Real.cos theta| := by
        rw [Real.sin_pi_sub, Real.cos_pi_sub, Real.cos_pi]
        have habs : |1 + Real.cos theta| = |-1 - Real.cos theta| := by
          rw [← abs_neg (1 + Real.cos theta)]
          ring_nf
        have hden : 1 - -Real.cos theta = 1 + Real.cos theta := by ring
        rw [hden, habs]

lemma sum_range_inv_nat_succ_eq_harmonic (M : ℕ) :
    (∑ t ∈ Finset.range M, (1 : ℝ) / ((t + 1 : ℕ) : ℝ)) =
      (harmonic M : ℝ) := by
  rw [harmonic]
  simp [Rat.cast_sum, one_div]

lemma log_nat_le_sum_range_inv_nat_succ (M : ℕ) :
    Real.log (M + 1 : ℝ) ≤
      ∑ t ∈ Finset.range M, (1 : ℝ) / ((t + 1 : ℕ) : ℝ) := by
  rw [sum_range_inv_nat_succ_eq_harmonic]
  simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic M

lemma zero_endpoint_progression_kernel_ge_grid_inv {n s t : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (ht : t < n / 2) :
    (n : ℝ) / (((t + 1 : ℕ) : ℝ) * Real.pi) ≤
      Real.sin (thetaNode (n * s) (s * t)) /
        |Real.cos 0 - Real.cos (thetaNode (n * s) (s * t))| := by
  have ht_n : t < n := by omega
  have hgrid := grid_inv_le_inv_thetaNode_progression hnpos hspos ht_n
  have htheta_pos : 0 < thetaNode (n * s) (s * t) :=
    thetaNode_pos (thetaNode_progression_lt_mul hspos ht_n)
  have htheta_le : thetaNode (n * s) (s * t) ≤ Real.pi / 2 :=
    thetaNode_progression_le_pi_div_two_of_lt_half hspos ht
  have hkernel := zero_endpoint_kernel_ge_inv htheta_pos htheta_le
  exact hgrid.trans (by simpa [Real.cos_zero] using hkernel)

lemma sum_range_half_grid_inv_le_zero_endpoint_kernel {n s : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    ∑ t ∈ Finset.range (n / 2),
        (n : ℝ) / (((t + 1 : ℕ) : ℝ) * Real.pi) ≤
      ∑ t ∈ Finset.range (n / 2),
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos 0 - Real.cos (thetaNode (n * s) (s * t))| := by
  exact Finset.sum_le_sum fun t ht =>
    zero_endpoint_progression_kernel_ge_grid_inv
      hnpos hspos (Finset.mem_range.mp ht)

lemma zero_endpoint_grid_half_lower_log (n : ℕ) :
    ((n : ℝ) / Real.pi) * Real.log (((n / 2) + 1 : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range (n / 2),
        (n : ℝ) / (((t + 1 : ℕ) : ℝ) * Real.pi) := by
  have hlog := log_nat_le_sum_range_inv_nat_succ (n / 2)
  have hcoef_nonneg : 0 ≤ (n : ℝ) / Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hcoef_nonneg
  calc
    ((n : ℝ) / Real.pi) * Real.log (((n / 2) + 1 : ℕ) : ℝ) ≤
        ((n : ℝ) / Real.pi) *
          (∑ t ∈ Finset.range (n / 2),
            (1 : ℝ) / ((t + 1 : ℕ) : ℝ)) := by
          simpa [Nat.cast_add, Nat.cast_one] using hscaled
    _ = ∑ t ∈ Finset.range (n / 2),
        (n : ℝ) / (((t + 1 : ℕ) : ℝ) * Real.pi) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _ht
          field_simp
            [ne_of_gt (by positivity : 0 < ((t + 1 : ℕ) : ℝ)),
             ne_of_gt Real.pi_pos]

lemma zero_endpoint_kernel_sum_first_half_ge_log {n s : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    ((n : ℝ) / Real.pi) * Real.log (((n / 2) + 1 : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range (n / 2),
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos 0 - Real.cos (thetaNode (n * s) (s * t))| := by
  exact (zero_endpoint_grid_half_lower_log n).trans
    (sum_range_half_grid_inv_le_zero_endpoint_kernel hnpos hspos)

lemma zero_endpoint_kernel_sum_range_ge_log {n s : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    ((n : ℝ) / Real.pi) * Real.log (((n / 2) + 1 : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos 0 - Real.cos (thetaNode (n * s) (s * t))| := by
  refine (zero_endpoint_kernel_sum_first_half_ge_log hnpos hspos).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro t ht
      have hthalf : t < n / 2 := Finset.mem_range.mp ht
      exact Finset.mem_range.mpr (by omega))
    (by
      intro t htn _ht_not_half
      have ht : t < n := Finset.mem_range.mp htn
      exact div_nonneg
        (le_of_lt (sin_thetaNode_progression_pos hspos ht))
        (abs_nonneg _))

lemma nat_le_half_add_one_sq {n : ℕ} (hn : 4 ≤ n) :
    n ≤ (n / 2 + 1) ^ 2 := by
  let q := n / 2
  have hnlt : n < q * 2 + 2 := by
    simpa [q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.lt_div_mul_add (a := n) (b := 2) (by norm_num : 0 < 2))
  have hq2 : 2 ≤ q + 1 := by
    have hq : 2 ≤ q := by
      dsimp [q]
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
    omega
  have h2m : 2 * (q + 1) ≤ (q + 1) ^ 2 := by
    simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right (q + 1) hq2
  have hlt_sq : n < (q + 1) ^ 2 := by
    calc
      n < q * 2 + 2 := hnlt
      _ = 2 * (q + 1) := by omega
      _ ≤ (q + 1) ^ 2 := h2m
  change n ≤ (q + 1) ^ 2
  exact Nat.le_of_lt hlt_sq

lemma log_nat_le_two_log_half_add_one {n : ℕ} (hn : 4 ≤ n) :
    Real.log (n : ℝ) ≤
      2 * Real.log (((n / 2) + 1 : ℕ) : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) hn)
  have hle_nat : n ≤ (n / 2 + 1) ^ 2 := nat_le_half_add_one_sq hn
  have hle_real : (n : ℝ) ≤ (((n / 2 + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hle_nat
  have hlog := Real.log_le_log hnpos hle_real
  have hpow : (((n / 2 + 1) ^ 2 : ℕ) : ℝ) =
      (((n / 2) + 1 : ℕ) : ℝ) ^ 2 := by norm_num
  rw [hpow, Real.log_pow] at hlog
  norm_num at hlog
  simpa [Nat.cast_add, Nat.cast_one] using hlog

lemma nat_le_div_add_one_sq_of_sq_le {n Q : ℕ}
    (hQpos : 0 < Q) (hnlarge : Q ^ 2 ≤ n) :
    n ≤ (n / Q + 1) ^ 2 := by
  let q := n / Q
  have hnlt : n < q * Q + Q := by
    simpa [q, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.lt_div_mul_add (a := n) (b := Q) hQpos)
  have hQ_le_q : Q ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hQpos).mpr
      (by simpa [pow_two] using hnlarge)
  have hQ_le_q1 : Q ≤ q + 1 :=
    Nat.le_trans hQ_le_q (Nat.le_succ q)
  have hmul : Q * (q + 1) ≤ (q + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right (q + 1) hQ_le_q1
  have hnlt_sq : n < (q + 1) ^ 2 := by
    calc
      n < q * Q + Q := hnlt
      _ = Q * (q + 1) := by ring
      _ ≤ (q + 1) ^ 2 := hmul
  change n ≤ (q + 1) ^ 2
  exact Nat.le_of_lt hnlt_sq

lemma log_nat_le_two_log_div_add_one {n Q : ℕ}
    (hQpos : 0 < Q) (hnlarge : Q ^ 2 ≤ n) :
    Real.log (n : ℝ) ≤
      2 * Real.log (((n / Q) + 1 : ℕ) : ℝ) := by
  have hnpos_nat : 0 < n := by
    exact lt_of_lt_of_le (pow_pos hQpos 2) hnlarge
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  have hle_nat := nat_le_div_add_one_sq_of_sq_le hQpos hnlarge
  have hle_real : (n : ℝ) ≤ ((((n / Q + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hle_nat
  have hlog := Real.log_le_log hnpos hle_real
  have hpow : ((((n / Q + 1) ^ 2 : ℕ) : ℝ)) =
      (((n / Q) + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num
  rw [hpow, Real.log_pow] at hlog
  simpa [Nat.cast_add, Nat.cast_one] using hlog

lemma zero_endpoint_kernel_sum_range_ge_base_log {n s : ℕ}
    (hn4 : 4 ≤ n) (hspos : 0 < s) :
    (1 / (2 * Real.pi)) * (n : ℝ) * Real.log (n : ℝ) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos 0 - Real.cos (thetaNode (n * s) (s * t))| := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn4
  have hlog := log_nat_le_two_log_half_add_one hn4
  have hhalf :
      Real.log (n : ℝ) / 2 ≤
        Real.log (((n / 2) + 1 : ℕ) : ℝ) := by
    nlinarith
  have hcoef_nonneg : 0 ≤ (n : ℝ) / Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hhalf hcoef_nonneg
  have hleft_eq :
      (1 / (2 * Real.pi)) * (n : ℝ) * Real.log (n : ℝ) =
        ((n : ℝ) / Real.pi) * (Real.log (n : ℝ) / 2) := by
    ring
  rw [hleft_eq]
  exact hscaled.trans (zero_endpoint_kernel_sum_range_ge_log hnpos hspos)

lemma pi_sub_thetaNode_progression_mirror_le_succ_mul_pi_div
    {n s q : ℕ} (hnpos : 0 < n) (hspos : 0 < s)
    (hq : q < n / 2) :
    Real.pi - thetaNode (n * s) (s * (n - 1 - q)) ≤
      ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnpos
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hspos
  have hq_lt_n : q < n := by omega
  have hcast_sub :
      ((n - 1 - q : ℕ) : ℝ) = (n : ℝ) - 1 - (q : ℝ) := by
    rw [Nat.cast_sub (by omega : q ≤ n - 1),
      Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  unfold thetaNode
  simp only [Nat.cast_mul, hcast_sub]
  field_simp [hnne, hsne]
  norm_num [Nat.cast_add]
  nlinarith [Real.pi_pos]

lemma pi_div_two_le_thetaNode_progression_mirror_of_lt_half
    {n s q : ℕ} (hspos : 0 < s) (hq : q < n / 2) :
    Real.pi / 2 ≤ thetaNode (n * s) (s * (n - 1 - q)) := by
  have hnpos : 0 < n := by omega
  have hdpos : 0 < ((n * s : ℕ) : ℝ) := by positivity
  have hnum_ge_nat : n * s ≤ 2 * (s * (n - 1 - q)) + 1 := by
    have ht_ge : n ≤ 2 * (n - 1 - q) := by omega
    nlinarith [Nat.mul_le_mul_right s ht_ge, hspos]
  have hnum_ge :
      ((n * s : ℕ) : ℝ) ≤
        2 * ((s * (n - 1 - q) : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnum_ge_nat
  unfold thetaNode
  calc
    Real.pi / 2 = (((n * s : ℕ) : ℝ) * Real.pi) /
        (2 * ((n * s : ℕ) : ℝ)) := by field_simp [ne_of_gt hdpos]
    _ ≤ ((2 * ((s * (n - 1 - q) : ℕ) : ℝ) + 1) *
          Real.pi) / (2 * ((n * s : ℕ) : ℝ)) := by gcongr

lemma grid_inv_le_inv_pi_sub_thetaNode_progression_mirror
    {n s q : ℕ} (hnpos : 0 < n) (hspos : 0 < s)
    (hq : q < n / 2) :
    (n : ℝ) / (((q + 1 : ℕ) : ℝ) * Real.pi) ≤
      1 / (Real.pi - thetaNode (n * s) (s * (n - 1 - q))) := by
  have ht_lt : s * (n - 1 - q) < n * s := by
    have hmir : n - 1 - q < n := by omega
    have hlt : s * (n - 1 - q) < s * n :=
      Nat.mul_lt_mul_of_pos_left hmir hspos
    simpa [Nat.mul_comm] using hlt
  have htheta_lt : thetaNode (n * s) (s * (n - 1 - q)) < Real.pi :=
    thetaNode_lt_pi ht_lt
  have hdenpos : 0 < Real.pi - thetaNode (n * s) (s * (n - 1 - q)) :=
    sub_pos.mpr htheta_lt
  have hupper := pi_sub_thetaNode_progression_mirror_le_succ_mul_pi_div
    (n := n) (s := s) (q := q) hnpos hspos hq
  have h := one_div_le_one_div_of_le hdenpos hupper
  have heq :
      1 / (((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) =
        (n : ℝ) / (((q + 1 : ℕ) : ℝ) * Real.pi) := by
    field_simp
      [ne_of_gt (by positivity :
        0 < ((q + 1 : ℕ) : ℝ) * Real.pi),
       ne_of_gt (by positivity : 0 < (n : ℝ))]
  simpa [heq] using h

lemma pi_endpoint_progression_kernel_ge_grid_inv
    {n s q : ℕ} (hnpos : 0 < n) (hspos : 0 < s)
    (hq : q < n / 2) :
    (n : ℝ) / (((q + 1 : ℕ) : ℝ) * Real.pi) ≤
      Real.sin (thetaNode (n * s) (s * (n - 1 - q))) /
        |Real.cos Real.pi -
          Real.cos (thetaNode (n * s) (s * (n - 1 - q)))| := by
  have hgrid :=
    grid_inv_le_inv_pi_sub_thetaNode_progression_mirror hnpos hspos hq
  have ht_lt : s * (n - 1 - q) < n * s := by
    have hmir : n - 1 - q < n := by omega
    have hlt : s * (n - 1 - q) < s * n :=
      Nat.mul_lt_mul_of_pos_left hmir hspos
    simpa [Nat.mul_comm] using hlt
  have htheta_lt : thetaNode (n * s) (s * (n - 1 - q)) < Real.pi :=
    thetaNode_lt_pi ht_lt
  have htheta_half :
      Real.pi / 2 ≤ thetaNode (n * s) (s * (n - 1 - q)) :=
    pi_div_two_le_thetaNode_progression_mirror_of_lt_half hspos hq
  have hkernel := pi_endpoint_kernel_ge_inv htheta_lt htheta_half
  exact hgrid.trans hkernel

lemma mirror_injOn_range_half (n : ℕ) :
    Set.InjOn (fun q : ℕ => n - 1 - q)
      (Finset.range (n / 2) : Set ℕ) := by
  intro a ha b hb h
  have ha_lt : a < n := by
    have : a < n / 2 := Finset.mem_range.mp ha
    omega
  have hb_lt : b < n := by
    have : b < n / 2 := Finset.mem_range.mp hb
    omega
  have ha_le : a ≤ n - 1 := Nat.le_sub_one_of_lt ha_lt
  have hb_le : b ≤ n - 1 := Nat.le_sub_one_of_lt hb_lt
  have h1 : n - 1 = (n - 1 - b) + a := by
    exact (Nat.sub_eq_iff_eq_add ha_le).mp h
  have h2 : n - 1 = (n - 1 - b) + b := by
    exact (Nat.sub_eq_iff_eq_add hb_le).mp rfl
  omega

lemma sum_range_half_grid_inv_le_pi_endpoint_kernel_mirror {n s : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    ∑ q ∈ Finset.range (n / 2),
        (n : ℝ) / (((q + 1 : ℕ) : ℝ) * Real.pi) ≤
      ∑ q ∈ Finset.range (n / 2),
        Real.sin (thetaNode (n * s) (s * (n - 1 - q))) /
          |Real.cos Real.pi -
            Real.cos (thetaNode (n * s) (s * (n - 1 - q)))| := by
  exact Finset.sum_le_sum fun q hq =>
    pi_endpoint_progression_kernel_ge_grid_inv
      hnpos hspos (Finset.mem_range.mp hq)

lemma pi_endpoint_kernel_sum_range_ge_log {n s : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) :
    ((n : ℝ) / Real.pi) * Real.log (((n / 2) + 1 : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos Real.pi - Real.cos (thetaNode (n * s) (s * t))| := by
  refine (zero_endpoint_grid_half_lower_log n).trans ?_
  refine (sum_range_half_grid_inv_le_pi_endpoint_kernel_mirror hnpos hspos).trans ?_
  let f : ℕ → ℝ := fun t =>
    Real.sin (thetaNode (n * s) (s * t)) /
      |Real.cos Real.pi - Real.cos (thetaNode (n * s) (s * t))|
  have himage_subset :
      (Finset.range (n / 2)).image (fun q => n - 1 - q) ⊆
        Finset.range n := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨q, hq, rfl⟩
    have hqhalf : q < n / 2 := Finset.mem_range.mp hq
    exact Finset.mem_range.mpr (by omega)
  calc
    ∑ q ∈ Finset.range (n / 2),
        Real.sin (thetaNode (n * s) (s * (n - 1 - q))) /
          |Real.cos Real.pi -
            Real.cos (thetaNode (n * s) (s * (n - 1 - q)))| =
        ∑ t ∈ (Finset.range (n / 2)).image (fun q => n - 1 - q),
          f t := by
          exact (Finset.sum_image (s := Finset.range (n / 2))
            (g := fun q => n - 1 - q) (f := f)
            (mirror_injOn_range_half n)).symm
    _ ≤ ∑ t ∈ Finset.range n, f t := by
        exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
          (by
            intro t htn _htnot
            have ht : t < n := Finset.mem_range.mp htn
            exact div_nonneg
              (le_of_lt (sin_thetaNode_progression_pos hspos ht))
              (abs_nonneg _))

lemma pi_endpoint_kernel_sum_range_ge_base_log {n s : ℕ}
    (hn4 : 4 ≤ n) (hspos : 0 < s) :
    (1 / (2 * Real.pi)) * (n : ℝ) * Real.log (n : ℝ) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos Real.pi - Real.cos (thetaNode (n * s) (s * t))| := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn4
  have hlog := log_nat_le_two_log_half_add_one hn4
  have hhalf :
      Real.log (n : ℝ) / 2 ≤
        Real.log (((n / 2) + 1 : ℕ) : ℝ) := by
    nlinarith
  have hcoef_nonneg : 0 ≤ (n : ℝ) / Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hhalf hcoef_nonneg
  have hleft_eq :
      (1 / (2 * Real.pi)) * (n : ℝ) * Real.log (n : ℝ) =
        ((n : ℝ) / Real.pi) * (Real.log (n : ℝ) / 2) := by
    ring
  rw [hleft_eq]
  exact hscaled.trans (pi_endpoint_kernel_sum_range_ge_log hnpos hspos)

lemma sin_ge_two_div_pi_mul_of_core {rho theta : ℝ}
    (hleft : rho ≤ theta) (hright : rho ≤ Real.pi - theta)
    (htheta : theta ∈ AngleI) :
    (2 / Real.pi) * rho ≤ Real.sin theta := by
  by_cases hhalf : theta ≤ Real.pi / 2
  · have hcoef_nonneg : 0 ≤ 2 / Real.pi := by positivity
    have hmul : (2 / Real.pi) * rho ≤ (2 / Real.pi) * theta :=
      mul_le_mul_of_nonneg_left hleft hcoef_nonneg
    exact hmul.trans (Real.mul_le_sin htheta.1 hhalf)
  · have hy_nonneg : 0 ≤ Real.pi - theta := sub_nonneg.mpr htheta.2
    have hy_le : Real.pi - theta ≤ Real.pi / 2 := by
      have hhalf_le : Real.pi / 2 ≤ theta := le_of_not_ge hhalf
      linarith
    have hcoef_nonneg : 0 ≤ 2 / Real.pi := by positivity
    have hmul :
        (2 / Real.pi) * rho ≤
          (2 / Real.pi) * (Real.pi - theta) :=
      mul_le_mul_of_nonneg_left hright hcoef_nonneg
    have hsin := Real.mul_le_sin hy_nonneg hy_le
    rw [Real.sin_pi_sub] at hsin
    exact hmul.trans hsin

lemma exists_interior_kernel_lower_bound
    {theta0 : ℝ} (h0 : 0 < theta0) (hpi : theta0 < Real.pi) :
    ∃ c > 0, ∃ rho > 0,
      ∀ theta ∈ AngleI, theta ≠ theta0 → |theta - theta0| < rho →
        c / |theta - theta0| ≤
          Real.sin theta / |Real.cos theta0 - Real.cos theta| := by
  let rho : ℝ := min theta0 (Real.pi - theta0) / 2
  let c : ℝ := (2 / Real.pi) * rho
  have htheta0 : theta0 ∈ AngleI := ⟨le_of_lt h0, le_of_lt hpi⟩
  have hpi_sub_pos : 0 < Real.pi - theta0 := sub_pos.mpr hpi
  have hmin_pos : 0 < min theta0 (Real.pi - theta0) :=
    lt_min h0 hpi_sub_pos
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    exact half_pos hmin_pos
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hcpos, rho, hrho_pos, ?_⟩
  intro theta htheta hne hdist
  have hrho_le_theta0_half : rho ≤ theta0 / 2 := by
    dsimp [rho]
    exact div_le_div_of_nonneg_right
      (min_le_left theta0 (Real.pi - theta0)) (by norm_num)
  have hrho_le_pi_sub_half : rho ≤ (Real.pi - theta0) / 2 := by
    dsimp [rho]
    exact div_le_div_of_nonneg_right
      (min_le_right theta0 (Real.pi - theta0)) (by norm_num)
  have hdist_pair := abs_lt.mp hdist
  have htheta_lower : theta0 - rho < theta := by linarith
  have htheta_upper : theta < theta0 + rho := by linarith
  have hleft : rho ≤ theta := by nlinarith
  have hright : rho ≤ Real.pi - theta := by nlinarith
  have hc_le_sin : c ≤ Real.sin theta := by
    dsimp [c]
    exact sin_ge_two_div_pi_mul_of_core hleft hright htheta
  have hdist_pos : 0 < |theta - theta0| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  have hcos_den_ne : Real.cos theta0 - Real.cos theta ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hcos
    have htheta_eq : theta0 = theta := Real.injOn_cos htheta0 htheta hcos
    exact hne htheta_eq.symm
  have hcos_den_pos : 0 < |Real.cos theta0 - Real.cos theta| :=
    abs_pos.mpr hcos_den_ne
  have hcos_dist : |Real.cos theta0 - Real.cos theta| ≤
      |theta - theta0| := by
    simpa [abs_sub_comm] using Real.abs_cos_sub_cos_le theta0 theta
  have hsin_nonneg : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_mem_Icc htheta
  have hfirst :
      c / |theta - theta0| ≤ Real.sin theta / |theta - theta0| :=
    div_le_div_of_nonneg_right hc_le_sin (le_of_lt hdist_pos)
  have hsecond :
      Real.sin theta / |theta - theta0| ≤
        Real.sin theta / |Real.cos theta0 - Real.cos theta| :=
    div_le_div_of_nonneg_left hsin_nonneg hcos_den_pos hcos_dist
  exact hfirst.trans hsecond

lemma local_inverse_distance_sum_le_progression_kernel_sum
    {theta0 c rho : ℝ} {n s : ℕ}
    (hspos : 0 < s) (hnot : ¬ IsNodeRow theta0 (n * s))
    (hlocal : ∀ theta ∈ AngleI, theta ≠ theta0 →
      |theta - theta0| < rho →
        c / |theta - theta0| ≤
          Real.sin theta / |Real.cos theta0 - Real.cos theta|) :
    ∑ t ∈ Finset.range n,
        (if |thetaNode (n * s) (s * t) - theta0| < rho then
          c / |thetaNode (n * s) (s * t) - theta0|
        else 0) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos theta0 -
            Real.cos (thetaNode (n * s) (s * t))| := by
  refine Finset.sum_le_sum ?_
  intro t ht
  have htlt : t < n := Finset.mem_range.mp ht
  have hklt : s * t < n * s := thetaNode_progression_lt_mul hspos htlt
  by_cases hnear : |thetaNode (n * s) (s * t) - theta0| < rho
  · have hmem : thetaNode (n * s) (s * t) ∈ AngleI :=
      thetaNode_mem_angleI hklt
    have hne : thetaNode (n * s) (s * t) ≠ theta0 := by
      intro htheta
      exact hnot (by simpa [htheta] using isNodeRow_thetaNode hklt)
    simpa [hnear] using
      hlocal (thetaNode (n * s) (s * t)) hmem hne hnear
  · have hsin_nonneg :
        0 ≤ Real.sin (thetaNode (n * s) (s * t)) :=
      le_of_lt (sin_thetaNode_pos hklt)
    have hterm_nonneg :
        0 ≤ Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos theta0 -
            Real.cos (thetaNode (n * s) (s * t))| :=
      div_nonneg hsin_nonneg (abs_nonneg _)
    simpa [hnear] using hterm_nonneg

lemma scaled_log_le_sum_range_inv_nat_succ {A : ℝ} (M : ℕ)
    (hA : 0 ≤ A) :
    A * Real.log (((M + 1 : ℕ) : ℝ)) ≤
      ∑ q ∈ Finset.range M, A / ((q + 1 : ℕ) : ℝ) := by
  have hlog := log_nat_le_sum_range_inv_nat_succ M
  have hscaled := mul_le_mul_of_nonneg_left hlog hA
  calc
    A * Real.log (((M + 1 : ℕ) : ℝ)) ≤
        A * (∑ q ∈ Finset.range M,
          (1 : ℝ) / ((q + 1 : ℕ) : ℝ)) := by
          simpa [Nat.cast_add, Nat.cast_one] using hscaled
    _ = ∑ q ∈ Finset.range M, A / ((q + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _hq
        ring

lemma shifted_range_image_subset {m M n : ℕ}
    (hrange : ∀ q : ℕ, q < M → m + q < n) :
    (Finset.range M).image (fun q => m + q) ⊆ Finset.range n := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨q, hq, rfl⟩
  exact Finset.mem_range.mpr (hrange q (Finset.mem_range.mp hq))

lemma add_left_injOn_range (m M : ℕ) :
    Set.InjOn (fun q : ℕ => m + q) (Finset.range M : Set ℕ) := by
  intro a _ha b _hb h
  exact Nat.add_left_cancel h

lemma sum_shifted_le_sum_range_of_nonneg {m M n : ℕ} {f : ℕ → ℝ}
    (hrange : ∀ q : ℕ, q < M → m + q < n)
    (hnonneg : ∀ t : ℕ, t < n → 0 ≤ f t) :
    ∑ q ∈ Finset.range M, f (m + q) ≤ ∑ t ∈ Finset.range n, f t := by
  calc
    ∑ q ∈ Finset.range M, f (m + q) =
        ∑ t ∈ (Finset.range M).image (fun q => m + q), f t := by
          exact (Finset.sum_image (s := Finset.range M)
            (g := fun q => m + q) (f := f)
            (add_left_injOn_range m M)).symm
    _ ≤ ∑ t ∈ Finset.range n, f t := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (shifted_range_image_subset hrange)
          (by
            intro t htn _htnot
            exact hnonneg t (Finset.mem_range.mp htn))

lemma interior_shifted_grid_term_le_local_inverse
    {theta0 c rho : ℝ} {n s m q : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (hc_nonneg : 0 ≤ c)
    (hnot : ¬ IsNodeRow theta0 (n * s))
    (hrange : m + q < n)
    (hnear : |thetaNode (n * s) (s * (m + q)) - theta0| < rho)
    (hdist : |thetaNode (n * s) (s * (m + q)) - theta0| ≤
      ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) :
    (c * (n : ℝ) / Real.pi) / ((q + 1 : ℕ) : ℝ) ≤
      if |thetaNode (n * s) (s * (m + q)) - theta0| < rho then
        c / |thetaNode (n * s) (s * (m + q)) - theta0|
      else 0 := by
  rw [if_pos hnear]
  have hklt : s * (m + q) < n * s :=
    thetaNode_progression_lt_mul hspos hrange
  have hne : thetaNode (n * s) (s * (m + q)) ≠ theta0 := by
    intro htheta
    exact hnot (by simpa [htheta] using isNodeRow_thetaNode hklt)
  have hdist_pos :
      0 < |thetaNode (n * s) (s * (m + q)) - theta0| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  have hrecip := one_div_le_one_div_of_le hdist_pos hdist
  have hc_mul := mul_le_mul_of_nonneg_left hrecip hc_nonneg
  have hrewrite :
      c * (1 / (((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ))) =
        (c * (n : ℝ) / Real.pi) / ((q + 1 : ℕ) : ℝ) := by
    field_simp
      [ne_of_gt (by positivity : 0 < ((q + 1 : ℕ) : ℝ)),
       ne_of_gt Real.pi_pos,
       ne_of_gt (by positivity : 0 < (n : ℝ))]
  simpa [hrewrite, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hc_mul

lemma interior_local_inverse_sum_ge_log_of_shift
    {theta0 c rho : ℝ} {n s m M : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (hc_nonneg : 0 ≤ c)
    (hnot : ¬ IsNodeRow theta0 (n * s))
    (hrange : ∀ q : ℕ, q < M → m + q < n)
    (hnear : ∀ q : ℕ, q < M →
      |thetaNode (n * s) (s * (m + q)) - theta0| < rho)
    (hdist : ∀ q : ℕ, q < M →
      |thetaNode (n * s) (s * (m + q)) - theta0| ≤
        ((q + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) :
    (c * (n : ℝ) / Real.pi) * Real.log (((M + 1 : ℕ) : ℝ)) ≤
      ∑ t ∈ Finset.range n,
        (if |thetaNode (n * s) (s * t) - theta0| < rho then
          c / |thetaNode (n * s) (s * t) - theta0|
        else 0) := by
  let f : ℕ → ℝ := fun t =>
    if |thetaNode (n * s) (s * t) - theta0| < rho then
      c / |thetaNode (n * s) (s * t) - theta0| else 0
  have hA_nonneg : 0 ≤ c * (n : ℝ) / Real.pi := by positivity
  refine (scaled_log_le_sum_range_inv_nat_succ M hA_nonneg).trans ?_
  calc
    ∑ q ∈ Finset.range M,
        (c * (n : ℝ) / Real.pi) / ((q + 1 : ℕ) : ℝ) ≤
        ∑ q ∈ Finset.range M, f (m + q) := by
          exact Finset.sum_le_sum fun q hq =>
            interior_shifted_grid_term_le_local_inverse hnpos hspos
              hc_nonneg hnot
              (hrange q (Finset.mem_range.mp hq))
              (hnear q (Finset.mem_range.mp hq))
              (hdist q (Finset.mem_range.mp hq))
    _ ≤ ∑ t ∈ Finset.range n, f t := by
      exact sum_shifted_le_sum_range_of_nonneg
        (m := m) (M := M) (n := n) (f := f) hrange
        (by
          intro t ht
          by_cases hnear_t : |thetaNode (n * s) (s * t) - theta0| < rho
          · have hklt : s * t < n * s :=
              thetaNode_progression_lt_mul hspos ht
            have hne : thetaNode (n * s) (s * t) ≠ theta0 := by
              intro htheta
              exact hnot (by simpa [htheta] using isNodeRow_thetaNode hklt)
            have hdist_pos :
                0 < |thetaNode (n * s) (s * t) - theta0| :=
              abs_pos.mpr (sub_ne_zero_of_ne hne)
            simpa [f, hnear_t] using
              div_nonneg hc_nonneg (le_of_lt hdist_pos)
          · simp [f, hnear_t])

lemma interior_local_inverse_sum_ge_log_of_floor_shift
    {theta0 c rho : ℝ} {n s M : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (hc_nonneg : 0 ≤ c)
    (htheta0_nonneg : 0 ≤ theta0)
    (hnot : ¬ IsNodeRow theta0 (n * s))
    (hrangeM :
      Nat.floor (((n : ℝ) * theta0) / Real.pi) + M ≤ n)
    (hclose : (M : ℝ) * Real.pi / (n : ℝ) < rho) :
    (c * (n : ℝ) / Real.pi) * Real.log (((M + 1 : ℕ) : ℝ)) ≤
      ∑ t ∈ Finset.range n,
        (if |thetaNode (n * s) (s * t) - theta0| < rho then
          c / |thetaNode (n * s) (s * t) - theta0|
        else 0) := by
  exact interior_local_inverse_sum_ge_log_of_shift
    (theta0 := theta0) (c := c) (rho := rho)
    (n := n) (s := s)
    (m := Nat.floor (((n : ℝ) * theta0) / Real.pi)) (M := M)
    hnpos hspos hc_nonneg hnot
    (fun q hq =>
      floor_shift_range_of_add_le (theta0 := theta0)
        (n := n) (M := M) (q := q) hrangeM hq)
    (fun q hq =>
      floor_shift_distance_lt_of_lt
        (theta0 := theta0) (rho := rho) (n := n) (s := s)
        (M := M) (q := q)
        htheta0_nonneg hnpos hspos hq hclose)
    (fun q _hq => by
      simpa using
        interior_floor_shift_distance_bound
          (theta0 := theta0) (n := n) (s := s) (q := q)
          htheta0_nonneg hnpos hspos)

lemma interior_progression_kernel_sum_ge_log_of_floor_shift
    {theta0 c rho : ℝ} {n s M : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (hc_nonneg : 0 ≤ c)
    (htheta0_nonneg : 0 ≤ theta0)
    (hnot : ¬ IsNodeRow theta0 (n * s))
    (hlocal : ∀ theta ∈ AngleI, theta ≠ theta0 →
      |theta - theta0| < rho →
        c / |theta - theta0| ≤
          Real.sin theta / |Real.cos theta0 - Real.cos theta|)
    (hrangeM :
      Nat.floor (((n : ℝ) * theta0) / Real.pi) + M ≤ n)
    (hclose : (M : ℝ) * Real.pi / (n : ℝ) < rho) :
    (c * (n : ℝ) / Real.pi) * Real.log (((M + 1 : ℕ) : ℝ)) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos theta0 -
            Real.cos (thetaNode (n * s) (s * t))| := by
  exact (interior_local_inverse_sum_ge_log_of_floor_shift
    (theta0 := theta0) (c := c) (rho := rho)
    (n := n) (s := s) (M := M)
    hnpos hspos hc_nonneg htheta0_nonneg hnot hrangeM hclose).trans
    (local_inverse_distance_sum_le_progression_kernel_sum
      (theta0 := theta0) (c := c) (rho := rho)
      (n := n) (s := s) hspos hnot hlocal)

lemma interior_progression_kernel_sum_ge_log_of_div_block
    {theta0 c rho : ℝ} {n s Q : ℕ}
    (hnpos : 0 < n) (hspos : 0 < s) (hQpos : 0 < Q)
    (hnlarge : Q ^ 2 ≤ n) (hc_nonneg : 0 ≤ c)
    (htheta0_nonneg : 0 ≤ theta0)
    (hnot : ¬ IsNodeRow theta0 (n * s))
    (hlocal : ∀ theta ∈ AngleI, theta ≠ theta0 →
      |theta - theta0| < rho →
        c / |theta - theta0| ≤
          Real.sin theta / |Real.cos theta0 - Real.cos theta|)
    (hrange : theta0 / Real.pi + 1 / (Q : ℝ) ≤ 1)
    (hQrho : Real.pi / (Q : ℝ) < rho) :
    (c / (2 * Real.pi)) * (n : ℝ) * Real.log (n : ℝ) ≤
      ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos theta0 -
            Real.cos (thetaNode (n * s) (s * t))| := by
  have hlog := log_nat_le_two_log_div_add_one hQpos hnlarge
  have hlog_half :
      Real.log (n : ℝ) / 2 ≤
        Real.log (((n / Q) + 1 : ℕ) : ℝ) := by
    linarith
  have hcoef_nonneg : 0 ≤ c * (n : ℝ) / Real.pi := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog_half hcoef_nonneg
  have hkernel :=
    interior_progression_kernel_sum_ge_log_of_floor_shift
      (theta0 := theta0) (c := c) (rho := rho)
      (n := n) (s := s) (M := n / Q)
      hnpos hspos hc_nonneg htheta0_nonneg hnot hlocal
      (floor_shift_range_div_of_add_inv_le (theta0 := theta0)
        (n := n) (Q := Q) htheta0_nonneg hrange)
      (div_block_close_of_pi_div_lt (rho := rho) (n := n) (Q := Q)
        hnpos hQpos hQrho)
  calc
    (c / (2 * Real.pi)) * (n : ℝ) * Real.log (n : ℝ) =
        (c * (n : ℝ) / Real.pi) * (Real.log (n : ℝ) / 2) := by
          ring
    _ ≤ (c * (n : ℝ) / Real.pi) *
          Real.log (((n / Q) + 1 : ℕ) : ℝ) := hscaled
    _ ≤ ∑ t ∈ Finset.range n,
        Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos theta0 -
            Real.cos (thetaNode (n * s) (s * t))| := hkernel

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

lemma primIdx_mul_powTwo_eq_filter_coprime_odd_factor
    {n s : ℕ} (hn : IsPowTwo n) :
    primIdx (n * s) =
      (Finset.range (n * s)).filter fun k => Nat.Coprime (2 * k + 1) s := by
  ext k
  simp [mem_primIdx_mul_powTwo_iff hn]

lemma primIdx_powTwo_eq_range {n : ℕ} (hn : IsPowTwo n) :
    primIdx n = Finset.range n := by
  have h := primIdx_mul_powTwo_eq_filter_coprime_odd_factor
    (n := n) (s := 1) hn
  simpa using h

lemma Vprim_mul_powTwo_eq_sum_coprime_odd_factor
    {theta0 : ℝ} {n s : ℕ} (hn : IsPowTwo n) :
    Vprim theta0 (n * s) =
      ∑ k ∈ (Finset.range (n * s)).filter
          (fun k => Nat.Coprime (2 * k + 1) s),
        |lambdaWeight theta0 (n * s) k| := by
  rw [Vprim, primIdx_mul_powTwo_eq_filter_coprime_odd_factor hn]

lemma Vprim_powTwo_eq_sum_range
    {theta0 : ℝ} {n : ℕ} (hn : IsPowTwo n) :
    Vprim theta0 n = ∑ k ∈ Finset.range n, |lambdaWeight theta0 n k| := by
  rw [Vprim, primIdx_powTwo_eq_range hn]

lemma Vprim_nonneg (theta0 : ℝ) (d : ℕ) :
    0 ≤ Vprim theta0 d := by
  unfold Vprim
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma sum_abs_lambdaWeight_le_Vprim_of_subset
    {theta0 : ℝ} {d : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primIdx d) :
    ∑ k ∈ S, |lambdaWeight theta0 d k| ≤ Vprim theta0 d := by
  unfold Vprim
  exact Finset.sum_le_sum_of_subset_of_nonneg hS
    (by intro k _hkprim _hknot; exact abs_nonneg _)

lemma sum_le_Vprim_of_subset_of_le_abs_lambdaWeight
    {theta0 : ℝ} {d : ℕ} {S : Finset ℕ} {w : ℕ → ℝ}
    (hS : S ⊆ primIdx d)
    (hw : ∀ k : ℕ, k ∈ S → w k ≤ |lambdaWeight theta0 d k|) :
    ∑ k ∈ S, w k ≤ Vprim theta0 d := by
  calc
    ∑ k ∈ S, w k ≤ ∑ k ∈ S, |lambdaWeight theta0 d k| := by
      exact Finset.sum_le_sum fun k hk => hw k hk
    _ ≤ Vprim theta0 d := sum_abs_lambdaWeight_le_Vprim_of_subset hS

lemma sum_progression_image_abs_lambdaWeight_le_Vprim
    {theta0 : ℝ} {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s) :
    ∑ k ∈ (Finset.range n).image (fun t => s * t),
        |lambdaWeight theta0 (n * s) k| ≤ Vprim theta0 (n * s) :=
  sum_abs_lambdaWeight_le_Vprim_of_subset
    (progression_image_subset_primIdx_mul_powTwo hn hspos)

lemma sum_progression_abs_lambdaWeight_le_Vprim
    {theta0 : ℝ} {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s) :
    ∑ t ∈ Finset.range n, |lambdaWeight theta0 (n * s) (s * t)| ≤
      Vprim theta0 (n * s) := by
  calc
    ∑ t ∈ Finset.range n, |lambdaWeight theta0 (n * s) (s * t)| =
        ∑ k ∈ (Finset.range n).image (fun t => s * t),
          |lambdaWeight theta0 (n * s) k| := by
          exact (Finset.sum_image (s := Finset.range n)
            (g := fun t => s * t)
            (f := fun k => |lambdaWeight theta0 (n * s) k|)
            (mul_left_injOn_range hspos)).symm
    _ ≤ Vprim theta0 (n * s) :=
        sum_progression_image_abs_lambdaWeight_le_Vprim hn hspos

lemma sum_progression_le_Vprim_of_le_abs_lambdaWeight
    {theta0 : ℝ} {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s)
    {w : ℕ → ℝ}
    (hw : ∀ t : ℕ, t ∈ Finset.range n →
      w t ≤ |lambdaWeight theta0 (n * s) (s * t)|) :
    ∑ t ∈ Finset.range n, w t ≤ Vprim theta0 (n * s) := by
  calc
    ∑ t ∈ Finset.range n, w t ≤
        ∑ t ∈ Finset.range n, |lambdaWeight theta0 (n * s) (s * t)| := by
      exact Finset.sum_le_sum fun t ht => hw t ht
    _ ≤ Vprim theta0 (n * s) :=
      sum_progression_abs_lambdaWeight_le_Vprim hn hspos

lemma abs_lambdaWeight_le_Vprim_of_mem
    {theta0 : ℝ} {d k : ℕ} (hk : k ∈ primIdx d) :
    |lambdaWeight theta0 d k| ≤ Vprim theta0 d := by
  unfold Vprim
  exact Finset.single_le_sum
    (s := primIdx d) (f := fun k => |lambdaWeight theta0 d k|)
    (fun _ _ => abs_nonneg _) hk

lemma abs_lambdaWeight_le_Vprim_mul_powTwo_of_coprime_odd_factor
    {theta0 : ℝ} {n s k : ℕ} (hn : IsPowTwo n)
    (hklt : k < n * s) (hcop : Nat.Coprime (2 * k + 1) s) :
    |lambdaWeight theta0 (n * s) k| ≤ Vprim theta0 (n * s) := by
  exact abs_lambdaWeight_le_Vprim_of_mem
    (mem_primIdx_mul_powTwo_iff hn |>.mpr ⟨hklt, hcop⟩)

lemma abs_lambdaWeight_eq
    {theta0 : ℝ} {d k : ℕ} (hk : k < d) :
    |lambdaWeight theta0 d k| =
      (|Real.cos ((d : ℝ) * theta0)| / (d : ℝ)) *
        (Real.sin (thetaNode d k) /
          |Real.cos theta0 - Real.cos (thetaNode d k)|) := by
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hdnonneg : 0 ≤ (d : ℝ) := by positivity
  have hsinnonneg : 0 ≤ Real.sin (thetaNode d k) :=
    le_of_lt (sin_thetaNode_pos hk)
  unfold lambdaWeight
  simp [abs_mul, abs_div, abs_pow, abs_of_nonneg hdnonneg,
    abs_of_nonneg hsinnonneg]
  ring

lemma abs_lambdaWeight_progression_eq
    {theta0 : ℝ} {n s t : ℕ} (hspos : 0 < s) (ht : t < n) :
    |lambdaWeight theta0 (n * s) (s * t)| =
      (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| / ((n * s : ℕ) : ℝ)) *
        (Real.sin (thetaNode (n * s) (s * t)) /
          |Real.cos theta0 - Real.cos (thetaNode (n * s) (s * t))|) := by
  have hklt : s * t < n * s := by
    have hlt : s * t < s * n := Nat.mul_lt_mul_of_pos_left ht hspos
    simpa [Nat.mul_comm] using hlt
  exact abs_lambdaWeight_eq hklt

lemma sum_progression_cos_mul_kernel_le_Vprim
    {theta0 : ℝ} {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s) :
    ∑ t ∈ Finset.range n,
        (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| / ((n * s : ℕ) : ℝ)) *
          (Real.sin (thetaNode (n * s) (s * t)) /
            |Real.cos theta0 - Real.cos (thetaNode (n * s) (s * t))|) ≤
      Vprim theta0 (n * s) := by
  exact sum_progression_le_Vprim_of_le_abs_lambdaWeight hn hspos
    (fun t ht => by
      rw [abs_lambdaWeight_progression_eq hspos (Finset.mem_range.mp ht)])

lemma cos_div_mul_sum_progression_kernel_le_Vprim
    {theta0 : ℝ} {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s) :
    (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| / ((n * s : ℕ) : ℝ)) *
        (∑ t ∈ Finset.range n,
          Real.sin (thetaNode (n * s) (s * t)) /
            |Real.cos theta0 - Real.cos (thetaNode (n * s) (s * t))|) ≤
      Vprim theta0 (n * s) := by
  rw [Finset.mul_sum]
  exact sum_progression_cos_mul_kernel_le_Vprim hn hspos

lemma Vprim_lower_of_progression_kernel_lower
    {theta0 c : ℝ} {n s : ℕ}
    (hn : IsPowTwo n) (hnpos : 0 < n) (hspos : 0 < s)
    (hkernel :
      c * ((n * s : ℕ) : ℝ) * Real.log (n : ℝ) ≤
        ∑ t ∈ Finset.range n,
          Real.sin (thetaNode (n * s) (s * t)) /
            |Real.cos theta0 - Real.cos (thetaNode (n * s) (s * t))|) :
    c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| * Real.log (n : ℝ) ≤
      Vprim theta0 (n * s) := by
  have hdpos_nat : 0 < n * s := Nat.mul_pos hnpos hspos
  have hdpos : 0 < ((n * s : ℕ) : ℝ) := by exact_mod_cast hdpos_nat
  have hdne : ((n * s : ℕ) : ℝ) ≠ 0 := ne_of_gt hdpos
  have hcoef_nonneg :
      0 ≤ |Real.cos (((n * s : ℕ) : ℝ) * theta0)| /
          ((n * s : ℕ) : ℝ) :=
    div_nonneg (abs_nonneg _) (le_of_lt hdpos)
  have hscaled := mul_le_mul_of_nonneg_left hkernel hcoef_nonneg
  have hnormalize :
      (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| /
            ((n * s : ℕ) : ℝ)) *
          (c * ((n * s : ℕ) : ℝ) * Real.log (n : ℝ)) =
        c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| *
          Real.log (n : ℝ) := by
    field_simp [hdne]
  calc
    c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| * Real.log (n : ℝ) =
        (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| /
            ((n * s : ℕ) : ℝ)) *
          (c * ((n * s : ℕ) : ℝ) * Real.log (n : ℝ)) := hnormalize.symm
    _ ≤ (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| /
            ((n * s : ℕ) : ℝ)) *
          (∑ t ∈ Finset.range n,
            Real.sin (thetaNode (n * s) (s * t)) /
              |Real.cos theta0 - Real.cos (thetaNode (n * s) (s * t))|) :=
        hscaled
    _ ≤ Vprim theta0 (n * s) :=
        cos_div_mul_sum_progression_kernel_le_Vprim hn hspos

lemma scaled_row_kernel_lower_of_base
    {c L S : ℝ} {R n s : ℕ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hRpos : 0 < R) (hsR : s ≤ R)
    (hbase : c * (n : ℝ) * L ≤ S) :
    (c / (R : ℝ)) * ((n * s : ℕ) : ℝ) * L ≤ S := by
  have hRpos_real : 0 < (R : ℝ) := by exact_mod_cast hRpos
  have hsR_real : (s : ℝ) ≤ (R : ℝ) := by exact_mod_cast hsR
  have hA_nonneg : 0 ≤ c * L * (n : ℝ) := by positivity
  have hmul :
      c * L * (n : ℝ) * (s : ℝ) ≤
        c * L * (n : ℝ) * (R : ℝ) :=
    mul_le_mul_of_nonneg_left hsR_real hA_nonneg
  have hscaled :
      c * ((n * s : ℕ) : ℝ) * L ≤ c * (n : ℝ) * L * (R : ℝ) := by
    norm_num [Nat.cast_mul] at hmul ⊢
    nlinarith
  have hto_base :
      (c / (R : ℝ)) * ((n * s : ℕ) : ℝ) * L ≤
        c * (n : ℝ) * L := by
    calc
      (c / (R : ℝ)) * ((n * s : ℕ) : ℝ) * L =
          (c * ((n * s : ℕ) : ℝ) * L) / (R : ℝ) := by ring
      _ ≤ c * (n : ℝ) * L := by
          rw [div_le_iff₀ hRpos_real]
          simpa [mul_assoc] using hscaled
  exact hto_base.trans hbase

lemma Vprim_lower_of_progression_kernel_lower_base
    {theta0 c : ℝ} {R n s : ℕ}
    (hn : IsPowTwo n) (hnpos : 0 < n)
    (hRpos : 0 < R) (hspos : 0 < s) (hsR : s ≤ R)
    (hc : 0 ≤ c) (hlog : 0 ≤ Real.log (n : ℝ))
    (hkernel :
      c * (n : ℝ) * Real.log (n : ℝ) ≤
        ∑ t ∈ Finset.range n,
          Real.sin (thetaNode (n * s) (s * t)) /
            |Real.cos theta0 - Real.cos (thetaNode (n * s) (s * t))|) :
    (c / (R : ℝ)) * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| *
        Real.log (n : ℝ) ≤
      Vprim theta0 (n * s) := by
  exact Vprim_lower_of_progression_kernel_lower
    (theta0 := theta0) (c := c / (R : ℝ)) hn hnpos hspos
    (scaled_row_kernel_lower_of_base hc hlog hRpos hsR hkernel)

lemma abs_lambdaWeight_ge_cos_mul_sin_div_theta_dist
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {d k : ℕ} (hk : k < d) (hne : thetaNode d k ≠ theta0) :
    (|Real.cos ((d : ℝ) * theta0)| / (d : ℝ)) *
        (Real.sin (thetaNode d k) / |thetaNode d k - theta0|) ≤
      |lambdaWeight theta0 d k| := by
  rw [abs_lambdaWeight_eq hk]
  have hnode : thetaNode d k ∈ AngleI := thetaNode_mem_angleI hk
  have hcos_den_ne :
      Real.cos theta0 - Real.cos (thetaNode d k) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hcos
    have htheta : theta0 = thetaNode d k :=
      Real.injOn_cos htheta0 hnode hcos
    exact hne htheta.symm
  have hcos_den_pos :
      0 < |Real.cos theta0 - Real.cos (thetaNode d k)| :=
    abs_pos.mpr hcos_den_ne
  have hdist_pos : 0 < |thetaNode d k - theta0| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  have hcos_dist :
      |Real.cos theta0 - Real.cos (thetaNode d k)| ≤
        |thetaNode d k - theta0| := by
    simpa [abs_sub_comm] using
      (Real.abs_cos_sub_cos_le theta0 (thetaNode d k))
  have hsinnonneg : 0 ≤ Real.sin (thetaNode d k) :=
    le_of_lt (sin_thetaNode_pos hk)
  have hfrac :
      Real.sin (thetaNode d k) / |thetaNode d k - theta0| ≤
        Real.sin (thetaNode d k) /
          |Real.cos theta0 - Real.cos (thetaNode d k)| :=
    div_le_div_of_nonneg_left hsinnonneg hcos_den_pos hcos_dist
  have hcoef_nonneg :
      0 ≤ |Real.cos ((d : ℝ) * theta0)| / (d : ℝ) :=
    div_nonneg (abs_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left hfrac hcoef_nonneg

lemma abs_lambdaWeight_ge_cos_mul_sin_div_theta_dist_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {d k : ℕ} (hk : k < d) (hnot : ¬ IsNodeRow theta0 d) :
    (|Real.cos ((d : ℝ) * theta0)| / (d : ℝ)) *
        (Real.sin (thetaNode d k) / |thetaNode d k - theta0|) ≤
      |lambdaWeight theta0 d k| := by
  have hne : thetaNode d k ≠ theta0 := by
    intro htheta
    exact hnot (by simpa [htheta] using isNodeRow_thetaNode hk)
  exact abs_lambdaWeight_ge_cos_mul_sin_div_theta_dist htheta0 hk hne

lemma abs_lambdaWeight_progression_ge_cos_mul_sin_div_theta_dist_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n s t : ℕ} (hspos : 0 < s) (ht : t < n)
    (hnot : ¬ IsNodeRow theta0 (n * s)) :
    (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| / ((n * s : ℕ) : ℝ)) *
        (Real.sin (thetaNode (n * s) (s * t)) /
          |thetaNode (n * s) (s * t) - theta0|) ≤
      |lambdaWeight theta0 (n * s) (s * t)| := by
  have hklt : s * t < n * s := by
    have hlt : s * t < s * n := Nat.mul_lt_mul_of_pos_left ht hspos
    simpa [Nat.mul_comm] using hlt
  exact abs_lambdaWeight_ge_cos_mul_sin_div_theta_dist_of_not_isNodeRow
    htheta0 hklt hnot

lemma sum_progression_cos_mul_sin_div_theta_dist_le_Vprim_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n s : ℕ} (hn : IsPowTwo n) (hspos : 0 < s)
    (hnot : ¬ IsNodeRow theta0 (n * s)) :
    ∑ t ∈ Finset.range n,
        (|Real.cos (((n * s : ℕ) : ℝ) * theta0)| / ((n * s : ℕ) : ℝ)) *
          (Real.sin (thetaNode (n * s) (s * t)) /
            |thetaNode (n * s) (s * t) - theta0|) ≤
      Vprim theta0 (n * s) := by
  exact sum_progression_le_Vprim_of_le_abs_lambdaWeight hn hspos
    (fun t ht =>
      abs_lambdaWeight_progression_ge_cos_mul_sin_div_theta_dist_of_not_isNodeRow
        htheta0 hspos (Finset.mem_range.mp ht) hnot)

lemma lambdaWeight_ne_zero_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {d k : ℕ} (hk : k < d) (hnot : ¬ IsNodeRow theta0 d) :
    lambdaWeight theta0 d k ≠ 0 := by
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdpos)
  have hcos : Real.cos ((d : ℝ) * theta0) ≠ 0 := hnot
  have hden : Real.cos theta0 - Real.cos (thetaNode d k) ≠ 0 := by
    have hcos_ne :=
      cos_ne_xNode_of_not_isNodeRow htheta0 hnot k (Finset.mem_range.mpr hk)
    simpa [xNode, sub_eq_zero] using hcos_ne
  have hfirst : Real.cos ((d : ℝ) * theta0) / (d : ℝ) ≠ 0 :=
    div_ne_zero hcos hdne
  have hpow : (-1 : ℝ) ^ k ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hsin : Real.sin (thetaNode d k) ≠ 0 :=
    ne_of_gt (sin_thetaNode_pos hk)
  unfold lambdaWeight
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hfirst hpow) hsin) hden

lemma Vprim_pos_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {d : ℕ} (hdpos : 0 < d) (hnot : ¬ IsNodeRow theta0 d) :
    0 < Vprim theta0 d := by
  have h0mem : 0 ∈ primIdx d := by
    simp [mem_primIdx_iff, hdpos]
  have hterm_pos : 0 < |lambdaWeight theta0 d 0| := by
    exact abs_pos.mpr
      (lambdaWeight_ne_zero_of_not_isNodeRow htheta0 (by simpa using hdpos) hnot)
  unfold Vprim
  exact hterm_pos.trans_le
    (Finset.single_le_sum
      (s := primIdx d) (f := fun k => |lambdaWeight theta0 d k|)
      (fun _ _ => abs_nonneg _) h0mem)

lemma Vprim_ne_zero_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {d : ℕ} (hdpos : 0 < d) (hnot : ¬ IsNodeRow theta0 d) :
    Vprim theta0 d ≠ 0 :=
  ne_of_gt (Vprim_pos_of_not_isNodeRow htheta0 hdpos hnot)

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

lemma abs_spikeCoeff_le
    {theta0 : ℝ} {n s : ℕ} (hspos : 0 < s)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0) :
    |spikeCoeff theta0 n s| ≤
      |Real.cos (((n * s : ℕ) : ℝ) * theta0)| /
        ((s : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
  have hs_nonneg : 0 ≤ (s : ℝ) := by positivity
  have hden_pos : 0 < (s : ℝ) * |Real.cos ((n : ℝ) * theta0)| := by
    exact mul_pos (by positivity) (abs_pos.mpr hcosn)
  have hnum_le :
      |muR s| * |chi s| * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| ≤
        |Real.cos (((n * s : ℕ) : ℝ) * theta0)| := by
    rw [abs_chi]
    calc
      |muR s| * 1 * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| ≤
          1 * 1 * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| := by
          gcongr
          exact abs_muR_le_one s
      _ = |Real.cos (((n * s : ℕ) : ℝ) * theta0)| := by ring
  unfold spikeCoeff
  calc
    |muR s * chi s * Real.cos (((n * s : ℕ) : ℝ) * theta0) /
        ((s : ℝ) * Real.cos ((n : ℝ) * theta0))| =
        (|muR s| * |chi s| * |Real.cos (((n * s : ℕ) : ℝ) * theta0)|) /
          ((s : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
          rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs_nonneg]
    _ ≤ |Real.cos (((n * s : ℕ) : ℝ) * theta0)| /
          ((s : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
          exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)

lemma abs_spikeCoeff_div_Vprim_le_of_Vprim_lower
    {theta0 : ℝ} {n s : ℕ} {c kappa : ℝ}
    (hspos : 0 < s) (hcpos : 0 < c) (hkpos : 0 < kappa)
    (hlogpos : 0 < Real.log (n : ℝ))
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcosns : Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hmass : c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| *
        Real.log (n : ℝ) ≤ Vprim theta0 (n * s)) :
    |spikeCoeff theta0 n s| / Vprim theta0 (n * s) ≤
      (1 / (c * kappa)) / Real.log (n : ℝ) := by
  let x : ℝ := |Real.cos (((n * s : ℕ) : ℝ) * theta0)|
  let y : ℝ := |Real.cos ((n : ℝ) * theta0)|
  let L : ℝ := Real.log (n : ℝ)
  let V : ℝ := Vprim theta0 (n * s)
  have hxpos : 0 < x := by
    dsimp [x]
    exact abs_pos.mpr hcosns
  have hypos : 0 < y := lt_of_lt_of_le hkpos hkappa_le
  have hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0 := by
    intro h
    have hy0 : y = 0 := by simp [y, h]
    linarith
  have hmass' : c * x * L ≤ V := by
    simpa [x, L, V] using hmass
  have hVpos : 0 < V :=
    lt_of_lt_of_le (mul_pos (mul_pos hcpos hxpos) hlogpos) hmass'
  have hsreal : (1 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hspos
  have hy_nonneg : 0 ≤ y := le_of_lt hypos
  have hsy_nonneg : 0 ≤ (s : ℝ) * y := mul_nonneg (by positivity) hy_nonneg
  have hy_le_sy : y ≤ (s : ℝ) * y := by nlinarith
  have hk_le_sy : kappa ≤ (s : ℝ) * y := hkappa_le.trans hy_le_sy
  have hA_nonneg : 0 ≤ c * x * L :=
    le_of_lt (mul_pos (mul_pos hcpos hxpos) hlogpos)
  have hden_lower : c * kappa * x * L ≤ (s : ℝ) * y * V := by
    calc
      c * kappa * x * L = kappa * (c * x * L) := by ring
      _ ≤ ((s : ℝ) * y) * (c * x * L) := by
          exact mul_le_mul_of_nonneg_right hk_le_sy hA_nonneg
      _ ≤ ((s : ℝ) * y) * V := by
          exact mul_le_mul_of_nonneg_left hmass' hsy_nonneg
      _ = (s : ℝ) * y * V := by ring
  have hden_lower_pos : 0 < c * kappa * x * L := by positivity
  have hsy_pos : 0 < (s : ℝ) * y := mul_pos (by positivity) hypos
  have hsy_ne : (s : ℝ) * y ≠ 0 := ne_of_gt hsy_pos
  have hV_ne : V ≠ 0 := ne_of_gt hVpos
  have hc_ne : c ≠ 0 := ne_of_gt hcpos
  have hk_ne : kappa ≠ 0 := ne_of_gt hkpos
  have hx_ne : x ≠ 0 := ne_of_gt hxpos
  have hL_ne : L ≠ 0 := ne_of_gt hlogpos
  have h_abs := abs_spikeCoeff_le (theta0 := theta0) (n := n) (s := s)
    hspos hcosn
  have hstep1 :
      |spikeCoeff theta0 n s| / V ≤ (x / ((s : ℝ) * y)) / V := by
    exact div_le_div_of_nonneg_right
      (by simpa [x, y] using h_abs) (le_of_lt hVpos)
  have hfrac : (x / ((s : ℝ) * y)) / V ≤ x / (c * kappa * x * L) := by
    calc
      (x / ((s : ℝ) * y)) / V = x / (((s : ℝ) * y) * V) := by
        field_simp [hsy_ne, hV_ne]
      _ ≤ x / (c * kappa * x * L) := by
        exact div_le_div_of_nonneg_left (le_of_lt hxpos) hden_lower_pos hden_lower
  have htarget : x / (c * kappa * x * L) = (1 / (c * kappa)) / L := by
    field_simp [hc_ne, hk_ne, hx_ne, hL_ne]
  exact hstep1.trans (hfrac.trans (le_of_eq htarget))

lemma coeff_bound_of_Vprim_lower
    {theta0 : ℝ} {R n : ℕ} {c kappa : ℝ}
    (hcpos : 0 < c) (hkpos : 0 < kappa)
    (hlogpos : 0 < Real.log (n : ℝ))
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hmass : ∀ s : ℕ, s ∈ oddUpTo R →
      c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| * Real.log (n : ℝ) ≤
        Vprim theta0 (n * s)) :
    ∀ s : ℕ, s ∈ oddUpTo R →
      |spikeCoeff theta0 n s| / Vprim theta0 (n * s) ≤
        (1 / (c * kappa)) / Real.log (n : ℝ) := by
  intro s hs
  have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
  exact abs_spikeCoeff_div_Vprim_le_of_Vprim_lower
    hspos hcpos hkpos hlogpos hkappa_le (hcos s hs) (hmass s hs)

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

lemma abs_real_sign_le_one (x : ℝ) :
    |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

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

lemma abs_finiteSpikeValueAtPrimitive_le
    {theta0 : ℝ} {n s k : ℕ} {B : ℝ}
    (hVpos : 0 < Vprim theta0 (n * s))
    (hbound : |spikeCoeff theta0 n s| / Vprim theta0 (n * s) ≤ B) :
    |finiteSpikeValueAtPrimitive theta0 n s k| ≤ B := by
  have hV_nonneg : 0 ≤ Vprim theta0 (n * s) := le_of_lt hVpos
  have hquot_nonneg : 0 ≤ |spikeCoeff theta0 n s| / Vprim theta0 (n * s) :=
    div_nonneg (abs_nonneg _) hV_nonneg
  unfold finiteSpikeValueAtPrimitive
  calc
    |spikeCoeff theta0 n s / Vprim theta0 (n * s) *
        Real.sign (lambdaWeight theta0 (n * s) k)| =
        (|spikeCoeff theta0 n s| / Vprim theta0 (n * s)) *
          |Real.sign (lambdaWeight theta0 (n * s) k)| := by
          rw [abs_mul, abs_div, abs_of_nonneg hV_nonneg]
    _ ≤ (|spikeCoeff theta0 n s| / Vprim theta0 (n * s)) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (abs_real_sign_le_one _) hquot_nonneg
    _ = |spikeCoeff theta0 n s| / Vprim theta0 (n * s) := by ring
    _ ≤ B := hbound

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
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u → Vprim theta0 (n * s) ≠ 0) :
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
        hnpos huodd hdiv hs (hcosns s hs hdiv) (hV s hs hdiv)
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

lemma row_sum_finiteSpikeRaw_eq_oddUpTo_if_of_good_divisors
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    (∑ l ∈ Finset.range (n * u),
      lambdaWeight theta0 (n * u) l *
        finiteSpikeRaw theta0 R n (thetaNode (n * u) l)) =
    ∑ s ∈ oddUpTo R,
      if s ∣ u then
        gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s
      else 0 := by
  have hV : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Vprim theta0 (n * s) ≠ 0 := by
    intro s hs hdiv
    have hsodd : Odd s := odd_of_dvd_odd huodd hdiv
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hsodd.pos
    have hnot : ¬ IsNodeRow theta0 (n * s) := by
      simpa [IsNodeRow] using hcosns s hs hdiv
    exact Vprim_ne_zero_of_not_isNodeRow htheta0 hdpos hnot
  exact row_sum_finiteSpikeRaw_eq_oddUpTo_if hnpos huodd hcosns hV

lemma rowEval_finiteSpikeRaw_odd_eq_oddUpTo_if_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) =
    ∑ s ∈ oddUpTo R,
      if s ∣ u then
        gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s
      else 0 := by
  have hrowpos : 0 < n * u := Nat.mul_pos hnpos huodd.pos
  have hrowne : n * u ≠ 0 := Nat.ne_of_gt hrowpos
  rw [rowEval, if_neg hrowne, if_neg hnot]
  exact row_sum_finiteSpikeRaw_eq_oddUpTo_if_of_good_divisors
    htheta0 hnpos huodd hcosns

lemma sum_oddUpTo_if_dvd_gamma_mul_spikeCoeff_eq_prefactor_mul
    {theta0 : ℝ} {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    (∑ s ∈ oddUpTo R,
      if s ∣ u then
        gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s
      else 0) =
      (chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
          ((u : ℝ) * Real.cos ((n : ℝ) * theta0))) *
        (∑ s ∈ oddUpTo R, if s ∣ u then muR s else 0) := by
  classical
  let P : ℝ :=
    chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
      ((u : ℝ) * Real.cos ((n : ℝ) * theta0))
  calc
    (∑ s ∈ oddUpTo R,
      if s ∣ u then
        gamma theta0 (n * u) (n * s) * spikeCoeff theta0 n s
      else 0) =
        ∑ s ∈ oddUpTo R, P * (if s ∣ u then muR s else 0) := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hdiv : s ∣ u
          · have hgamma :=
              gamma_mul_spikeCoeff_eq_prefactor_mul_muR
              (theta0 := theta0) (n := n) (u := u) (s := s)
              hnpos huodd hdiv hcosn (hcosns s hs hdiv)
            simpa [hdiv, P, Nat.cast_mul, mul_assoc] using hgamma
          · simp [hdiv]
    _ =
      P * (∑ s ∈ oddUpTo R, if s ∣ u then muR s else 0) := by
        rw [Finset.mul_sum]

lemma rowEval_finiteSpikeRaw_odd_eq_prefactor_mul_partial_mu
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) =
      (chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
          ((u : ℝ) * Real.cos ((n : ℝ) * theta0))) *
        (∑ s ∈ oddUpTo R, if s ∣ u then muR s else 0) := by
  rw [rowEval_finiteSpikeRaw_odd_eq_oddUpTo_if_of_not_isNodeRow
    htheta0 hnpos huodd hnot hcosns]
  exact sum_oddUpTo_if_dvd_gamma_mul_spikeCoeff_eq_prefactor_mul
    hnpos huodd hcosn hcosns

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

lemma sum_oddUpTo_if_dvd_eq_sum_divisors_le
    {R u : ℕ} (huodd : Odd u) (G : ℕ → ℝ) :
    (∑ s ∈ oddUpTo R, if s ∣ u then G s else 0) =
      ∑ s ∈ Nat.divisors u, if s ≤ R then G s else 0 := by
  classical
  let D : Finset ℕ := (Nat.divisors u).filter fun s => s ≤ R
  have hsubset : D ⊆ oddUpTo R := by
    intro s hs
    have hsD := Finset.mem_filter.mp hs
    have hdiv : s ∣ u := (Nat.mem_divisors.mp hsD.1).1
    have hspos : 0 < s := Nat.pos_of_mem_divisors hsD.1
    have hsodd : Odd s := odd_of_dvd_odd huodd hdiv
    exact mem_oddUpTo_iff.mpr ⟨hspos, hsD.2, hsodd⟩
  have houtside :
      ∀ x ∈ oddUpTo R, x ∉ D →
        (if x ∣ u then G x else 0) = 0 := by
    intro x hx hnot
    by_cases hdiv : x ∣ u
    · have hxdiv : x ∈ Nat.divisors u :=
        Nat.mem_divisors.mpr ⟨hdiv, Nat.ne_of_gt huodd.pos⟩
      have hxle : x ≤ R := (mem_oddUpTo_iff.mp hx).2.1
      have hxD : x ∈ D := by
        exact Finset.mem_filter.mpr ⟨hxdiv, hxle⟩
      exact False.elim (hnot hxD)
    · simp [hdiv]
  calc
    (∑ s ∈ oddUpTo R, if s ∣ u then G s else 0) =
        ∑ s ∈ D, if s ∣ u then G s else 0 := by
          exact (Finset.sum_subset hsubset houtside).symm
    _ = ∑ s ∈ D, G s := by
          apply Finset.sum_congr rfl
          intro s hs
          have hdiv : s ∣ u := (Nat.mem_divisors.mp (Finset.mem_filter.mp hs).1).1
          simp [hdiv]
    _ = ∑ s ∈ Nat.divisors u, if s ≤ R then G s else 0 := by
          simp [D, Finset.sum_filter]

lemma partial_mu_sum_eq_neg_tail
    {R u : ℕ} (huodd : Odd u) (hu_ne : u ≠ 1) :
    (∑ s ∈ oddUpTo R, if s ∣ u then muR s else 0) =
      -∑ s ∈ Nat.divisors u, if R < s then muR s else 0 := by
  classical
  have hpartial :=
    sum_oddUpTo_if_dvd_eq_sum_divisors_le (R := R) (u := u) huodd muR
  have hsplit :
      (∑ s ∈ Nat.divisors u, muR s) =
        (∑ s ∈ Nat.divisors u, if s ≤ R then muR s else 0) +
          ∑ s ∈ Nat.divisors u, if R < s then muR s else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hsR : s ≤ R
    · simp [hsR, not_lt.mpr hsR]
    · have hRs : R < s := Nat.lt_of_not_ge hsR
      simp [hsR, hRs]
  have hfull : (∑ s ∈ Nat.divisors u, muR s) = 0 :=
    sum_muR_divisors_eq_zero_of_ne_one huodd.pos hu_ne
  rw [hsplit, ← hpartial] at hfull
  linarith

lemma abs_sum_muR_tail_le_card (R u : ℕ) :
    |∑ s ∈ Nat.divisors u, if R < s then muR s else 0| ≤
      (((Nat.divisors u).filter fun s => R < s).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  calc
    |∑ s ∈ (Nat.divisors u).filter fun s => R < s, muR s| ≤
        ∑ s ∈ (Nat.divisors u).filter fun s => R < s, |muR s| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (Nat.divisors u).filter fun s => R < s, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          exact abs_muR_le_one s
    _ = (((Nat.divisors u).filter fun s => R < s).card : ℝ) := by
          simp

lemma abs_future_prefactor_le
    {theta0 : ℝ} {n u : ℕ}
    (huodd : Odd u)
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0) :
    |chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
        ((u : ℝ) * Real.cos ((n : ℝ) * theta0))| ≤
      1 / ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
  have hupos : 0 < u := huodd.pos
  have hu_nonneg : 0 ≤ (u : ℝ) := by positivity
  have hden_pos : 0 < (u : ℝ) * |Real.cos ((n : ℝ) * theta0)| := by
    exact mul_pos (by positivity) (abs_pos.mpr hcosn)
  calc
    |chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
        ((u : ℝ) * Real.cos ((n : ℝ) * theta0))| =
        |Real.cos (((n * u : ℕ) : ℝ) * theta0)| /
          ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
          rw [abs_div, abs_mul, abs_mul, abs_chi,
            abs_of_nonneg hu_nonneg]
          ring
    _ ≤ 1 / ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
          exact div_le_div_of_nonneg_right
            (Real.abs_cos_le_one _) (le_of_lt hden_pos)

lemma rowEval_finiteSpikeRaw_odd_eq_neg_prefactor_mul_tail_mu
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n) =
      -((chi u * Real.cos (((n * u : ℕ) : ℝ) * theta0) /
          ((u : ℝ) * Real.cos ((n : ℝ) * theta0))) *
        (∑ s ∈ Nat.divisors u, if R < s then muR s else 0)) := by
  rw [rowEval_finiteSpikeRaw_odd_eq_prefactor_mul_partial_mu
    htheta0 hnpos huodd hnot hcosn hcosns]
  rw [partial_mu_sum_eq_neg_tail (R := R) (u := u) huodd hu_ne]
  ring

lemma abs_rowEval_finiteSpikeRaw_odd_le_tail_card
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    |rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n)| ≤
      (1 / ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|)) *
        (((Nat.divisors u).filter fun s => R < s).card : ℝ) := by
  rw [rowEval_finiteSpikeRaw_odd_eq_neg_prefactor_mul_tail_mu
    htheta0 hnpos huodd hu_ne hnot hcosn hcosns]
  rw [abs_neg, abs_mul]
  have hpref :=
    abs_future_prefactor_le (theta0 := theta0) (n := n) (u := u)
      huodd hcosn
  have htail := abs_sum_muR_tail_le_card R u
  exact mul_le_mul hpref htail (abs_nonneg _)
    (div_nonneg zero_le_one
      (mul_nonneg (by positivity) (abs_nonneg _)))

lemma divisor_tail_card_le_complement_small_card (R u : ℕ) :
    ((Nat.divisors u).filter fun s => R < s).card ≤
      ((Nat.divisors u).filter fun t => R * t < u).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun s => u / s) ?_ ?_
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    rcases hs with ⟨hsdivs, hRs⟩
    have hsdiv : s ∣ u := (Nat.mem_divisors.mp hsdivs).1
    have hune : u ≠ 0 := (Nat.mem_divisors.mp hsdivs).2
    have hspos : 0 < s := Nat.pos_of_mem_divisors hsdivs
    have hcompdiv : u / s ∣ u := Nat.div_dvd_of_dvd hsdiv
    have hcompmem : u / s ∈ Nat.divisors u :=
      Nat.mem_divisors.mpr ⟨hcompdiv, hune⟩
    have hsu : s ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hune) hsdiv
    have hqpos : 0 < u / s := Nat.div_pos hsu hspos
    have hmul_lt : R * (u / s) < s * (u / s) :=
      Nat.mul_lt_mul_of_pos_right hRs hqpos
    have hsqu : s * (u / s) = u := by
      simpa [Nat.mul_comm] using Nat.div_mul_cancel hsdiv
    exact ⟨hcompmem, by simpa [hsqu] using hmul_lt⟩
  · intro a ha b hb hab
    change u / a = u / b at hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    rcases ha with ⟨hadivs, _hRa⟩
    rcases hb with ⟨hbdivs, _hRb⟩
    have hadiv : a ∣ u := (Nat.mem_divisors.mp hadivs).1
    have hbdiv : b ∣ u := (Nat.mem_divisors.mp hbdivs).1
    have hune : u ≠ 0 := (Nat.mem_divisors.mp hadivs).2
    have hapos : 0 < a := Nat.pos_of_mem_divisors hadivs
    have hau : a ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hune) hadiv
    have hqpos : 0 < u / a := Nat.div_pos hau hapos
    have hmul_a : (u / a) * a = u := Nat.div_mul_cancel hadiv
    have hmul_b : (u / b) * b = u := Nat.div_mul_cancel hbdiv
    have hmul : (u / a) * a = (u / a) * b := by
      calc
        (u / a) * a = u := hmul_a
        _ = (u / b) * b := hmul_b.symm
        _ = (u / a) * b := by rw [hab]
    exact Nat.eq_of_mul_eq_mul_left hqpos hmul

lemma abs_rowEval_finiteSpikeRaw_odd_le_complement_small_card
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    |rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n)| ≤
      (1 / ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|)) *
        (((Nat.divisors u).filter fun t => R * t < u).card : ℝ) := by
  have htail :=
    abs_rowEval_finiteSpikeRaw_odd_le_tail_card
      (R := R) htheta0 hnpos huodd hu_ne hnot hcosn hcosns
  have hcard_nat := divisor_tail_card_le_complement_small_card R u
  have hcard :
      (((Nat.divisors u).filter fun s => R < s).card : ℝ) ≤
        (((Nat.divisors u).filter fun t => R * t < u).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hpref_nonneg :
      0 ≤ 1 / ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
    exact div_nonneg zero_le_one
      (mul_nonneg (by positivity) (abs_nonneg _))
  exact htail.trans (mul_le_mul_of_nonneg_left hcard hpref_nonneg)

lemma complement_small_card_le_div {R u : ℕ} (hRpos : 0 < R) :
    ((Nat.divisors u).filter fun t => R * t < u).card ≤ u / R := by
  classical
  have hsubset :
      ((Nat.divisors u).filter fun t => R * t < u) ⊆ Finset.Icc 1 (u / R) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_Icc]
    rcases ht with ⟨htdivs, hRt⟩
    have htpos : 0 < t := Nat.pos_of_mem_divisors htdivs
    have hle_mul : t * R ≤ u := by
      have hle : R * t ≤ u := Nat.le_of_lt hRt
      simpa [Nat.mul_comm] using hle
    exact ⟨htpos, (Nat.le_div_iff_mul_le hRpos).mpr hle_mul⟩
  have hcard := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hcard
  simpa using hcard

lemma complement_small_card_div_le_inv {R u : ℕ}
    (hRpos : 0 < R) (hupos : 0 < u) :
    ((((Nat.divisors u).filter fun t => R * t < u).card : ℝ) / (u : ℝ)) ≤
      1 / (R : ℝ) := by
  classical
  let C : ℕ := ((Nat.divisors u).filter fun t => R * t < u).card
  have hcard_nat : C ≤ u / R := by
    simpa [C] using complement_small_card_le_div (R := R) (u := u) hRpos
  have hcard_cast : (C : ℝ) ≤ ((u / R : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hfloor : ((u / R : ℕ) : ℝ) ≤ (u : ℝ) / (R : ℝ) :=
    Nat.cast_div_le
  have hcard_real : (C : ℝ) ≤ (u : ℝ) / (R : ℝ) :=
    hcard_cast.trans hfloor
  have hu_nonneg : 0 ≤ (u : ℝ) := by positivity
  have hu_ne : (u : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hupos
  have hR_ne : (R : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hRpos
  have h := div_le_div_of_nonneg_right hcard_real hu_nonneg
  have hcalc : ((u : ℝ) / (R : ℝ)) / (u : ℝ) = 1 / (R : ℝ) := by
    field_simp [hu_ne, hR_ne]
  simpa [C, hcalc] using h

lemma abs_rowEval_finiteSpikeRaw_odd_le_inv_R_abs_cos
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ}
    (hRpos : 0 < R) (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0)
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    |rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n)| ≤
      1 / ((R : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
  have hbase :=
    abs_rowEval_finiteSpikeRaw_odd_le_complement_small_card
      (R := R) htheta0 hnpos huodd hu_ne hnot hcosn hcosns
  have hcard_div :=
    complement_small_card_div_le_inv (R := R) (u := u) hRpos huodd.pos
  have hcos_abs_pos : 0 < |Real.cos ((n : ℝ) * theta0)| := abs_pos.mpr hcosn
  have hu_ne_real : (u : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt huodd.pos
  have hR_ne_real : (R : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hRpos
  have hcos_abs_ne : |Real.cos ((n : ℝ) * theta0)| ≠ 0 :=
    ne_of_gt hcos_abs_pos
  calc
    |rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n)| ≤
        (1 / ((u : ℝ) * |Real.cos ((n : ℝ) * theta0)|)) *
          (((Nat.divisors u).filter fun t => R * t < u).card : ℝ) := hbase
    _ = ((((Nat.divisors u).filter fun t => R * t < u).card : ℝ) / (u : ℝ)) *
          (1 / |Real.cos ((n : ℝ) * theta0)|) := by
          field_simp [hu_ne_real, hcos_abs_ne]
    _ ≤ (1 / (R : ℝ)) * (1 / |Real.cos ((n : ℝ) * theta0)|) := by
          exact mul_le_mul_of_nonneg_right hcard_div (by positivity)
    _ = 1 / ((R : ℝ) * |Real.cos ((n : ℝ) * theta0)|) := by
          field_simp [hR_ne_real, hcos_abs_ne]

lemma abs_rowEval_finiteSpikeRaw_odd_le_inv_R_kappa
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ} {kappa : ℝ}
    (hRpos : 0 < R) (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    |rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n)| ≤
      1 / ((R : ℝ) * kappa) := by
  have hcosn : Real.cos ((n : ℝ) * theta0) ≠ 0 := by
    intro h
    have : |Real.cos ((n : ℝ) * theta0)| = 0 := by simp [h]
    linarith
  have hbase :=
    abs_rowEval_finiteSpikeRaw_odd_le_inv_R_abs_cos
      (R := R) htheta0 hRpos hnpos huodd hu_ne hnot hcosn hcosns
  have hR_pos_real : 0 < (R : ℝ) := by
    exact_mod_cast hRpos
  have hden_pos : 0 < (R : ℝ) * kappa := mul_pos hR_pos_real hkappa_pos
  have hden_le :
      (R : ℝ) * kappa ≤
        (R : ℝ) * |Real.cos ((n : ℝ) * theta0)| := by
    exact mul_le_mul_of_nonneg_left hkappa_le (le_of_lt hR_pos_real)
  exact hbase.trans (one_div_le_one_div_of_le hden_pos hden_le)

lemma sqrt_nat_le_self {R : ℕ} (hR : 1 ≤ R) :
    Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
  have hR_nonneg : 0 ≤ (R : ℝ) := by positivity
  have hsq : (Real.sqrt (R : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by
    rw [Real.sq_sqrt hR_nonneg]
    nlinarith [show (1 : ℝ) ≤ (R : ℝ) by exact_mod_cast hR]
  have habs := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hR_nonneg] using habs

lemma one_div_nat_le_one_div_sqrt {R : ℕ} (hR : 1 ≤ R) :
    1 / (R : ℝ) ≤ 1 / Real.sqrt (R : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt (R : ℝ) := by
    exact Real.sqrt_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
  exact one_div_le_one_div_of_le hsqrt_pos (sqrt_nat_le_self hR)

lemma inv_R_kappa_le_sqrt {R : ℕ} {kappa : ℝ}
    (hR : 1 ≤ R) (hkappa_pos : 0 < kappa) :
    1 / ((R : ℝ) * kappa) ≤ (1 / kappa) / Real.sqrt (R : ℝ) := by
  have hR_ne : (R : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hk_ne : kappa ≠ 0 := ne_of_gt hkappa_pos
  have hsqrt_ne : Real.sqrt (R : ℝ) ≠ 0 := by
    exact ne_of_gt
      (Real.sqrt_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)))
  have hbase := one_div_nat_le_one_div_sqrt hR
  have hmul := mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ 1 / kappa)
  calc
    1 / ((R : ℝ) * kappa) = (1 / (R : ℝ)) * (1 / kappa) := by
      field_simp [hR_ne, hk_ne]
    _ ≤ (1 / Real.sqrt (R : ℝ)) * (1 / kappa) := hmul
    _ = (1 / kappa) / Real.sqrt (R : ℝ) := by
      field_simp [hk_ne, hsqrt_ne]

lemma abs_rowEval_finiteSpikeRaw_odd_le_sqrt_kappa
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n u : ℕ} {kappa : ℝ}
    (hR : 1 ≤ R) (hnpos : 0 < n) (huodd : Odd u) (hu_ne : u ≠ 1)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hnot : ¬ IsNodeRow theta0 (n * u))
    (hcosns : ∀ s : ℕ, s ∈ oddUpTo R → s ∣ u →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    |rowEval theta0 (n * u) (finiteSpikeRaw theta0 R n)| ≤
      (1 / kappa) / Real.sqrt (R : ℝ) := by
  have hRpos : 0 < R := lt_of_lt_of_le Nat.zero_lt_one hR
  have hbase :=
    abs_rowEval_finiteSpikeRaw_odd_le_inv_R_kappa
      (R := R) htheta0 hRpos hnpos huodd hu_ne
      hkappa_pos hkappa_le hnot hcosns
  exact hbase.trans (inv_R_kappa_le_sqrt hR hkappa_pos)

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
  rw [row_sum_finiteSpikeRaw_eq_oddUpTo_if hnpos huodd
    (fun s _hs hdiv => hcosns s hdiv)
    (fun s _hs hdiv => hV s hdiv)]
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

lemma rowEval_finiteSpikeRaw_future_le_sqrt_kappa
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n j : ℕ} {kappa : ℝ}
    (hR : 1 ≤ R) (hnpos : 0 < n) (hfuture : R * n < j)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    |rowEval theta0 j (finiteSpikeRaw theta0 R n)| ≤
      (1 / kappa) / Real.sqrt (R : ℝ) := by
  have htarget_nonneg : 0 ≤ (1 / kappa) / Real.sqrt (R : ℝ) := by
    positivity
  have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le _) hfuture
  by_cases hndiv : n ∣ j
  · rcases hndiv with ⟨u, hju⟩
    have hu_gt_R : R < u := by
      have hmul : n * R < n * u := by
        simpa [hju, Nat.mul_comm] using hfuture
      exact (Nat.mul_lt_mul_left hnpos).mp hmul
    have hupos : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hu_gt_R
    by_cases huodd : Odd u
    · have hu_ne : u ≠ 1 := by omega
      by_cases hnode : IsNodeRow theta0 (n * u)
      · rw [hju, rowEval_finiteSpikeRaw_of_isNodeRow_odd hnpos huodd hnode hcos]
        simpa using htarget_nonneg
      · rw [hju]
        exact abs_rowEval_finiteSpikeRaw_odd_le_sqrt_kappa
          htheta0 hR hnpos huodd hu_ne hkappa_pos hkappa_le hnode
          (fun s hs _hdiv => hcos s hs)
    · rw [hju, rowEval_finiteSpikeRaw_eq_zero_of_not_odd_multiple hnpos hupos huodd hcos]
      simpa using htarget_nonneg
  · rw [rowEval_finiteSpikeRaw_eq_zero_of_base_not_dvd hnpos hjpos hndiv hcos]
    simpa using htarget_nonneg

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

lemma rowEval_finiteSpikeRaw_block_and_future_of_good_rows
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n : ℕ} {kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    rowEval theta0 n (finiteSpikeRaw theta0 R n) = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        rowEval theta0 j (finiteSpikeRaw theta0 R n) = 0) ∧
      (∀ j : ℕ, R * n < j →
        |rowEval theta0 j (finiteSpikeRaw theta0 R n)| ≤
          (1 / kappa) / Real.sqrt (R : ℝ)) := by
  have hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0 := by
    intro s hs
    have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hnot : ¬ IsNodeRow theta0 (n * s) := by
      simpa [IsNodeRow] using hcos s hs
    exact Vprim_ne_zero_of_not_isNodeRow htheta0 hdpos hnot
  have hblock := rowEval_finiteSpikeRaw_block_rows hnpos hR hcos hV
  exact ⟨hblock.1, hblock.2,
    fun j hj => rowEval_finiteSpikeRaw_future_le_sqrt_kappa
      htheta0 hR hnpos hj hkappa_pos hkappa_le hcos⟩

lemma exists_finiteSpikeRaw_block_and_future_good_pow_two
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R N : ℕ}
    (hR : 1 ≤ R) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      rowEval theta0 n (finiteSpikeRaw theta0 R n) = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        rowEval theta0 j (finiteSpikeRaw theta0 R n) = 0) ∧
      (∀ j : ℕ, R * n < j →
        |rowEval theta0 j (finiteSpikeRaw theta0 R n)| ≤
          (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ)) := by
  rcases exists_large_pow_two_good_cos_oddUpTo theta0 R N with
    ⟨n, hnN, hpow, hnpos, hcosn, hcos⟩
  have hpack :=
    rowEval_finiteSpikeRaw_block_and_future_of_good_rows
      (theta0 := theta0) htheta0 (R := R) (n := n) (kappa := (1 / 2 : ℝ))
      hnpos hR (by norm_num) hcosn hcos
  exact ⟨n, hnN, hpow, hnpos, hpack.1, hpack.2.1, hpack.2.2⟩

lemma log_nat_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  exact Real.log_pos hnreal

lemma abs_le_add_of_sub_abs_le {x y eta delta : ℝ}
    (hy : |y| ≤ eta) (hxy : |x - y| ≤ delta) :
    |x| ≤ eta + delta := by
  have htri : |x| ≤ |x - y| + |y| := by
    have h := abs_add_le (x - y) y
    have hsum : x - y + y = x := by ring
    simpa [hsum] using h
  linarith

lemma F_future_bound_of_rowEval_finiteSpikeRaw_close
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) {R n : ℕ} {kappa delta : ℝ}
    (hR : 1 ≤ R) (hnpos : 0 < n)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    {psi : AngleFun}
    (hclose : ∀ j : ℕ, R * n < j →
      |F theta0 j psi - rowEval theta0 j (finiteSpikeRaw theta0 R n)| ≤ delta) :
    ∀ j : ℕ, R * n < j →
      |F theta0 j psi| ≤ (1 / kappa) / Real.sqrt (R : ℝ) + delta := by
  intro j hj
  exact abs_le_add_of_sub_abs_le
    (rowEval_finiteSpikeRaw_future_le_sqrt_kappa
      htheta0 hR hnpos hj hkappa_pos hkappa_le hcos)
    (hclose j hj)

lemma exists_F_abs_le_of_tendsto_zero
    {theta0 : ℝ} {psi : AngleFun}
    (hlim : Filter.Tendsto (fun j : ℕ => F theta0 j psi) Filter.atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ K : ℕ, ∀ j : ℕ, K ≤ j → |F theta0 j psi| ≤ delta := by
  have hevent :
      ∀ᶠ j : ℕ in Filter.atTop, |F theta0 j psi| < delta := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim delta hdelta)
  rcases Filter.eventually_atTop.mp hevent with ⟨K, hK⟩
  exact ⟨K, fun j hj => le_of_lt (hK j hj)⟩

lemma F_future_bound_of_finite_cutoff_and_tail
    {theta0 : ℝ} {R n K : ℕ} {psi : AngleFun} {eta delta : ℝ}
    (heta_nonneg : 0 ≤ eta) (hdelta_nonneg : 0 ≤ delta)
    (hfinite : ∀ j : ℕ, R * n < j → j ≤ K →
      |F theta0 j psi| ≤ eta)
    (htail : ∀ j : ℕ, K < j → |F theta0 j psi| ≤ delta) :
    ∀ j : ℕ, R * n < j → |F theta0 j psi| ≤ eta + delta := by
  intro j hjfuture
  by_cases hjK : j ≤ K
  · exact (hfinite j hjfuture hjK).trans (by linarith)
  · have hKj : K < j := Nat.lt_of_not_ge hjK
    exact (htail j hKj).trans (by linarith)

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

lemma finiteSpikeRaw_abs_le_on_spikePoints_of_primitive_bound
    {theta0 : ℝ} {R n : ℕ} {B : ℝ} (hnpos : 0 < n)
    (hbound : ∀ s : ℕ, s ∈ oddUpTo R → ∀ k : ℕ, k ∈ primIdx (n * s) →
      |finiteSpikeValueAtPrimitive theta0 n s k| ≤ B) :
    ∀ p : ℝ, p ∈ spikePoints n R → |finiteSpikeRaw theta0 R n p| ≤ B := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, hp_eq⟩
  have hqmem := mem_spikeIdx_iff.mp hq
  rw [← hp_eq]
  rw [finiteSpikeRaw_at_primitive hnpos hqmem.1 hqmem.2]
  exact hbound q.1 hqmem.1 q.2 hqmem.2

lemma finiteSpikeRaw_abs_le_on_spikePoints_of_coeff_bound
    {theta0 : ℝ} {R n : ℕ} {B : ℝ} (hnpos : 0 < n)
    (hVpos : ∀ s : ℕ, s ∈ oddUpTo R → 0 < Vprim theta0 (n * s))
    (hcoeff : ∀ s : ℕ, s ∈ oddUpTo R →
      |spikeCoeff theta0 n s| / Vprim theta0 (n * s) ≤ B) :
    ∀ p : ℝ, p ∈ spikePoints n R → |finiteSpikeRaw theta0 R n p| ≤ B := by
  exact finiteSpikeRaw_abs_le_on_spikePoints_of_primitive_bound hnpos
    (fun s hs k _hk =>
      abs_finiteSpikeValueAtPrimitive_le (hVpos s hs) (hcoeff s hs))

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

lemma nodesUpTo_mono {K L : ℕ} (hKL : K ≤ L) :
    nodesUpTo K ⊆ nodesUpTo L := by
  classical
  intro theta htheta
  unfold nodesUpTo at htheta ⊢
  rcases Finset.mem_image.mp htheta with ⟨p, hp, rfl⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨p, ?_, rfl⟩
  rcases Finset.mem_sigma.mp hp with ⟨hpIcc, hprange⟩
  exact Finset.mem_sigma.mpr
    ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hpIcc).1,
        (Finset.mem_Icc.mp hpIcc).2.trans hKL⟩,
      hprange⟩

lemma spikePoints_subset_nodesUpTo_of_le
    {R n K : ℕ} (hnpos : 0 < n) (hRK : R * n ≤ K) :
    spikePoints n R ⊆ nodesUpTo K := by
  intro theta htheta
  exact nodesUpTo_mono hRK (spikePoints_subset_nodesUpTo hnpos htheta)

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
      (∀ p : ℝ, p ∈ P → ∀ q : ℝ, q ∈ P → p ≠ q →
        radius p + radius q ≤ |p - q|) ∧
      (∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps →
        ∀ p : ℝ, p ∈ P → radius p ≤ |theta - p|) := by
  classical
  rcases finite_set_pair_positive_separation E with ⟨rho, hrho, hpair⟩
  let radius : ℝ → ℝ := fun _ => rho / 4
  refine ⟨radius, ?_, ?_, ?_, ?_⟩
  · intro p hp
    dsimp [radius]
    positivity
  · intro p hp e he hne
    have hpE : p ∈ E := hPE hp
    have hle : rho ≤ |e - p| := hpair e he p hpE hne
    dsimp [radius]
    linarith
  · intro p hp q hq hpq
    have hpE : p ∈ E := hPE hp
    have hqE : q ∈ E := hPE hq
    have hle : rho ≤ |p - q| := hpair p hpE q hqE hpq
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

lemma F_continuousSpike_block_and_finite_future_of_good_rows
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K : ℕ} {kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R) (hRK : R * n ≤ K)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo K) → e ≠ p →
        radius p ≤ |e - p|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
    F theta0 n
        (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)) = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j
          (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)) = 0) ∧
      (∀ j : ℕ, R * n < j → j ≤ K →
        |F theta0 j
          (continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n))| ≤
            (1 / kappa) / Real.sqrt (R : ℝ)) := by
  have hraw :=
    rowEval_finiteSpikeRaw_block_and_future_of_good_rows
      htheta0 hnpos hR hkappa_pos hkappa_le hcos
  have hnK : n ≤ K := by
    have hn_le_Rn : n ≤ R * n := by
      simpa [one_mul] using Nat.mul_le_mul_right n hR
    exact hn_le_Rn.trans hRK
  refine ⟨?_, ?_, ?_⟩
  · rw [F_continuousSpike_eq_rowEval_finiteSpikeRaw
      htheta0 hnK hradpos hsep]
    exact hraw.1
  · intro j hjpos hjle hjne
    have hjK : j ≤ K := hjle.trans hRK
    rw [F_continuousSpike_eq_rowEval_finiteSpikeRaw
      htheta0 hjK hradpos hsep]
    exact hraw.2.1 j hjpos hjle hjne
  · intro j hjfuture hjK
    rw [F_continuousSpike_eq_rowEval_finiteSpikeRaw
      htheta0 hjK hradpos hsep]
    exact hraw.2.2 j hjfuture

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

lemma abs_continuousSpikeRaw_le_height_bound
    {P : Finset ℝ} {radius height : ℝ → ℝ} {B theta : ℝ}
    (hB : 0 ≤ B)
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ P → ∀ q : ℝ, q ∈ P → p ≠ q →
      radius p + radius q ≤ |p - q|)
    (hheight : ∀ p : ℝ, p ∈ P → |height p| ≤ B) :
    |continuousSpikeRaw P radius height theta| ≤ B := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [continuousSpikeRaw, hB]
  | insert a P haP ih =>
      have hrad_a : 0 < radius a := hradpos a (Finset.mem_insert_self a P)
      rw [continuousSpikeRaw, Finset.sum_insert haP]
      by_cases hfar_a : radius a ≤ |theta - a|
      · have htent_a : tent a (radius a) (height a) theta = 0 :=
          tent_eq_zero_of_radius_le hrad_a hfar_a
        rw [htent_a, zero_add]
        have hradP : ∀ p : ℝ, p ∈ P → 0 < radius p := by
          intro p hp
          exact hradpos p (Finset.mem_insert_of_mem hp)
        have hsepP : ∀ p : ℝ, p ∈ P → ∀ q : ℝ, q ∈ P → p ≠ q →
            radius p + radius q ≤ |p - q| := by
          intro p hp q hq hpq
          exact hsep p (Finset.mem_insert_of_mem hp)
            q (Finset.mem_insert_of_mem hq) hpq
        have hheightP : ∀ p : ℝ, p ∈ P → |height p| ≤ B := by
          intro p hp
          exact hheight p (Finset.mem_insert_of_mem hp)
        simpa [continuousSpikeRaw] using ih hradP hsepP hheightP
      · have hnear_a : |theta - a| < radius a := lt_of_not_ge hfar_a
        have hfarP : ∀ p : ℝ, p ∈ P → radius p ≤ |theta - p| := by
          intro p hp
          by_contra hnot
          have hnear_p : |theta - p| < radius p := lt_of_not_ge hnot
          have hap : a ≠ p := by
            intro hap
            exact haP (hap ▸ hp)
          have hsep_ap : radius a + radius p ≤ |a - p| :=
            hsep a (Finset.mem_insert_self a P)
              p (Finset.mem_insert_of_mem hp) hap
          have htri : |a - p| ≤ |theta - a| + |theta - p| := by
            have h := abs_add_le (a - theta) (theta - p)
            have hsum : a - theta + (theta - p) = a - p := by ring
            simpa [hsum, abs_sub_comm a theta] using h
          have hlt : |theta - a| + |theta - p| < radius a + radius p :=
            add_lt_add hnear_a hnear_p
          linarith
        have hsumP : (∑ p ∈ P, tent p (radius p) (height p) theta) = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          exact tent_eq_zero_of_radius_le
            (hradpos p (Finset.mem_insert_of_mem hp)) (hfarP p hp)
        rw [hsumP, add_zero]
        exact (abs_tent_le_abs_height hrad_a).trans
          (hheight a (Finset.mem_insert_self a P))

lemma norm_continuousSpike_le_sum_abs_height
    {P : Finset ℝ} {radius height : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p) :
    ‖continuousSpike P radius height‖ ≤ ∑ p ∈ P, |height p| := by
  rw [ContinuousMap.norm_le _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  intro theta
  simpa [Real.norm_eq_abs, continuousSpike] using
    abs_continuousSpikeRaw_le_sum_abs_height
      (P := P) (radius := radius) (height := height) (theta := theta.1) hradpos

lemma norm_continuousSpike_le_height_bound
    {P : Finset ℝ} {radius height : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hradpos : ∀ p : ℝ, p ∈ P → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ P → ∀ q : ℝ, q ∈ P → p ≠ q →
      radius p + radius q ≤ |p - q|)
    (hheight : ∀ p : ℝ, p ∈ P → |height p| ≤ B) :
    ‖continuousSpike P radius height‖ ≤ B := by
  rw [ContinuousMap.norm_le _ hB]
  intro theta
  simpa [Real.norm_eq_abs, continuousSpike] using
    abs_continuousSpikeRaw_le_height_bound
      (P := P) (radius := radius) (height := height)
      (B := B) (theta := theta.1) hB hradpos hsep hheight

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

lemma exists_continuousSpike_exact_block_norm_le
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R) {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo (R * n)) → e ≠ p →
        radius p ≤ |e - p|)
    (hpairsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ q : ℝ, q ∈ spikePoints n R → p ≠ q →
        radius p + radius q ≤ |p - q|)
    (haway : ∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps →
      ∀ p : ℝ, p ∈ spikePoints n R → radius p ≤ |theta - p|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ p : ℝ, p ∈ spikePoints n R →
      |finiteSpikeRaw theta0 R n p| ≤ B) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ B := by
  let psi : AngleFun :=
    continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)
  have hblock :=
    F_continuousSpike_block_rows
      (theta0 := theta0) htheta0 hnpos hR hradpos hsep hcos hV
  refine ⟨psi, ?_, hblock.1, hblock.2, ?_⟩
  · exact continuousSpike_vanishesNear_of_radius_away hradpos haway
  · exact norm_continuousSpike_le_height_bound hB hradpos hpairsep hheight

lemma exists_continuousSpike_block_and_finite_future_norm_le
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K : ℕ} {kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R) (hRK : R * n ≤ K)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    {radius : ℝ → ℝ}
    (hradpos : ∀ p : ℝ, p ∈ spikePoints n R → 0 < radius p)
    (hsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ e : ℝ, e ∈ insert theta0 (nodesUpTo K) → e ≠ p →
        radius p ≤ |e - p|)
    (hpairsep : ∀ p : ℝ, p ∈ spikePoints n R →
      ∀ q : ℝ, q ∈ spikePoints n R → p ≠ q →
        radius p + radius q ≤ |p - q|)
    (haway : ∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps →
      ∀ p : ℝ, p ∈ spikePoints n R → radius p ≤ |theta - p|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ p : ℝ, p ∈ spikePoints n R →
      |finiteSpikeRaw theta0 R n p| ≤ B) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      (∀ j : ℕ, R * n < j → j ≤ K →
        |F theta0 j psi| ≤ (1 / kappa) / Real.sqrt (R : ℝ)) ∧
      ‖psi‖ ≤ B := by
  let psi : AngleFun :=
    continuousSpike (spikePoints n R) radius (finiteSpikeRaw theta0 R n)
  have hpack :=
    F_continuousSpike_block_and_finite_future_of_good_rows
      (theta0 := theta0) htheta0 hnpos hR hRK
      hkappa_pos hkappa_le hradpos hsep hcos
  refine ⟨psi, ?_, hpack.1, hpack.2.1, hpack.2.2, ?_⟩
  · exact continuousSpike_vanishesNear_of_radius_away hradpos haway
  · exact norm_continuousSpike_le_height_bound hB hradpos hpairsep hheight

lemma exists_continuousSpike_exact_block_of_good_rows
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) :
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
    ⟨radius, hradpos, hsep, _hpairsep, haway⟩
  have hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0 := by
    intro s hs
    have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hnot : ¬ IsNodeRow theta0 (n * s) := by
      simpa [IsNodeRow] using hcos s hs
    exact Vprim_ne_zero_of_not_isNodeRow htheta0 hdpos hnot
  exact exists_continuousSpike_exact_block
    htheta0 hnpos hR hradpos hsep haway hcos hV

lemma exists_continuousSpike_exact_block_of_good_rows_norm_le
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ p : ℝ, p ∈ spikePoints n R →
      |finiteSpikeRaw theta0 R n p| ≤ B) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ B := by
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
    ⟨radius, hradpos, hsep, hpairsep, haway⟩
  have hV : ∀ s : ℕ, s ∈ oddUpTo R → Vprim theta0 (n * s) ≠ 0 := by
    intro s hs
    have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hnot : ¬ IsNodeRow theta0 (n * s) := by
      simpa [IsNodeRow] using hcos s hs
    exact Vprim_ne_zero_of_not_isNodeRow htheta0 hdpos hnot
  exact exists_continuousSpike_exact_block_norm_le
    htheta0 hnpos hR hradpos hsep hpairsep haway hcos hV hB hheight

lemma exists_continuousSpike_block_and_finite_future_of_good_rows_norm_le
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K : ℕ} {kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R) (hRK : R * n ≤ K)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hheight : ∀ p : ℝ, p ∈ spikePoints n R →
      |finiteSpikeRaw theta0 R n p| ≤ B) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      (∀ j : ℕ, R * n < j → j ≤ K →
        |F theta0 j psi| ≤ (1 / kappa) / Real.sqrt (R : ℝ)) ∧
      ‖psi‖ ≤ B := by
  classical
  let E : Finset ℝ := insert theta0 (nodesUpTo K)
  have hPE : spikePoints n R ⊆ E := by
    intro p hp
    exact Finset.mem_insert.mpr
      (Or.inr (spikePoints_subset_nodesUpTo_of_le hnpos hRK hp))
  have hthetaE : theta0 ∈ E := Finset.mem_insert_self _ _
  have hthetaP : theta0 ∉ spikePoints n R :=
    theta0_not_mem_spikePoints_of_good_rows hcos
  rcases exists_constant_isolating_radius
      (P := spikePoints n R) (E := E) (theta0 := theta0)
      hPE hthetaE hthetaP with
    ⟨radius, hradpos, hsep, hpairsep, haway⟩
  exact exists_continuousSpike_block_and_finite_future_norm_le
    htheta0 hnpos hR hRK hkappa_pos hkappa_le
    hradpos hsep hpairsep haway hcos hB hheight

lemma exists_continuousSpike_exact_block_of_good_rows_coeff_bound
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ s : ℕ, s ∈ oddUpTo R →
      |spikeCoeff theta0 n s| / Vprim theta0 (n * s) ≤ B) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ B := by
  have hVpos : ∀ s : ℕ, s ∈ oddUpTo R → 0 < Vprim theta0 (n * s) := by
    intro s hs
    have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hnot : ¬ IsNodeRow theta0 (n * s) := by
      simpa [IsNodeRow] using hcos s hs
    exact Vprim_pos_of_not_isNodeRow htheta0 hdpos hnot
  have hheight :
      ∀ p : ℝ, p ∈ spikePoints n R →
        |finiteSpikeRaw theta0 R n p| ≤ B :=
    finiteSpikeRaw_abs_le_on_spikePoints_of_coeff_bound
      hnpos hVpos hcoeff
  exact exists_continuousSpike_exact_block_of_good_rows_norm_le
    htheta0 hnpos hR hcos hB hheight

lemma exists_continuousSpike_block_and_finite_future_of_good_rows_coeff_bound
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K : ℕ} {kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R) (hRK : R * n ≤ K)
    (hkappa_pos : 0 < kappa)
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ s : ℕ, s ∈ oddUpTo R →
      |spikeCoeff theta0 n s| / Vprim theta0 (n * s) ≤ B) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      (∀ j : ℕ, R * n < j → j ≤ K →
        |F theta0 j psi| ≤ (1 / kappa) / Real.sqrt (R : ℝ)) ∧
      ‖psi‖ ≤ B := by
  have hVpos : ∀ s : ℕ, s ∈ oddUpTo R → 0 < Vprim theta0 (n * s) := by
    intro s hs
    have hspos : 0 < s := (mem_oddUpTo_iff.mp hs).2.2.pos
    have hdpos : 0 < n * s := Nat.mul_pos hnpos hspos
    have hnot : ¬ IsNodeRow theta0 (n * s) := by
      simpa [IsNodeRow] using hcos s hs
    exact Vprim_pos_of_not_isNodeRow htheta0 hdpos hnot
  have hheight :
      ∀ p : ℝ, p ∈ spikePoints n R →
        |finiteSpikeRaw theta0 R n p| ≤ B :=
    finiteSpikeRaw_abs_le_on_spikePoints_of_coeff_bound
      hnpos hVpos hcoeff
  exact exists_continuousSpike_block_and_finite_future_of_good_rows_norm_le
    htheta0 hnpos hR hRK hkappa_pos hkappa_le hcos hB hheight

lemma exists_continuousSpike_exact_block_of_good_rows_Vprim_lower
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n : ℕ} {c kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R)
    (hcpos : 0 < c) (hkpos : 0 < kappa)
    (hlogpos : 0 < Real.log (n : ℝ))
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hmass : ∀ s : ℕ, s ∈ oddUpTo R →
      c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| * Real.log (n : ℝ) ≤
        Vprim theta0 (n * s)) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ (1 / (c * kappa)) / Real.log (n : ℝ) := by
  have hB : 0 ≤ (1 / (c * kappa)) / Real.log (n : ℝ) := by
    positivity
  exact exists_continuousSpike_exact_block_of_good_rows_coeff_bound
    htheta0 hnpos hR hcos hB
    (coeff_bound_of_Vprim_lower hcpos hkpos hlogpos hkappa_le hcos hmass)

lemma exists_continuousSpike_exact_block_good_pow_two_of_Vprim_lower
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R N : ℕ} {c : ℝ}
    (hR : 1 ≤ R) (hcpos : 0 < c)
    (hmass : ∀ n : ℕ, N ≤ n → IsPowTwo n → 0 < n →
      (∀ s : ℕ, s ∈ oddUpTo R →
        Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) →
      ∀ s : ℕ, s ∈ oddUpTo R →
        c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| *
            Real.log (n : ℝ) ≤ Vprim theta0 (n * s)) :
    ∃ n : ℕ, ∃ psi : AngleFun,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      ‖psi‖ ≤ (1 / (c * (1 / 2 : ℝ))) / Real.log (n : ℝ) := by
  rcases exists_large_pow_two_good_cos_oddUpTo theta0 R (max N 2) with
    ⟨n, hnmax, hpow, hnpos, hkappa_le, hcos⟩
  have hnN : N ≤ n := (le_max_left N 2).trans hnmax
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hnmax
  have hlogpos : 0 < Real.log (n : ℝ) := log_nat_pos_of_two_le hn2
  rcases exists_continuousSpike_exact_block_of_good_rows_Vprim_lower
      (theta0 := theta0) htheta0
      (R := R) (n := n) (c := c) (kappa := (1 / 2 : ℝ))
      hnpos hR hcpos (by norm_num) hlogpos hkappa_le hcos
      (hmass n hnN hpow hnpos hcos) with
    ⟨psi, hvanish, hhit, hearly, hnorm⟩
  exact ⟨n, psi, hnN, hpow, hnpos, hvanish, hhit, hearly, hnorm⟩

lemma exists_continuousSpike_block_and_finite_future_of_good_rows_Vprim_lower
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R n K : ℕ} {c kappa : ℝ}
    (hnpos : 0 < n) (hR : 1 ≤ R) (hRK : R * n ≤ K)
    (hcpos : 0 < c) (hkpos : 0 < kappa)
    (hlogpos : 0 < Real.log (n : ℝ))
    (hkappa_le : kappa ≤ |Real.cos ((n : ℝ) * theta0)|)
    (hcos : ∀ s : ℕ, s ∈ oddUpTo R →
      Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0)
    (hmass : ∀ s : ℕ, s ∈ oddUpTo R →
      c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| * Real.log (n : ℝ) ≤
        Vprim theta0 (n * s)) :
    ∃ psi : AngleFun,
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
        F theta0 j psi = 0) ∧
      (∀ j : ℕ, R * n < j → j ≤ K →
        |F theta0 j psi| ≤ (1 / kappa) / Real.sqrt (R : ℝ)) ∧
      ‖psi‖ ≤ (1 / (c * kappa)) / Real.log (n : ℝ) := by
  have hB : 0 ≤ (1 / (c * kappa)) / Real.log (n : ℝ) := by
    positivity
  exact exists_continuousSpike_block_and_finite_future_of_good_rows_coeff_bound
    htheta0 hnpos hR hRK hkpos hkappa_le hcos hB
    (coeff_bound_of_Vprim_lower hcpos hkpos hlogpos hkappa_le hcos hmass)

lemma exists_good_pow_two_with_continuousSpike_finite_future_of_Vprim_lower
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R N : ℕ} {c : ℝ}
    (hR : 1 ≤ R) (hcpos : 0 < c)
    (hmass : ∀ n : ℕ, N ≤ n → IsPowTwo n → 0 < n →
      (∀ s : ℕ, s ∈ oddUpTo R →
        Real.cos (((n * s : ℕ) : ℝ) * theta0) ≠ 0) →
      ∀ s : ℕ, s ∈ oddUpTo R →
        c * |Real.cos (((n * s : ℕ) : ℝ) * theta0)| *
            Real.log (n : ℝ) ≤ Vprim theta0 (n * s)) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear theta0 (angleFunToRaw psi) ∧
          F theta0 n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F theta0 j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F theta0 j psi| ≤ (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ)) ∧
          ‖psi‖ ≤ (1 / (c * (1 / 2 : ℝ))) / Real.log (n : ℝ)) := by
  rcases exists_large_pow_two_good_cos_oddUpTo theta0 R (max N 2) with
    ⟨n, hnmax, hpow, hnpos, hkappa_le, hcos⟩
  have hnN : N ≤ n := (le_max_left N 2).trans hnmax
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hnmax
  have hlogpos : 0 < Real.log (n : ℝ) := log_nat_pos_of_two_le hn2
  refine ⟨n, hnN, hpow, hnpos, ?_⟩
  intro K hRK
  exact exists_continuousSpike_block_and_finite_future_of_good_rows_Vprim_lower
    (theta0 := theta0) htheta0
    (R := R) (n := n) (K := K) (c := c) (kappa := (1 / 2 : ℝ))
    hnpos hR hRK hcpos (by norm_num) hlogpos hkappa_le hcos
    (hmass n hnN hpow hnpos hcos)

lemma exists_good_pow_two_with_continuousSpike_finite_future_interior_of_kernel_params
    {theta0 c rho : ℝ} {Q R N : ℕ}
    (htheta0 : theta0 ∈ AngleI) (hcpos : 0 < c)
    (hQpos : 0 < Q) (hR : 1 ≤ R)
    (hrange : theta0 / Real.pi + 1 / (Q : ℝ) ≤ 1)
    (hQrho : Real.pi / (Q : ℝ) < rho)
    (hlocal : ∀ theta ∈ AngleI, theta ≠ theta0 →
      |theta - theta0| < rho →
        c / |theta - theta0| ≤
          Real.sin theta / |Real.cos theta0 - Real.cos theta|) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear theta0 (angleFunToRaw psi) ∧
          F theta0 n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F theta0 j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F theta0 j psi| ≤ (1 / (1 / 2 : ℝ)) /
              Real.sqrt (R : ℝ)) ∧
          ‖psi‖ ≤
            1 / (((c / (2 * Real.pi)) / (R : ℝ)) * (1 / 2 : ℝ)) /
              Real.log (n : ℝ)) := by
  have hRpos : 0 < R := lt_of_lt_of_le Nat.zero_lt_one hR
  have hcbase_pos : 0 < c / (2 * Real.pi) := by
    positivity
  have hcmass_pos : 0 < (c / (2 * Real.pi)) / (R : ℝ) := by
    positivity
  rcases exists_good_pow_two_with_continuousSpike_finite_future_of_Vprim_lower
      (theta0 := theta0) htheta0 (R := R) (N := max N (Q ^ 2))
      (c := (c / (2 * Real.pi)) / (R : ℝ)) hR hcmass_pos
      (fun n hnmax hpow hnpos hcos s hs => by
        have hnNQ : Q ^ 2 ≤ n := (le_max_right N (Q ^ 2)).trans hnmax
        have hs_info := mem_oddUpTo_iff.mp hs
        have hspos : 0 < s := hs_info.2.2.pos
        have hsR : s ≤ R := hs_info.2.1
        have hnot : ¬ IsNodeRow theta0 (n * s) := hcos s hs
        have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
          exact Real.log_nonneg
            (by exact_mod_cast (Nat.succ_le_iff.mpr hnpos))
        exact Vprim_lower_of_progression_kernel_lower_base
          (theta0 := theta0) (c := c / (2 * Real.pi))
          (R := R) (n := n) (s := s)
          hpow hnpos hRpos hspos hsR (le_of_lt hcbase_pos)
          hlog_nonneg
          (interior_progression_kernel_sum_ge_log_of_div_block
            (theta0 := theta0) (c := c) (rho := rho)
            (n := n) (s := s) (Q := Q)
            hnpos hspos hQpos hnNQ (le_of_lt hcpos) htheta0.1
            hnot hlocal hrange hQrho)) with
    ⟨n, hnmax, hpow, hnpos, hK⟩
  exact ⟨n, (le_max_left N (Q ^ 2)).trans hnmax, hpow, hnpos, hK⟩

lemma exists_nat_good_interior_divisor
    {theta0 rho : ℝ} (hpi : theta0 < Real.pi) (hrho : 0 < rho) :
    ∃ Q : ℕ, 0 < Q ∧
      theta0 / Real.pi + 1 / (Q : ℝ) ≤ 1 ∧
      Real.pi / (Q : ℝ) < rho := by
  have hdpos : 0 < Real.pi - theta0 := sub_pos.mpr hpi
  rcases exists_nat_gt (max (1 : ℝ)
      (max (Real.pi / (Real.pi - theta0)) (Real.pi / rho))) with
    ⟨Q, hQ⟩
  have hQ_gt_one : (1 : ℝ) < (Q : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hQ
  have hQpos : 0 < Q := by
    exact_mod_cast
      (lt_trans (by norm_num : (0 : ℝ) < 1) hQ_gt_one)
  have hQpos_real : 0 < (Q : ℝ) := by
    exact_mod_cast hQpos
  have hQtheta_large :
      Real.pi / (Real.pi - theta0) < (Q : ℝ) := by
    exact lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQrho_large : Real.pi / rho < (Q : ℝ) := by
    exact lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hpi_lt_Qd : Real.pi < (Q : ℝ) * (Real.pi - theta0) := by
    have hmul := mul_lt_mul_of_pos_right hQtheta_large hdpos
    have hleft :
        (Real.pi / (Real.pi - theta0)) * (Real.pi - theta0) =
          Real.pi := by
      field_simp [ne_of_gt hdpos]
    nlinarith
  have hone_div_le :
      1 / (Q : ℝ) ≤ (Real.pi - theta0) / Real.pi := by
    rw [div_le_iff₀ hQpos_real]
    have htarget :
        1 ≤ ((Real.pi - theta0) / Real.pi) * (Q : ℝ) := by
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using htarget
  have hrange : theta0 / Real.pi + 1 / (Q : ℝ) ≤ 1 := by
    calc
      theta0 / Real.pi + 1 / (Q : ℝ) ≤
          theta0 / Real.pi + (Real.pi - theta0) / Real.pi := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hone_div_le (theta0 / Real.pi)
      _ = 1 := by
          field_simp [Real.pi_ne_zero]
          ring
  have hpi_div_Q_lt : Real.pi / (Q : ℝ) < rho := by
    rw [div_lt_iff₀ hQpos_real]
    have hmul := mul_lt_mul_of_pos_right hQrho_large hrho
    have hleft : (Real.pi / rho) * rho = Real.pi := by
      field_simp [ne_of_gt hrho]
    nlinarith
  exact ⟨Q, hQpos, hrange, hpi_div_Q_lt⟩

lemma exists_continuousSpike_finite_future_interior
    {theta0 : ℝ} (h0 : 0 < theta0) (hpi : theta0 < Real.pi)
    {R : ℕ} (hR : 1 ≤ R) :
    ∃ C_R : ℝ, 0 < C_R ∧ ∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        IsPowTwo n ∧
        0 < n ∧
        (∀ K : ℕ, R * n ≤ K →
          ∃ psi : AngleFun,
            VanishesNear theta0 (angleFunToRaw psi) ∧
            F theta0 n psi = 1 ∧
            (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
              F theta0 j psi = 0) ∧
            (∀ j : ℕ, R * n < j → j ≤ K →
              |F theta0 j psi| ≤ (1 / (1 / 2 : ℝ)) /
                Real.sqrt (R : ℝ)) ∧
            ‖psi‖ ≤ C_R / Real.log (n : ℝ)) := by
  have htheta0 : theta0 ∈ AngleI := ⟨le_of_lt h0, le_of_lt hpi⟩
  rcases exists_interior_kernel_lower_bound h0 hpi with
    ⟨c, hcpos, rho, hrhopos, hlocal⟩
  rcases exists_nat_good_interior_divisor
      (theta0 := theta0) (rho := rho) hpi hrhopos with
    ⟨Q, hQpos, hrange, hQrho⟩
  let C_R : ℝ :=
    1 / (((c / (2 * Real.pi)) / (R : ℝ)) * (1 / 2 : ℝ))
  have hC_R_pos : 0 < C_R := by
    dsimp [C_R]
    positivity
  refine ⟨C_R, hC_R_pos, ?_⟩
  intro N
  rcases exists_good_pow_two_with_continuousSpike_finite_future_interior_of_kernel_params
      (theta0 := theta0) (c := c) (rho := rho)
      (Q := Q) (R := R) (N := N)
      htheta0 hcpos hQpos hR hrange hQrho hlocal with
    ⟨n, hnN, hpow, hnpos, hK⟩
  refine ⟨n, hnN, hpow, hnpos, ?_⟩
  intro K hRK
  rcases hK K hRK with ⟨psi, hvanish, hhit, hearly, hfuture, hnorm⟩
  exact ⟨psi, hvanish, hhit, hearly, hfuture, by simpa [C_R] using hnorm⟩

lemma exists_good_pow_two_with_continuousSpike_finite_future_of_progression_kernel_lower
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R N : ℕ} {c : ℝ}
    (hR : 1 ≤ R) (hcpos : 0 < c)
    (hkernel : ∀ n : ℕ, N ≤ n → IsPowTwo n → 0 < n →
      ∀ s : ℕ, s ∈ oddUpTo R →
        c * ((n * s : ℕ) : ℝ) * Real.log (n : ℝ) ≤
          ∑ t ∈ Finset.range n,
            Real.sin (thetaNode (n * s) (s * t)) /
              |Real.cos theta0 -
                Real.cos (thetaNode (n * s) (s * t))|) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear theta0 (angleFunToRaw psi) ∧
          F theta0 n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F theta0 j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F theta0 j psi| ≤ (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ)) ∧
          ‖psi‖ ≤ (1 / (c * (1 / 2 : ℝ))) / Real.log (n : ℝ)) := by
  exact exists_good_pow_two_with_continuousSpike_finite_future_of_Vprim_lower
    htheta0 hR hcpos
    (fun n hnN hpow hnpos _hcos s hs =>
      Vprim_lower_of_progression_kernel_lower hpow hnpos
        (mem_oddUpTo_iff.mp hs).2.2.pos
        (hkernel n hnN hpow hnpos s hs))

lemma exists_good_pow_two_with_continuousSpike_finite_future_of_base_kernel_lower
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R N : ℕ} {c : ℝ}
    (hR : 1 ≤ R) (hcpos : 0 < c)
    (hkernel : ∀ n : ℕ, N ≤ n → IsPowTwo n → 0 < n →
      ∀ s : ℕ, s ∈ oddUpTo R →
        c * (n : ℝ) * Real.log (n : ℝ) ≤
          ∑ t ∈ Finset.range n,
            Real.sin (thetaNode (n * s) (s * t)) /
              |Real.cos theta0 -
                Real.cos (thetaNode (n * s) (s * t))|) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear theta0 (angleFunToRaw psi) ∧
          F theta0 n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F theta0 j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F theta0 j psi| ≤ (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ)) ∧
          ‖psi‖ ≤
            (1 / ((c / (R : ℝ)) * (1 / 2 : ℝ))) /
              Real.log (n : ℝ)) := by
  have hRpos : 0 < R := lt_of_lt_of_le Nat.zero_lt_one hR
  have hcRpos : 0 < c / (R : ℝ) := by
    positivity
  rcases exists_large_pow_two_good_cos_oddUpTo theta0 R (max N 2) with
    ⟨n, hnmax, hpow, hnpos, hkappa_le, hcos⟩
  have hnN : N ≤ n := (le_max_left N 2).trans hnmax
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hnmax
  have hlogpos : 0 < Real.log (n : ℝ) := log_nat_pos_of_two_le hn2
  refine ⟨n, hnN, hpow, hnpos, ?_⟩
  intro K hRK
  exact exists_continuousSpike_block_and_finite_future_of_good_rows_Vprim_lower
    (theta0 := theta0) htheta0
    (R := R) (n := n) (K := K)
    (c := c / (R : ℝ)) (kappa := (1 / 2 : ℝ))
    hnpos hR hRK hcRpos (by norm_num) hlogpos hkappa_le hcos
    (fun s hs =>
      Vprim_lower_of_progression_kernel_lower_base hpow hnpos hRpos
        (mem_oddUpTo_iff.mp hs).2.2.pos (mem_oddUpTo_iff.mp hs).2.1
        (le_of_lt hcpos) (le_of_lt hlogpos)
        (hkernel n hnN hpow hnpos s hs))

lemma exists_good_pow_two_with_continuousSpike_finite_future_zero_endpoint
    {R N : ℕ} (hR : 1 ≤ R) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear 0 (angleFunToRaw psi) ∧
          F 0 n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F 0 j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F 0 j psi| ≤ (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ)) ∧
          ‖psi‖ ≤
            (1 / (((1 / (2 * Real.pi)) / (R : ℝ)) *
              (1 / 2 : ℝ))) / Real.log (n : ℝ)) := by
  have htheta0 : (0 : ℝ) ∈ AngleI := ⟨le_rfl, Real.pi_pos.le⟩
  rcases exists_good_pow_two_with_continuousSpike_finite_future_of_base_kernel_lower
      (theta0 := 0) htheta0 (R := R) (N := max N 4)
      (c := 1 / (2 * Real.pi)) hR (by positivity)
      (fun n hnmax _hpow _hnpos s hs =>
        zero_endpoint_kernel_sum_range_ge_base_log
          ((le_max_right N 4).trans hnmax)
          (mem_oddUpTo_iff.mp hs).2.2.pos) with
    ⟨n, hnmax, hpow, hnpos, hK⟩
  exact ⟨n, (le_max_left N 4).trans hnmax, hpow, hnpos, hK⟩

lemma exists_good_pow_two_with_continuousSpike_finite_future_pi_endpoint
    {R N : ℕ} (hR : 1 ≤ R) :
    ∃ n : ℕ,
      N ≤ n ∧
      IsPowTwo n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear Real.pi (angleFunToRaw psi) ∧
          F Real.pi n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F Real.pi j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F Real.pi j psi| ≤ (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ)) ∧
          ‖psi‖ ≤
            (1 / (((1 / (2 * Real.pi)) / (R : ℝ)) *
              (1 / 2 : ℝ))) / Real.log (n : ℝ)) := by
  have htheta0 : Real.pi ∈ AngleI := ⟨Real.pi_pos.le, le_rfl⟩
  rcases exists_good_pow_two_with_continuousSpike_finite_future_of_base_kernel_lower
      (theta0 := Real.pi) htheta0 (R := R) (N := max N 4)
      (c := 1 / (2 * Real.pi)) hR (by positivity)
      (fun n hnmax _hpow _hnpos s hs =>
        pi_endpoint_kernel_sum_range_ge_base_log
          ((le_max_right N 4).trans hnmax)
          (mem_oddUpTo_iff.mp hs).2.2.pos) with
    ⟨n, hnmax, hpow, hnpos, hK⟩
  exact ⟨n, (le_max_left N 4).trans hnmax, hpow, hnpos, hK⟩

lemma exists_continuousSpike_finite_future_angle
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R : ℕ} (hR : 1 ≤ R) :
    ∃ C_R : ℝ, 0 < C_R ∧ ∀ N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        IsPowTwo n ∧
        0 < n ∧
        (∀ K : ℕ, R * n ≤ K →
          ∃ psi : AngleFun,
            VanishesNear theta0 (angleFunToRaw psi) ∧
            F theta0 n psi = 1 ∧
            (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
              F theta0 j psi = 0) ∧
            (∀ j : ℕ, R * n < j → j ≤ K →
              |F theta0 j psi| ≤ (1 / (1 / 2 : ℝ)) /
                Real.sqrt (R : ℝ)) ∧
            ‖psi‖ ≤ C_R / Real.log (n : ℝ)) := by
  by_cases hzero : theta0 = 0
  · let C_R : ℝ :=
      1 / ((((1 / (2 * Real.pi)) / (R : ℝ)) * (1 / 2 : ℝ)))
    have hC_R_pos : 0 < C_R := by
      dsimp [C_R]
      positivity
    refine ⟨C_R, hC_R_pos, ?_⟩
    intro N
    rcases exists_good_pow_two_with_continuousSpike_finite_future_zero_endpoint
        (R := R) (N := N) hR with
      ⟨n, hnN, hpow, hnpos, hK⟩
    refine ⟨n, hnN, hpow, hnpos, ?_⟩
    intro K hRK
    rcases hK K hRK with ⟨psi, hvanish, hhit, hearly, hfuture, hnorm⟩
    subst theta0
    exact ⟨psi, hvanish, hhit, hearly, hfuture,
      by simpa [C_R] using hnorm⟩
  · by_cases hpi_eq : theta0 = Real.pi
    · let C_R : ℝ :=
        1 / ((((1 / (2 * Real.pi)) / (R : ℝ)) * (1 / 2 : ℝ)))
      have hC_R_pos : 0 < C_R := by
        dsimp [C_R]
        positivity
      refine ⟨C_R, hC_R_pos, ?_⟩
      intro N
      rcases exists_good_pow_two_with_continuousSpike_finite_future_pi_endpoint
          (R := R) (N := N) hR with
        ⟨n, hnN, hpow, hnpos, hK⟩
      refine ⟨n, hnN, hpow, hnpos, ?_⟩
      intro K hRK
      rcases hK K hRK with ⟨psi, hvanish, hhit, hearly, hfuture, hnorm⟩
      subst theta0
      exact ⟨psi, hvanish, hhit, hearly, hfuture,
        by simpa [C_R] using hnorm⟩
    · have h0 : 0 < theta0 := lt_of_le_of_ne htheta0.1 (Ne.symm hzero)
      have hpi : theta0 < Real.pi := lt_of_le_of_ne htheta0.2 hpi_eq
      exact exists_continuousSpike_finite_future_interior h0 hpi hR

lemma exists_continuousSpike_finite_future_angle_with_delta
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {R : ℕ} (hR : 1 ≤ R) :
    ∃ C_R : ℝ, 0 < C_R ∧ ∀ N : ℕ, ∀ delta > 0,
      ∃ n : ℕ,
        N ≤ n ∧
        0 < n ∧
        (∀ K : ℕ, R * n ≤ K →
          ∃ psi : AngleFun,
            VanishesNear theta0 (angleFunToRaw psi) ∧
            F theta0 n psi = 1 ∧
            (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
              F theta0 j psi = 0) ∧
            (∀ j : ℕ, R * n < j → j ≤ K →
              |F theta0 j psi| ≤
                (1 / (1 / 2 : ℝ)) / Real.sqrt (R : ℝ) + delta) ∧
            ‖psi‖ ≤ C_R / Real.log (n : ℝ)) := by
  rcases exists_continuousSpike_finite_future_angle htheta0 hR with
    ⟨C_R, hC_R_pos, hspike⟩
  refine ⟨C_R, hC_R_pos, ?_⟩
  intro N delta hdelta
  rcases hspike N with ⟨n, hnN, _hpow, hnpos, hK⟩
  refine ⟨n, hnN, hnpos, ?_⟩
  intro K hRK
  rcases hK K hRK with ⟨psi, hvanish, hhit, hearly, hfuture, hnorm⟩
  refine ⟨psi, hvanish, hhit, hearly, ?_, hnorm⟩
  intro j hj hjK
  exact (hfuture j hj hjK).trans (by linarith [le_of_lt hdelta])

end Erdos1151Formalization

end
