import Erdos1151Formalization.ClusterSequence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Abstract block-spike interface for Erdős Problem 1151

The first major theorem should be proved from this interface before the concrete
primitive-row construction is formalised.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos1151Formalization

lemma exists_large_odd_eta_lt
    {eta : ℕ → ℝ} (heta : Tendsto eta Filter.atTop (nhds 0))
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) :
    ∃ R : ℕ, N ≤ R ∧ Odd R ∧ 3 ≤ R ∧ eta R < eps := by
  have hevent : ∀ᶠ R in Filter.atTop, eta R < eps :=
    (tendsto_order.mp heta).2 eps heps
  rcases Filter.eventually_atTop.mp hevent with ⟨M, hM⟩
  let R := 2 * max M N + 3
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · omega
  · use max M N + 1
    omega
  · omega
  · exact hM R (by omega)

/-- A concrete tail error rate for the block-spike interface. -/
def etaSqrt (C : ℝ) (R : ℕ) : ℝ :=
  C / Real.sqrt (R : ℝ)

lemma etaSqrt_nonneg {C : ℝ} (hC : 0 ≤ C) (R : ℕ) :
    0 ≤ etaSqrt C R := by
  exact div_nonneg hC (Real.sqrt_nonneg _)

lemma etaSqrt_tendsto_zero (C : ℝ) :
    Tendsto (etaSqrt C) Filter.atTop (nhds 0) := by
  have hsqrt :
      Tendsto (fun R : ℕ => Real.sqrt (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa [etaSqrt] using tendsto_const_nhds.div_atTop hsqrt

lemma tendsto_const_div_log_nat_atTop_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C / Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
  exact Filter.Tendsto.const_div_atTop
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) C

lemma exists_nat_forall_ge_const_div_log_lt
    (C : ℝ) {eps : ℝ} (heps : 0 < eps) (N : ℕ) :
    ∃ M : ℕ, N ≤ M ∧ ∀ n : ℕ, M ≤ n → C / Real.log (n : ℝ) < eps := by
  have hlim := tendsto_const_div_log_nat_atTop_zero C
  have hevent :
      ∀ᶠ (n : ℕ) in (Filter.atTop : Filter ℕ), C / Real.log (n : ℝ) < eps :=
    (tendsto_order.mp hlim).2 eps heps
  rcases Filter.eventually_atTop.mp hevent with ⟨M, hM⟩
  exact ⟨max N M, le_max_left N M, fun n hn => hM n ((le_max_right N M).trans hn)⟩

lemma tsum_eq_sum_range_succ_of_eq_zero
    {f : ℕ → ℝ} {m : ℕ}
    (hzero : ∀ i : ℕ, m < i → f i = 0) :
    (∑' i : ℕ, f i) = (Finset.range (m + 1)).sum f := by
  rw [tsum_eq_sum (s := Finset.range (m + 1))]
  intro i hi
  exact hzero i (by
    rw [Finset.mem_range] at hi
    omega)

lemma tsum_eq_sum_range_add_of_tail_zero
    {f : ℕ → ℝ} {m : ℕ}
    (hzero : ∀ i : ℕ, m < i → f i = 0) :
    (∑' i : ℕ, f i) = (Finset.range m).sum f + f m := by
  rw [tsum_eq_sum_range_succ_of_eq_zero hzero, Finset.sum_range_succ]

lemma selected_row_algebra
    {a c : ℝ} {b row : ℕ → ℝ} {m : ℕ}
    (hb : b m = a - c - (Finset.range m).sum (fun i => b i * row i))
    (hrow : row m = 1)
    (htail : ∀ i : ℕ, m < i → b i * row i = 0) :
    c + ∑' i : ℕ, b i * row i = a := by
  rw [tsum_eq_sum_range_add_of_tail_zero htail, hrow, mul_one, hb]
  ring

lemma summable_angleFun_of_norm_le_geometric {phis : ℕ → AngleFun}
    (hphis : ∀ i : ℕ, ‖phis i‖ ≤ ((1 / 2 : ℝ) ^ i)) :
    Summable phis :=
  Summable.of_norm_bounded summable_geometric_two hphis

/-- The coefficient that should be assigned to a new selected row after a
finite prefix with already assigned coefficients. -/
def nextCoeff
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun) (m n : ℕ) : ℝ :=
  a m - c - (Finset.range m).sum
    (fun i => coeff i * F theta0 n (psiSeq i))

lemma abs_nextCoeff_le_of_prev_sum_lt
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun) (m n : ℕ)
    {B eps : ℝ}
    (hbase : |a m - c| ≤ B)
    (hprev :
      |(Finset.range m).sum
        (fun i => coeff i * F theta0 n (psiSeq i))| < eps) :
    |nextCoeff theta0 a c coeff psiSeq m n| ≤ B + eps := by
  unfold nextCoeff
  set prev := (Finset.range m).sum
    (fun i => coeff i * F theta0 n (psiSeq i))
  calc
    |a m - c - prev| ≤ |a m - c| + |prev| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (a m - c) (-prev)
    _ ≤ B + eps := add_le_add hbase (le_of_lt hprev)

lemma abs_nextCoeff_le_three_of_prev_sum_lt_one
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun) (m n : ℕ)
    (hbase : |a m - c| ≤ 2)
    (hprev :
      |(Finset.range m).sum
        (fun i => coeff i * F theta0 n (psiSeq i))| < 1) :
    |nextCoeff theta0 a c coeff psiSeq m n| ≤ 3 := by
  have h :=
    abs_nextCoeff_le_of_prev_sum_lt
      (theta0 := theta0) (a := a) (c := c)
      (coeff := coeff) (psiSeq := psiSeq) (m := m) (n := n)
      (B := 2) (eps := 1) hbase hprev
  norm_num at h
  exact h

/-- Recursive coefficients cancelling the previously chosen spikes at the selected rows. -/
def diagonalCoeff
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (nSeq : ℕ → ℕ) (psiSeq : ℕ → AngleFun) : ℕ → ℝ
  | m =>
      a m - c -
        (Finset.range m).attach.sum
          (fun i => diagonalCoeff theta0 a c nSeq psiSeq i *
            F theta0 (nSeq m) (psiSeq i))
termination_by m => m
decreasing_by
  exact Finset.mem_range.mp i.2

lemma diagonalCoeff_eq
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (nSeq : ℕ → ℕ) (psiSeq : ℕ → AngleFun) (m : ℕ) :
    diagonalCoeff theta0 a c nSeq psiSeq m =
      a m - c -
        (Finset.range m).sum
          (fun i => diagonalCoeff theta0 a c nSeq psiSeq i *
            F theta0 (nSeq m) (psiSeq i)) := by
  rw [diagonalCoeff]
  have hsum :=
    Finset.sum_attach (s := Finset.range m)
      (f := fun i : ℕ =>
        diagonalCoeff theta0 a c nSeq psiSeq i * F theta0 (nSeq m) (psiSeq i))
  rw [hsum]

lemma diagonalCoeff_congr_of_eq_on_lt
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    {nSeq₁ nSeq₂ : ℕ → ℕ} {psiSeq₁ psiSeq₂ : ℕ → AngleFun}
    {m : ℕ}
    (hn : ∀ i : ℕ, i < m → nSeq₁ i = nSeq₂ i)
    (hpsi : ∀ i : ℕ, i < m → psiSeq₁ i = psiSeq₂ i) :
    ∀ i : ℕ, i < m →
      diagonalCoeff theta0 a c nSeq₁ psiSeq₁ i =
        diagonalCoeff theta0 a c nSeq₂ psiSeq₂ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      rw [diagonalCoeff_eq, diagonalCoeff_eq]
      apply congrArg
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j < i := Finset.mem_range.mp hj
      have hjm : j < m := hji.trans hi
      rw [ih j hji hjm, hn i hi, hpsi j hjm]

lemma selected_row_diagonalCoeff_algebra
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (nSeq : ℕ → ℕ) (psiSeq : ℕ → AngleFun) (m : ℕ)
    (hrow : F theta0 (nSeq m) (psiSeq m) = 1)
    (htail : ∀ i : ℕ, m < i →
      diagonalCoeff theta0 a c nSeq psiSeq i * F theta0 (nSeq m) (psiSeq i) = 0) :
    c + ∑' i : ℕ,
      diagonalCoeff theta0 a c nSeq psiSeq i * F theta0 (nSeq m) (psiSeq i) =
        a m := by
  exact selected_row_algebra
    (hb := diagonalCoeff_eq theta0 a c nSeq psiSeq m)
    (hrow := hrow)
    (htail := htail)

lemma abs_diagonalCoeff_le_of_prev_sum_lt
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (nSeq : ℕ → ℕ) (psiSeq : ℕ → AngleFun) (m : ℕ)
    {B eps : ℝ}
    (hbase : |a m - c| ≤ B)
    (hprev :
      |(Finset.range m).sum
        (fun i => diagonalCoeff theta0 a c nSeq psiSeq i *
          F theta0 (nSeq m) (psiSeq i))| < eps) :
    |diagonalCoeff theta0 a c nSeq psiSeq m| ≤ B + eps := by
  rw [diagonalCoeff_eq]
  set prev :=
    (Finset.range m).sum
      (fun i => diagonalCoeff theta0 a c nSeq psiSeq i *
        F theta0 (nSeq m) (psiSeq i))
  calc
    |a m - c - prev| ≤ |a m - c| + |prev| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (a m - c) (-prev)
    _ ≤ B + eps := add_le_add hbase (le_of_lt hprev)

lemma abs_diagonalCoeff_le_three_of_prev_sum_lt_one
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    (nSeq : ℕ → ℕ) (psiSeq : ℕ → AngleFun) (m : ℕ)
    (hbase : |a m - c| ≤ 2)
    (hprev :
      |(Finset.range m).sum
        (fun i => diagonalCoeff theta0 a c nSeq psiSeq i *
          F theta0 (nSeq m) (psiSeq i))| < 1) :
    |diagonalCoeff theta0 a c nSeq psiSeq m| ≤ 3 := by
  have h :=
    abs_diagonalCoeff_le_of_prev_sum_lt
      (theta0 := theta0) (a := a) (c := c)
      (nSeq := nSeq) (psiSeq := psiSeq) (m := m)
      (B := 2) (eps := 1) hbase hprev
  norm_num at h
  exact h

/-- The exact spike-row data needed for the selected-row algebra. -/
structure DiagonalSpikeData (theta0 : ℝ) where
  RSeq : ℕ → ℕ
  nSeq : ℕ → ℕ
  psiSeq : ℕ → AngleFun
  R_ge_one : ∀ m, 1 ≤ RSeq m
  n_pos : ∀ m, 0 < nSeq m
  n_strict : StrictMono nSeq
  vanishes : ∀ m, VanishesNear theta0 (angleFunToRaw (psiSeq m))
  hit : ∀ m, F theta0 (nSeq m) (psiSeq m) = 1
  early_zero :
    ∀ m j : ℕ, 1 ≤ j → j ≤ RSeq m * nSeq m → j ≠ nSeq m →
      F theta0 j (psiSeq m) = 0

lemma DiagonalSpikeData.future_selected_zero
    {theta0 : ℝ} (D : DiagonalSpikeData theta0) {m i : ℕ} (hmi : m < i) :
    F theta0 (D.nSeq m) (D.psiSeq i) = 0 := by
  have hnlt : D.nSeq m < D.nSeq i := D.n_strict hmi
  have hjpos : 1 ≤ D.nSeq m := D.n_pos m
  have hRpos : 0 < D.RSeq i := Nat.lt_of_lt_of_le Nat.zero_lt_one (D.R_ge_one i)
  have hle_mul : D.nSeq i ≤ D.RSeq i * D.nSeq i :=
    Nat.le_mul_of_pos_left (D.nSeq i) hRpos
  have hle : D.nSeq m ≤ D.RSeq i * D.nSeq i := (le_of_lt hnlt).trans hle_mul
  have hne : D.nSeq m ≠ D.nSeq i := ne_of_lt hnlt
  exact D.early_zero i (D.nSeq m) hjpos hle hne

lemma DiagonalSpikeData.future_selected_tail_zero
    {theta0 : ℝ} (D : DiagonalSpikeData theta0)
    (a : ℕ → ℝ) (c : ℝ) {m : ℕ} :
    ∀ i : ℕ, m < i →
      diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
        F theta0 (D.nSeq m) (D.psiSeq i) = 0 := by
  intro i hmi
  rw [D.future_selected_zero hmi, mul_zero]

lemma DiagonalSpikeData.selected_raw_tsum
    {theta0 : ℝ} (D : DiagonalSpikeData theta0)
    (a : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    c + ∑' i : ℕ,
      diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
        F theta0 (D.nSeq m) (D.psiSeq i) =
      a m := by
  exact selected_row_diagonalCoeff_algebra theta0 a c D.nSeq D.psiSeq m
    (D.hit m) (D.future_selected_tail_zero a c)

/-- Diagonal spike data with the quantitative estimates needed for convergence
of the diagonal series and for rows outside the selected subsequence. -/
structure ControlledDiagonalSpikeData
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ)
    extends DiagonalSpikeData theta0 where
  coeff_bound :
    ∀ m : ℕ, |diagonalCoeff theta0 a c nSeq psiSeq m| ≤ 3
  norm_bound :
    ∀ m : ℕ, ‖psiSeq m‖ ≤ ((1 / 2 : ℝ) ^ m) / 4
  future_bound :
    ∀ m j : ℕ, RSeq m * nSeq m < j →
      |F theta0 j (psiSeq m)| ≤ ((1 / 2 : ℝ) ^ m) / 4

lemma ControlledDiagonalSpikeData.term_norm_le_geometric
    {theta0 : ℝ} {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c) (m : ℕ) :
    ‖diagonalCoeff theta0 a c D.nSeq D.psiSeq m • D.psiSeq m‖ ≤
      ((1 / 2 : ℝ) ^ m) := by
  rw [norm_smul, Real.norm_eq_abs]
  have hpow_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ m) := by positivity
  have hmul :
      |diagonalCoeff theta0 a c D.nSeq D.psiSeq m| * ‖D.psiSeq m‖ ≤
        3 * (((1 / 2 : ℝ) ^ m) / 4) := by
    exact mul_le_mul (D.coeff_bound m) (D.norm_bound m) (norm_nonneg _) (by norm_num)
  have hscale : 3 * (((1 / 2 : ℝ) ^ m) / 4) ≤ ((1 / 2 : ℝ) ^ m) := by
    nlinarith
  exact hmul.trans hscale

lemma ControlledDiagonalSpikeData.summable_terms
    {theta0 : ℝ} {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c) :
    Summable fun m : ℕ =>
      diagonalCoeff theta0 a c D.nSeq D.psiSeq m • D.psiSeq m :=
  summable_angleFun_of_norm_le_geometric D.term_norm_le_geometric

lemma ControlledDiagonalSpikeData.future_term_abs_le_geometric
    {theta0 : ℝ} {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c)
    {m j : ℕ} (hfuture : D.RSeq m * D.nSeq m < j) :
    |diagonalCoeff theta0 a c D.nSeq D.psiSeq m *
      F theta0 j (D.psiSeq m)| ≤ ((1 / 2 : ℝ) ^ m) := by
  rw [abs_mul]
  have hmul :
      |diagonalCoeff theta0 a c D.nSeq D.psiSeq m| *
          |F theta0 j (D.psiSeq m)| ≤
        3 * (((1 / 2 : ℝ) ^ m) / 4) := by
    exact mul_le_mul (D.coeff_bound m) (D.future_bound m j hfuture)
      (abs_nonneg _) (by norm_num)
  have hscale : 3 * (((1 / 2 : ℝ) ^ m) / 4) ≤ ((1 / 2 : ℝ) ^ m) := by
    have hpow_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ m) := by positivity
    nlinarith
  exact hmul.trans hscale

lemma ControlledDiagonalSpikeData.off_range_term_abs_le_geometric
    {theta0 : ℝ} {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c)
    {m j : ℕ} (hjpos : 1 ≤ j) (hjnot : j ∉ Set.range D.nSeq) :
    |diagonalCoeff theta0 a c D.nSeq D.psiSeq m *
      F theta0 j (D.psiSeq m)| ≤ ((1 / 2 : ℝ) ^ m) := by
  by_cases hfuture : D.RSeq m * D.nSeq m < j
  · exact D.future_term_abs_le_geometric hfuture
  · have hle : j ≤ D.RSeq m * D.nSeq m := Nat.le_of_not_lt hfuture
    have hne : j ≠ D.nSeq m := by
      intro h
      exact hjnot ⟨m, h.symm⟩
    rw [D.early_zero m j hjpos hle hne, mul_zero, abs_zero]
    positivity

/-- The diagonal angle function attached to selected spike-row data. -/
def DiagonalSpikeData.diagonalPhi
    {theta0 : ℝ} (D : DiagonalSpikeData theta0) (a : ℕ → ℝ) (c : ℝ) : AngleFun :=
  ContinuousMap.const AngleI c +
    ∑' i : ℕ, diagonalCoeff theta0 a c D.nSeq D.psiSeq i • D.psiSeq i

/-- The diagonal angle function attached to controlled selected spike-row data. -/
def ControlledDiagonalSpikeData.diagonalPhi
    {theta0 : ℝ} {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c) : AngleFun :=
  D.toDiagonalSpikeData.diagonalPhi a c

/-- Abstract block-spike data sufficient for the diagonal cluster-set theorem. -/
structure AbstractBlockSpikeHypothesis
    (theta0 : ℝ) (_htheta0 : theta0 ∈ AngleI) where
  const_eval : ∀ c : ℝ, ∀ n : ℕ, 0 < n →
    F theta0 n (ContinuousMap.const AngleI c) = c
  off_point_decay : ∀ psi : AngleFun,
    VanishesNear theta0 (angleFunToRaw psi) →
      Tendsto (fun n : ℕ => F theta0 n psi) Filter.atTop (nhds 0)
  eta : ℕ → ℝ
  eta_nonneg : ∀ R, 0 ≤ eta R
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  exists_spike :
    ∀ R : ℕ, Odd R → 3 ≤ R →
      ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ, ∃ psi : AngleFun,
        N ≤ n ∧
        0 < n ∧
        VanishesNear theta0 (angleFunToRaw psi) ∧
        F theta0 n psi = 1 ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F theta0 j psi = 0) ∧
        (∀ j : ℕ, R * n < j → |F theta0 j psi| ≤ eta R + delta) ∧
        ‖psi‖ ≤ C_R / Real.log (n : ℝ)

/-- Variant of the block-spike interface where the square-root future bound is
only required up to an arbitrary finite cutoff.  This matches the concrete
continuous-spike construction, where the interpolation identities are exact on
any prescribed finite set of rows. -/
structure AbstractFiniteBlockSpikeHypothesis
    (theta0 : ℝ) (_htheta0 : theta0 ∈ AngleI) where
  const_eval : ∀ c : ℝ, ∀ n : ℕ, 0 < n →
    F theta0 n (ContinuousMap.const AngleI c) = c
  off_point_decay : ∀ psi : AngleFun,
    VanishesNear theta0 (angleFunToRaw psi) →
      Tendsto (fun n : ℕ => F theta0 n psi) Filter.atTop (nhds 0)
  eta : ℕ → ℝ
  eta_nonneg : ∀ R, 0 ≤ eta R
  eta_tendsto_zero : Tendsto eta atTop (nhds 0)
  exists_finite_spike :
    ∀ R : ℕ, Odd R → 3 ≤ R →
      ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ,
        N ≤ n ∧
        0 < n ∧
        (∀ K : ℕ, R * n ≤ K →
          ∃ psi : AngleFun,
            VanishesNear theta0 (angleFunToRaw psi) ∧
            F theta0 n psi = 1 ∧
            (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
              F theta0 j psi = 0) ∧
            (∀ j : ℕ, R * n < j → j ≤ K →
              |F theta0 j psi| ≤ eta R + delta) ∧
            ‖psi‖ ≤ C_R / Real.log (n : ℝ))

lemma AbstractFiniteBlockSpikeHypothesis.exists_finite_spike_with_eta_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractFiniteBlockSpikeHypothesis theta0 htheta0)
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (Rmin Nrow : ℕ) :
    ∃ R : ℕ, ∃ C_R : ℝ, ∃ n : ℕ,
      Rmin ≤ R ∧
      Odd R ∧
      3 ≤ R ∧
      H.eta R < eps ∧
      0 < C_R ∧
      Nrow ≤ n ∧
      0 < n ∧
      (∀ K : ℕ, R * n ≤ K →
        ∃ psi : AngleFun,
          VanishesNear theta0 (angleFunToRaw psi) ∧
          F theta0 n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F theta0 j psi = 0) ∧
          (∀ j : ℕ, R * n < j → j ≤ K →
            |F theta0 j psi| ≤ H.eta R + delta) ∧
          ‖psi‖ ≤ C_R / Real.log (n : ℝ)) := by
  obtain ⟨R, hRmin, hRodd, hR3, hReta⟩ :=
    exists_large_odd_eta_lt H.eta_tendsto_zero heps Rmin
  obtain ⟨C_R, hC_R_pos, hspikes⟩ := H.exists_finite_spike R hRodd hR3
  obtain ⟨n, hnrow, hnpos, hK⟩ := hspikes Nrow delta hdelta
  exact ⟨R, C_R, n, hRmin, hRodd, hR3, hReta, hC_R_pos, hnrow, hnpos, hK⟩

lemma AbstractBlockSpikeHypothesis.F_diagonalPhi_selected
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (D : DiagonalSpikeData theta0) (a : ℕ → ℝ) (c : ℝ)
    (hsum : Summable fun i : ℕ =>
      diagonalCoeff theta0 a c D.nSeq D.psiSeq i • D.psiSeq i)
    (m : ℕ) :
    F theta0 (D.nSeq m) (D.diagonalPhi a c) = a m := by
  rw [DiagonalSpikeData.diagonalPhi]
  rw [F_const_add_tsum_smul (H.const_eval c (D.nSeq m) (D.n_pos m)) hsum]
  exact D.selected_raw_tsum a c m

lemma AbstractBlockSpikeHypothesis.F_controlledDiagonalPhi_selected
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c) (m : ℕ) :
    F theta0 (D.nSeq m) D.diagonalPhi = a m :=
  H.F_diagonalPhi_selected D.toDiagonalSpikeData a c D.summable_terms m

lemma AbstractBlockSpikeHypothesis.tendsto_finset_spike_rows_zero
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun)
    (hvanish : ∀ i : ℕ, VanishesNear theta0 (angleFunToRaw (psiSeq i)))
    (s : Finset ℕ) :
    Tendsto (fun n : ℕ => s.sum fun i => coeff i * F theta0 n (psiSeq i))
      Filter.atTop (nhds 0) := by
  have hsum := tendsto_finset_sum s
    (f := fun i n => coeff i * F theta0 n (psiSeq i))
    (a := fun _ : ℕ => 0)
    (x := Filter.atTop)
    (fun i _hi => by
      have hi := H.off_point_decay (psiSeq i) (hvanish i)
      simpa using hi.const_mul (coeff i))
  simpa using hsum

lemma AbstractBlockSpikeHypothesis.tendsto_finset_spike_rows_zero_of_mem
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun)
    (s : Finset ℕ)
    (hvanish : ∀ i : ℕ, i ∈ s → VanishesNear theta0 (angleFunToRaw (psiSeq i))) :
    Tendsto (fun n : ℕ => s.sum fun i => coeff i * F theta0 n (psiSeq i))
      Filter.atTop (nhds 0) := by
  have hsum := tendsto_finset_sum s
    (f := fun i n => coeff i * F theta0 n (psiSeq i))
    (a := fun _ : ℕ => 0)
    (x := Filter.atTop)
    (fun i hi => by
      have hdecay := H.off_point_decay (psiSeq i) (hvanish i hi)
      simpa using hdecay.const_mul (coeff i))
  simpa using hsum

lemma AbstractBlockSpikeHypothesis.tendsto_finset_diagonal_rows_zero
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (D : DiagonalSpikeData theta0) (coeff : ℕ → ℝ) (s : Finset ℕ) :
    Tendsto (fun n : ℕ => s.sum fun i => coeff i * F theta0 n (D.psiSeq i))
      Filter.atTop (nhds 0) :=
  H.tendsto_finset_spike_rows_zero coeff D.psiSeq D.vanishes s

lemma AbstractBlockSpikeHypothesis.exists_finset_spike_rows_abs_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun)
    (hvanish : ∀ i : ℕ, VanishesNear theta0 (angleFunToRaw (psiSeq i)))
    (s : Finset ℕ) {eps : ℝ} (heps : 0 < eps) (N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        |s.sum fun i => coeff i * F theta0 n (psiSeq i)| < eps := by
  have hlim := H.tendsto_finset_spike_rows_zero coeff psiSeq hvanish s
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        |s.sum fun i => coeff i * F theta0 n (psiSeq i)| < eps := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim eps heps)
  rcases Filter.eventually_atTop.mp hevent with ⟨N1, hN1⟩
  exact ⟨max N0 N1, le_max_left N0 N1,
    fun n hn => hN1 n ((le_max_right N0 N1).trans hn)⟩

lemma AbstractBlockSpikeHypothesis.exists_finset_spike_rows_abs_lt_of_mem
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun)
    (s : Finset ℕ)
    (hvanish : ∀ i : ℕ, i ∈ s → VanishesNear theta0 (angleFunToRaw (psiSeq i)))
    {eps : ℝ} (heps : 0 < eps) (N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        |s.sum fun i => coeff i * F theta0 n (psiSeq i)| < eps := by
  have hlim := H.tendsto_finset_spike_rows_zero_of_mem coeff psiSeq s hvanish
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        |s.sum fun i => coeff i * F theta0 n (psiSeq i)| < eps := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim eps heps)
  rcases Filter.eventually_atTop.mp hevent with ⟨N1, hN1⟩
  exact ⟨max N0 N1, le_max_left N0 N1,
    fun n hn => hN1 n ((le_max_right N0 N1).trans hn)⟩

lemma AbstractBlockSpikeHypothesis.exists_diagonal_prev_sum_abs_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (D : DiagonalSpikeData theta0) (a : ℕ → ℝ) (c : ℝ)
    {eps : ℝ} (heps : 0 < eps) (m N0 : ℕ) :
    ∃ N : ℕ, N0 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        |(Finset.range m).sum
          (fun i => diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
            F theta0 n (D.psiSeq i))| < eps := by
  exact H.exists_finset_spike_rows_abs_lt
    (fun i => diagonalCoeff theta0 a c D.nSeq D.psiSeq i)
    D.psiSeq D.vanishes (Finset.range m) heps N0

lemma AbstractBlockSpikeHypothesis.clusterSet_diagonalPhi_of_complement_tendsto
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (D : DiagonalSpikeData theta0) (a : ℕ → ℝ) (c : ℝ)
    {A : Set ℝ}
    (hsum : Summable fun i : ℕ =>
      diagonalCoeff theta0 a c D.nSeq D.psiSeq i • D.psiSeq i)
    (ha_cluster : clusterSet a = A)
    (hcA : c ∈ A)
    (hcomp : Tendsto (fun n : ℕ => F theta0 n (D.diagonalPhi a c))
      (Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ) (nhds c)) :
    clusterSet (fun n : ℕ => F theta0 n (D.diagonalPhi a c)) = A := by
  apply clusterSet_of_selected_rows_and_complement_tendsto D.n_strict ?_ ha_cluster hcA hcomp
  intro m
  exact H.F_diagonalPhi_selected D a c hsum m

lemma AbstractBlockSpikeHypothesis.clusterSet_diagonalPhi_succ_of_complement_tendsto
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (D : DiagonalSpikeData theta0) (a : ℕ → ℝ) (c : ℝ)
    {A : Set ℝ}
    (hsum : Summable fun i : ℕ =>
      diagonalCoeff theta0 a c D.nSeq D.psiSeq i • D.psiSeq i)
    (ha_cluster : clusterSet a = A)
    (hcA : c ∈ A)
    (hcomp : Tendsto (fun n : ℕ => F theta0 n (D.diagonalPhi a c))
      (Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ) (nhds c)) :
    clusterSet (fun m : ℕ => F theta0 (m.succ) (D.diagonalPhi a c)) = A := by
  rw [clusterSet_succ_eq (fun n : ℕ => F theta0 n (D.diagonalPhi a c))]
  exact H.clusterSet_diagonalPhi_of_complement_tendsto D a c hsum ha_cluster hcA hcomp

lemma AbstractBlockSpikeHypothesis.clusterSet_controlledDiagonalPhi_succ_of_complement_tendsto
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c)
    {A : Set ℝ}
    (ha_cluster : clusterSet a = A)
    (hcA : c ∈ A)
    (hcomp : Tendsto (fun n : ℕ => F theta0 n D.diagonalPhi)
      (Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ) (nhds c)) :
    clusterSet (fun m : ℕ => F theta0 (m.succ) D.diagonalPhi) = A := by
  exact H.clusterSet_diagonalPhi_succ_of_complement_tendsto
    D.toDiagonalSpikeData a c D.summable_terms ha_cluster hcA hcomp

lemma AbstractBlockSpikeHypothesis.controlledDiagonal_scalar_tsum_complement_tendsto_zero
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c) :
    Tendsto
      (fun n : ℕ =>
        ∑' i : ℕ,
          diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
            F theta0 n (D.psiSeq i))
      (Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ)
      (nhds 0) := by
  let L : Filter ℕ := Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ
  have hsum_bound : Summable fun i : ℕ => ((1 / 2 : ℝ) ^ i) :=
    summable_geometric_two
  have hterm :
      ∀ i : ℕ,
        Tendsto
          (fun n : ℕ =>
            diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
              F theta0 n (D.psiSeq i))
          L (nhds 0) := by
    intro i
    have hi :=
      H.off_point_decay (D.psiSeq i) (D.vanishes i)
    simpa [L, mul_zero] using
      (hi.const_mul (diagonalCoeff theta0 a c D.nSeq D.psiSeq i)).mono_left inf_le_left
  have hbound :
      ∀ᶠ n : ℕ in L, ∀ i : ℕ,
        ‖diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
          F theta0 n (D.psiSeq i)‖ ≤ ((1 / 2 : ℝ) ^ i) := by
    have hpos_atTop : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    have hpos : ∀ᶠ n : ℕ in L, 1 ≤ n :=
      hpos_atTop.filter_mono inf_le_left
    have hnot : ∀ᶠ n : ℕ in L, n ∉ Set.range D.nSeq :=
      Filter.le_principal_iff.mp inf_le_right
    filter_upwards [hpos, hnot] with n hnpos hnnot i
    simpa [Real.norm_eq_abs] using
      D.off_range_term_abs_le_geometric (m := i) (j := n) hnpos hnnot
  have htsum :=
    tendsto_tsum_of_dominated_convergence
      (𝓕 := L)
      (f := fun n i =>
        diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
          F theta0 n (D.psiSeq i))
      (g := fun _ : ℕ => (0 : ℝ))
      (bound := fun i : ℕ => ((1 / 2 : ℝ) ^ i))
      hsum_bound hterm hbound
  simpa using htsum

lemma AbstractBlockSpikeHypothesis.controlledDiagonalPhi_complement_tendsto
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c) :
      Tendsto (fun n : ℕ => F theta0 n D.diagonalPhi)
      (Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ) (nhds c) := by
  let L : Filter ℕ := Filter.atTop ⊓ Filter.principal (Set.range D.nSeq)ᶜ
  have hseries := H.controlledDiagonal_scalar_tsum_complement_tendsto_zero D
  have hrewrite :
      ∀ᶠ n : ℕ in L,
        F theta0 n D.diagonalPhi =
          c + ∑' i : ℕ,
            diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
              F theta0 n (D.psiSeq i) := by
    have hpos_atTop : ∀ᶠ n : ℕ in Filter.atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
    have hpos : ∀ᶠ n : ℕ in L, 0 < n :=
      hpos_atTop.filter_mono inf_le_left
    filter_upwards [hpos] with n hnpos
    rw [ControlledDiagonalSpikeData.diagonalPhi, DiagonalSpikeData.diagonalPhi]
    rw [F_const_add_tsum_smul (H.const_eval c n hnpos) D.summable_terms]
  have htarget :
      Tendsto
        (fun n : ℕ =>
          c + ∑' i : ℕ,
            diagonalCoeff theta0 a c D.nSeq D.psiSeq i *
              F theta0 n (D.psiSeq i))
        L (nhds c) := by
    simpa using (tendsto_const_nhds.add hseries)
  exact htarget.congr' (hrewrite.mono fun _ h => h.symm)

lemma AbstractBlockSpikeHypothesis.clusterSet_controlledDiagonalPhi_succ
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (D : ControlledDiagonalSpikeData theta0 a c)
    {A : Set ℝ}
    (ha_cluster : clusterSet a = A)
    (hcA : c ∈ A) :
    clusterSet (fun m : ℕ => F theta0 (m.succ) D.diagonalPhi) = A :=
  H.clusterSet_controlledDiagonalPhi_succ_of_complement_tendsto D
    ha_cluster hcA (H.controlledDiagonalPhi_complement_tendsto D)

lemma AbstractBlockSpikeHypothesis.exists_spike_with_eta_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (Rmin Nrow : ℕ) :
    ∃ R : ℕ, ∃ C_R : ℝ, ∃ n : ℕ, ∃ psi : AngleFun,
      Rmin ≤ R ∧
      Odd R ∧
      3 ≤ R ∧
      H.eta R < eps ∧
      0 < C_R ∧
      Nrow ≤ n ∧
      0 < n ∧
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F theta0 j psi = 0) ∧
      (∀ j : ℕ, R * n < j → |F theta0 j psi| ≤ H.eta R + delta) ∧
      ‖psi‖ ≤ C_R / Real.log (n : ℝ) := by
  obtain ⟨R, hRmin, hRodd, hR3, hReta⟩ :=
    exists_large_odd_eta_lt H.eta_tendsto_zero heps Rmin
  obtain ⟨C_R, hC_R_pos, hspikes⟩ := H.exists_spike R hRodd hR3
  obtain ⟨n, psi, hnrow, hnpos, hvanish, hhit, hearly, hfuture, hnorm⟩ :=
    hspikes Nrow delta hdelta
  exact ⟨R, C_R, n, psi, hRmin, hRodd, hR3, hReta, hC_R_pos, hnrow, hnpos,
    hvanish, hhit, hearly, hfuture, hnorm⟩

lemma AbstractBlockSpikeHypothesis.exists_spike_with_eta_lt_norm_le
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {eps delta normTarget : ℝ}
    (heps : 0 < eps) (hdelta : 0 < delta) (hnormTarget : 0 < normTarget)
    (Rmin Nrow : ℕ) :
    ∃ R : ℕ, ∃ C_R : ℝ, ∃ n : ℕ, ∃ psi : AngleFun,
      Rmin ≤ R ∧
      Odd R ∧
      3 ≤ R ∧
      H.eta R < eps ∧
      0 < C_R ∧
      Nrow ≤ n ∧
      0 < n ∧
      VanishesNear theta0 (angleFunToRaw psi) ∧
      F theta0 n psi = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F theta0 j psi = 0) ∧
      (∀ j : ℕ, R * n < j → |F theta0 j psi| ≤ H.eta R + delta) ∧
      ‖psi‖ ≤ C_R / Real.log (n : ℝ) ∧
      ‖psi‖ ≤ normTarget := by
  obtain ⟨R, hRmin, hRodd, hR3, hReta⟩ :=
    exists_large_odd_eta_lt H.eta_tendsto_zero heps Rmin
  obtain ⟨C_R, hC_R_pos, hspikes⟩ := H.exists_spike R hRodd hR3
  obtain ⟨M, hNrowM, hM⟩ :=
    exists_nat_forall_ge_const_div_log_lt C_R hnormTarget Nrow
  obtain ⟨n, psi, hnM, hnpos, hvanish, hhit, hearly, hfuture, hnorm⟩ :=
    hspikes M delta hdelta
  have hnrow : Nrow ≤ n := hNrowM.trans hnM
  have hnorm_target : ‖psi‖ ≤ normTarget :=
    hnorm.trans (le_of_lt (hM n hnM))
  exact ⟨R, C_R, n, psi, hRmin, hRodd, hR3, hReta, hC_R_pos, hnrow, hnpos,
    hvanish, hhit, hearly, hfuture, hnorm, hnorm_target⟩

structure SpikePackage (theta0 : ℝ) where
  R : ℕ
  n : ℕ
  psi : AngleFun

structure SpikeChoice (theta0 : ℝ) (N : ℕ) where
  R : ℕ
  n : ℕ
  psi : AngleFun
  R_ge_one : 1 ≤ R
  n_ge : N ≤ n
  n_pos : 0 < n
  vanishes : VanishesNear theta0 (angleFunToRaw psi)
  hit : F theta0 n psi = 1
  early_zero :
    ∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F theta0 j psi = 0

structure QuantSpikeChoice
    (theta0 : ℝ) (N : ℕ) (futureTarget normTarget : ℝ) where
  R : ℕ
  n : ℕ
  psi : AngleFun
  R_ge_one : 1 ≤ R
  n_ge : N ≤ n
  n_pos : 0 < n
  vanishes : VanishesNear theta0 (angleFunToRaw psi)
  hit : F theta0 n psi = 1
  early_zero :
    ∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F theta0 j psi = 0
  future_bound :
    ∀ j : ℕ, R * n < j → |F theta0 j psi| ≤ futureTarget
  norm_bound : ‖psi‖ ≤ normTarget

def SpikeChoice.toPackage {theta0 : ℝ} {N : ℕ} (S : SpikeChoice theta0 N) :
    SpikePackage theta0 where
  R := S.R
  n := S.n
  psi := S.psi

def QuantSpikeChoice.toPackage
    {theta0 : ℝ} {N : ℕ} {futureTarget normTarget : ℝ}
    (S : QuantSpikeChoice theta0 N futureTarget normTarget) :
    SpikePackage theta0 where
  R := S.R
  n := S.n
  psi := S.psi

lemma AbstractBlockSpikeHypothesis.exists_spikeChoice
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (N : ℕ) :
    ∃ _ : SpikeChoice theta0 N, True := by
  obtain ⟨R, _C_R, n, psi, _hRmin, _hRodd, hR3, _hReta, _hC_R_pos, hnrow,
    hnpos, hvanish, hhit, hearly, _hfuture, _hnorm⟩ :=
    H.exists_spike_with_eta_lt (eps := 1) (delta := 1)
      zero_lt_one zero_lt_one 3 N
  have hRone : 1 ≤ R := by omega
  exact ⟨{
    R := R
    n := n
    psi := psi
    R_ge_one := hRone
    n_ge := hnrow
    n_pos := hnpos
    vanishes := hvanish
    hit := hhit
    early_zero := hearly }, trivial⟩

noncomputable def AbstractBlockSpikeHypothesis.chooseSpikeChoice
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (N : ℕ) :
    SpikeChoice theta0 N :=
  Classical.choose (H.exists_spikeChoice N)

lemma AbstractBlockSpikeHypothesis.exists_quantSpikeChoice
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (N : ℕ) {futureTarget normTarget : ℝ}
    (hfutureTarget : 0 < futureTarget)
    (hnormTarget : 0 < normTarget) :
    ∃ _ : QuantSpikeChoice theta0 N futureTarget normTarget, True := by
  have hhalf_future : 0 < futureTarget / 2 := by positivity
  obtain ⟨R, _C_R, n, psi, _hRmin, _hRodd, hR3, _hReta, _hC_R_pos, hnrow,
    hnpos, hvanish, hhit, hearly, hfuture, _hnorm, hnorm_target⟩ :=
    H.exists_spike_with_eta_lt_norm_le
      (eps := futureTarget / 2) (delta := futureTarget / 2)
      (normTarget := normTarget)
      hhalf_future hhalf_future hnormTarget 3 N
  have hRone : 1 ≤ R := by omega
  have hfuture_target :
      ∀ j : ℕ, R * n < j → |F theta0 j psi| ≤ futureTarget := by
    intro j hj
    have hjbound := hfuture j hj
    linarith
  exact ⟨{
    R := R
    n := n
    psi := psi
    R_ge_one := hRone
    n_ge := hnrow
    n_pos := hnpos
    vanishes := hvanish
    hit := hhit
    early_zero := hearly
    future_bound := hfuture_target
    norm_bound := hnorm_target }, trivial⟩

noncomputable def AbstractBlockSpikeHypothesis.chooseQuantSpikeChoice
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (N : ℕ) {futureTarget normTarget : ℝ}
    (hfutureTarget : 0 < futureTarget)
    (hnormTarget : 0 < normTarget) :
    QuantSpikeChoice theta0 N futureTarget normTarget :=
  Classical.choose (H.exists_quantSpikeChoice N hfutureTarget hnormTarget)

lemma AbstractBlockSpikeHypothesis.exists_quantSpikeChoice_with_nextCoeff_bound
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    (a : ℕ → ℝ) (c : ℝ)
    (coeff : ℕ → ℝ) (psiSeq : ℕ → AngleFun)
    (m N0 : ℕ)
    (hvanish :
      ∀ i : ℕ, i ∈ Finset.range m →
        VanishesNear theta0 (angleFunToRaw (psiSeq i)))
    (hbase : |a m - c| ≤ 2)
    {futureTarget normTarget : ℝ}
    (hfutureTarget : 0 < futureTarget)
    (hnormTarget : 0 < normTarget) :
    ∃ S : QuantSpikeChoice theta0 N0 futureTarget normTarget,
      |nextCoeff theta0 a c coeff psiSeq m S.n| ≤ 3 := by
  obtain ⟨N, hN0, hsmall⟩ :=
    H.exists_finset_spike_rows_abs_lt_of_mem coeff psiSeq
      (Finset.range m) hvanish zero_lt_one N0
  obtain ⟨S, _⟩ :=
    H.exists_quantSpikeChoice N hfutureTarget hnormTarget
  have hprev :
      |(Finset.range m).sum
        (fun i => coeff i * F theta0 S.n (psiSeq i))| < 1 :=
    hsmall S.n S.n_ge
  have hcoeff :
      |nextCoeff theta0 a c coeff psiSeq m S.n| ≤ 3 :=
    abs_nextCoeff_le_three_of_prev_sum_lt_one
      theta0 a c coeff psiSeq m S.n hbase hprev
  exact ⟨{
    R := S.R
    n := S.n
    psi := S.psi
    R_ge_one := S.R_ge_one
    n_ge := hN0.trans S.n_ge
    n_pos := S.n_pos
    vanishes := S.vanishes
    hit := S.hit
    early_zero := S.early_zero
    future_bound := S.future_bound
    norm_bound := S.norm_bound }, hcoeff⟩

/-- A finite controlled prefix of the diagonal spike construction.  The
sequence-valued fields are only constrained on indices `< m`; outside the
prefix they may take arbitrary values. -/
structure ControlledFinitePrefix
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ) (m : ℕ) where
  upper : ℕ
  RSeq : ℕ → ℕ
  nSeq : ℕ → ℕ
  psiSeq : ℕ → AngleFun
  coeff : ℕ → ℝ
  R_ge_one : ∀ i : ℕ, i < m → 1 ≤ RSeq i
  n_pos : ∀ i : ℕ, i < m → 0 < nSeq i
  n_lt_upper : ∀ i : ℕ, i < m → nSeq i < upper
  n_strict : ∀ i j : ℕ, i < j → j < m → nSeq i < nSeq j
  vanishes : ∀ i : ℕ, i < m → VanishesNear theta0 (angleFunToRaw (psiSeq i))
  hit : ∀ i : ℕ, i < m → F theta0 (nSeq i) (psiSeq i) = 1
  early_zero :
    ∀ i j : ℕ, i < m → 1 ≤ j → j ≤ RSeq i * nSeq i → j ≠ nSeq i →
      F theta0 j (psiSeq i) = 0
  future_bound :
    ∀ i j : ℕ, i < m → RSeq i * nSeq i < j →
      |F theta0 j (psiSeq i)| ≤ ((1 / 2 : ℝ) ^ i) / 4
  norm_bound :
    ∀ i : ℕ, i < m → ‖psiSeq i‖ ≤ ((1 / 2 : ℝ) ^ i) / 4
  coeff_bound : ∀ i : ℕ, i < m → |coeff i| ≤ 3
  coeff_eq :
    ∀ i : ℕ, i < m → coeff i = diagonalCoeff theta0 a c nSeq psiSeq i

/-- A successor prefix extends a prefix if it agrees with it on all old indices. -/
def ControlledFinitePrefix.Extends
    {theta0 : ℝ} {a : ℕ → ℝ} {c : ℝ} {m : ℕ}
    (P : ControlledFinitePrefix theta0 a c m)
    (Q : ControlledFinitePrefix theta0 a c (m + 1)) : Prop :=
  ∀ i : ℕ, i < m →
    Q.RSeq i = P.RSeq i ∧
    Q.nSeq i = P.nSeq i ∧
    Q.psiSeq i = P.psiSeq i ∧
    Q.coeff i = P.coeff i

lemma exists_controlledFinitePrefix_zero
    (theta0 : ℝ) (a : ℕ → ℝ) (c : ℝ) :
    ∃ _ : ControlledFinitePrefix theta0 a c 0, True := by
  exact ⟨{
    upper := 1
    RSeq := fun _ => 1
    nSeq := fun _ => 1
    psiSeq := fun _ => ContinuousMap.const AngleI 0
    coeff := fun _ => 0
    R_ge_one := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    n_pos := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    n_lt_upper := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    n_strict := by intro i j hij hj; exact False.elim (Nat.not_lt_zero j hj)
    vanishes := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    hit := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    early_zero := by intro i j hi; exact False.elim (Nat.not_lt_zero i hi)
    future_bound := by intro i j hi; exact False.elim (Nat.not_lt_zero i hi)
    norm_bound := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    coeff_bound := by intro i hi; exact False.elim (Nat.not_lt_zero i hi)
    coeff_eq := by intro i hi; exact False.elim (Nat.not_lt_zero i hi) }, trivial⟩

lemma ControlledFinitePrefix.exists_extend
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {m : ℕ} (P : ControlledFinitePrefix theta0 a c m) :
    ∃ Q : ControlledFinitePrefix theta0 a c (m + 1), P.Extends Q := by
  have htarget_pos : 0 < ((1 / 2 : ℝ) ^ m) / 4 := by positivity
  have hvanish :
      ∀ i : ℕ, i ∈ Finset.range m →
        VanishesNear theta0 (angleFunToRaw (P.psiSeq i)) := by
    intro i hi
    exact P.vanishes i (Finset.mem_range.mp hi)
  obtain ⟨S, hcoeff⟩ :=
    H.exists_quantSpikeChoice_with_nextCoeff_bound a c P.coeff P.psiSeq
      m P.upper hvanish (ha_bound m) htarget_pos htarget_pos
  let RSeq' : ℕ → ℕ := fun i => if i = m then S.R else P.RSeq i
  let nSeq' : ℕ → ℕ := fun i => if i = m then S.n else P.nSeq i
  let psiSeq' : ℕ → AngleFun := fun i => if i = m then S.psi else P.psiSeq i
  let coeff' : ℕ → ℝ := fun i =>
    if i = m then nextCoeff theta0 a c P.coeff P.psiSeq m S.n else P.coeff i
  have hdiag_prefix :
      ∀ i : ℕ, i < m →
        diagonalCoeff theta0 a c P.nSeq P.psiSeq i =
          diagonalCoeff theta0 a c nSeq' psiSeq' i := by
    exact diagonalCoeff_congr_of_eq_on_lt theta0 a c
      (m := m)
      (nSeq₁ := P.nSeq) (nSeq₂ := nSeq')
      (psiSeq₁ := P.psiSeq) (psiSeq₂ := psiSeq')
      (by
        intro i hi
        have him : i ≠ m := by omega
        simp [nSeq', him])
      (by
        intro i hi
        have him : i ≠ m := by omega
        simp [psiSeq', him])
  refine ⟨{
    upper := S.n + 1
    RSeq := RSeq'
    nSeq := nSeq'
    psiSeq := psiSeq'
    coeff := coeff'
    R_ge_one := ?_
    n_pos := ?_
    n_lt_upper := ?_
    n_strict := ?_
    vanishes := ?_
    hit := ?_
    early_zero := ?_
    future_bound := ?_
    norm_bound := ?_
    coeff_bound := ?_
    coeff_eq := ?_ }, ?_⟩
  · intro i hi
    by_cases him : i = m
    · simpa [RSeq', him] using S.R_ge_one
    · have hiold : i < m := by omega
      simpa [RSeq', him] using P.R_ge_one i hiold
  · intro i hi
    by_cases him : i = m
    · simpa [nSeq', him] using S.n_pos
    · have hiold : i < m := by omega
      simpa [nSeq', him] using P.n_pos i hiold
  · intro i hi
    by_cases him : i = m
    · simp [nSeq', him]
    · have hiold : i < m := by omega
      have hlt : P.nSeq i < S.n := (P.n_lt_upper i hiold).trans_le S.n_ge
      have hlt' : P.nSeq i < S.n + 1 := hlt.trans (Nat.lt_succ_self S.n)
      simpa [nSeq', him] using hlt'
  · intro i j hij hj
    by_cases hjm : j = m
    · have hiold : i < m := by omega
      have him : i ≠ m := by omega
      have hlt : P.nSeq i < S.n := (P.n_lt_upper i hiold).trans_le S.n_ge
      simpa [nSeq', him, hjm] using hlt
    · have hjold : j < m := by omega
      have hiold : i < m := lt_trans hij hjold
      have him : i ≠ m := by omega
      simpa [nSeq', him, hjm] using P.n_strict i j hij hjold
  · intro i hi
    by_cases him : i = m
    · simpa [psiSeq', him] using S.vanishes
    · have hiold : i < m := by omega
      simpa [psiSeq', him] using P.vanishes i hiold
  · intro i hi
    by_cases him : i = m
    · simpa [nSeq', psiSeq', him] using S.hit
    · have hiold : i < m := by omega
      simpa [nSeq', psiSeq', him] using P.hit i hiold
  · intro i j hi hjpos hle hne
    by_cases him : i = m
    · simpa [RSeq', nSeq', psiSeq', him] using
        S.early_zero j hjpos (by simpa [RSeq', nSeq', him] using hle)
          (by simpa [nSeq', him] using hne)
    · have hiold : i < m := by omega
      simpa [RSeq', nSeq', psiSeq', him] using
        P.early_zero i j hiold hjpos
          (by simpa [RSeq', nSeq', him] using hle)
          (by simpa [nSeq', him] using hne)
  · intro i j hi hfuture
    by_cases him : i = m
    · simpa [RSeq', nSeq', psiSeq', him] using
        S.future_bound j (by simpa [RSeq', nSeq', him] using hfuture)
    · have hiold : i < m := by omega
      simpa [RSeq', nSeq', psiSeq', him] using
        P.future_bound i j hiold (by simpa [RSeq', nSeq', him] using hfuture)
  · intro i hi
    by_cases him : i = m
    · simpa [psiSeq', him] using S.norm_bound
    · have hiold : i < m := by omega
      simpa [psiSeq', him] using P.norm_bound i hiold
  · intro i hi
    by_cases him : i = m
    · simpa [coeff', him] using hcoeff
    · have hiold : i < m := by omega
      simpa [coeff', him] using P.coeff_bound i hiold
  · intro i hi
    by_cases him : i = m
    · subst i
      rw [show coeff' m = nextCoeff theta0 a c P.coeff P.psiSeq m S.n by
        simp [coeff']]
      rw [nextCoeff, diagonalCoeff_eq]
      apply congrArg (fun x => a m - c - x)
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hjne : j ≠ m := by omega
      have hcoeffj :
          P.coeff j = diagonalCoeff theta0 a c nSeq' psiSeq' j :=
        (P.coeff_eq j hjm).trans (hdiag_prefix j hjm)
      rw [hcoeffj]
      simp [nSeq', psiSeq', hjne]
    · have hiold : i < m := by omega
      simpa [coeff', him] using (P.coeff_eq i hiold).trans (hdiag_prefix i hiold)
  · intro i hi
    have him : i ≠ m := by omega
    simp [RSeq', nSeq', psiSeq', coeff', him]

lemma AbstractBlockSpikeHypothesis.exists_controlledFinitePrefix
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    (m : ℕ) :
    ∃ _ : ControlledFinitePrefix theta0 a c m, True := by
  induction m with
  | zero =>
      exact exists_controlledFinitePrefix_zero theta0 a c
  | succ m ih =>
      obtain ⟨P, _⟩ := ih
      obtain ⟨Q, _hQ⟩ := P.exists_extend H ha_bound
      exact ⟨Q, trivial⟩

noncomputable def AbstractBlockSpikeHypothesis.controlledPrefixChain
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) :
    (m : ℕ) → ControlledFinitePrefix theta0 a c m
  | 0 => Classical.choose (exists_controlledFinitePrefix_zero theta0 a c)
  | m + 1 =>
      Classical.choose
        ((H.controlledPrefixChain ha_bound m).exists_extend H ha_bound)

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_extends
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    (H.controlledPrefixChain ha_bound m).Extends
      (H.controlledPrefixChain ha_bound (m + 1)) := by
  rw [controlledPrefixChain]
  exact Classical.choose_spec
    ((H.controlledPrefixChain ha_bound m).exists_extend H ha_bound)

noncomputable def AbstractBlockSpikeHypothesis.controlledRSeq
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) : ℕ :=
  (H.controlledPrefixChain ha_bound (m + 1)).RSeq m

noncomputable def AbstractBlockSpikeHypothesis.controlledNSeq
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) : ℕ :=
  (H.controlledPrefixChain ha_bound (m + 1)).nSeq m

noncomputable def AbstractBlockSpikeHypothesis.controlledPsiSeq
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) : AngleFun :=
  (H.controlledPrefixChain ha_bound (m + 1)).psiSeq m

noncomputable def AbstractBlockSpikeHypothesis.controlledCoeff
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) : ℝ :=
  (H.controlledPrefixChain ha_bound (m + 1)).coeff m

lemma AbstractBlockSpikeHypothesis.controlledRSeq_ge_one
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    1 ≤ H.controlledRSeq ha_bound m := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).R_ge_one m (by omega)

lemma AbstractBlockSpikeHypothesis.controlledNSeq_pos
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    0 < H.controlledNSeq ha_bound m := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).n_pos m (by omega)

lemma AbstractBlockSpikeHypothesis.controlledVanishes
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    VanishesNear theta0 (angleFunToRaw (H.controlledPsiSeq ha_bound m)) := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).vanishes m (by omega)

lemma AbstractBlockSpikeHypothesis.controlledHit
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    F theta0 (H.controlledNSeq ha_bound m) (H.controlledPsiSeq ha_bound m) = 1 := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).hit m (by omega)

lemma AbstractBlockSpikeHypothesis.controlledEarlyZero
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m j : ℕ)
    (hjpos : 1 ≤ j)
    (hle : j ≤ H.controlledRSeq ha_bound m * H.controlledNSeq ha_bound m)
    (hne : j ≠ H.controlledNSeq ha_bound m) :
    F theta0 j (H.controlledPsiSeq ha_bound m) = 0 := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).early_zero
    m j (by omega) hjpos hle hne

lemma AbstractBlockSpikeHypothesis.controlledFutureBound
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m j : ℕ)
    (hfuture : H.controlledRSeq ha_bound m * H.controlledNSeq ha_bound m < j) :
    |F theta0 j (H.controlledPsiSeq ha_bound m)| ≤ ((1 / 2 : ℝ) ^ m) / 4 := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).future_bound
    m j (by omega) hfuture

lemma AbstractBlockSpikeHypothesis.controlledNormBound
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    ‖H.controlledPsiSeq ha_bound m‖ ≤ ((1 / 2 : ℝ) ^ m) / 4 := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).norm_bound m (by omega)

lemma AbstractBlockSpikeHypothesis.controlledCoeffBound
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    |H.controlledCoeff ha_bound m| ≤ 3 := by
  exact (H.controlledPrefixChain ha_bound (m + 1)).coeff_bound m (by omega)

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_RSeq_succ_eq_of_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i m : ℕ} (hi : i < m) :
    (H.controlledPrefixChain ha_bound (m + 1)).RSeq i =
      (H.controlledPrefixChain ha_bound m).RSeq i :=
  (H.controlledPrefixChain_extends ha_bound m i hi).1

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_nSeq_succ_eq_of_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i m : ℕ} (hi : i < m) :
    (H.controlledPrefixChain ha_bound (m + 1)).nSeq i =
      (H.controlledPrefixChain ha_bound m).nSeq i :=
  (H.controlledPrefixChain_extends ha_bound m i hi).2.1

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_psiSeq_succ_eq_of_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i m : ℕ} (hi : i < m) :
    (H.controlledPrefixChain ha_bound (m + 1)).psiSeq i =
      (H.controlledPrefixChain ha_bound m).psiSeq i :=
  (H.controlledPrefixChain_extends ha_bound m i hi).2.2.1

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_coeff_succ_eq_of_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i m : ℕ} (hi : i < m) :
    (H.controlledPrefixChain ha_bound (m + 1)).coeff i =
      (H.controlledPrefixChain ha_bound m).coeff i :=
  (H.controlledPrefixChain_extends ha_bound m i hi).2.2.2

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_nSeq_add_eq_of_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i k : ℕ} (hi : i < k) (t : ℕ) :
    (H.controlledPrefixChain ha_bound (k + t)).nSeq i =
      (H.controlledPrefixChain ha_bound k).nSeq i := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have hi' : i < k + t := hi.trans_le (Nat.le_add_right k t)
      calc
        (H.controlledPrefixChain ha_bound (k + Nat.succ t)).nSeq i
            = (H.controlledPrefixChain ha_bound ((k + t) + 1)).nSeq i := by
                rw [Nat.add_succ]
        _ = (H.controlledPrefixChain ha_bound (k + t)).nSeq i :=
            H.controlledPrefixChain_nSeq_succ_eq_of_lt ha_bound hi'
        _ = (H.controlledPrefixChain ha_bound k).nSeq i := ih

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_nSeq_eq_of_lt_le
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i k l : ℕ} (hi : i < k) (hkl : k ≤ l) :
    (H.controlledPrefixChain ha_bound l).nSeq i =
      (H.controlledPrefixChain ha_bound k).nSeq i := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkl
  exact H.controlledPrefixChain_nSeq_add_eq_of_lt ha_bound hi t

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_psiSeq_add_eq_of_lt
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i k : ℕ} (hi : i < k) (t : ℕ) :
    (H.controlledPrefixChain ha_bound (k + t)).psiSeq i =
      (H.controlledPrefixChain ha_bound k).psiSeq i := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have hi' : i < k + t := hi.trans_le (Nat.le_add_right k t)
      calc
        (H.controlledPrefixChain ha_bound (k + Nat.succ t)).psiSeq i
            = (H.controlledPrefixChain ha_bound ((k + t) + 1)).psiSeq i := by
                rw [Nat.add_succ]
        _ = (H.controlledPrefixChain ha_bound (k + t)).psiSeq i :=
            H.controlledPrefixChain_psiSeq_succ_eq_of_lt ha_bound hi'
        _ = (H.controlledPrefixChain ha_bound k).psiSeq i := ih

lemma AbstractBlockSpikeHypothesis.controlledPrefixChain_psiSeq_eq_of_lt_le
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2)
    {i k l : ℕ} (hi : i < k) (hkl : k ≤ l) :
    (H.controlledPrefixChain ha_bound l).psiSeq i =
      (H.controlledPrefixChain ha_bound k).psiSeq i := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkl
  exact H.controlledPrefixChain_psiSeq_add_eq_of_lt ha_bound hi t

lemma AbstractBlockSpikeHypothesis.controlledNSeq_strict
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) :
    StrictMono (H.controlledNSeq ha_bound) := by
  intro i j hij
  have hprefix :
      (H.controlledPrefixChain ha_bound (j + 1)).nSeq i <
        (H.controlledPrefixChain ha_bound (j + 1)).nSeq j :=
    (H.controlledPrefixChain ha_bound (j + 1)).n_strict i j hij (by omega)
  have histable :
      (H.controlledPrefixChain ha_bound (j + 1)).nSeq i =
        H.controlledNSeq ha_bound i := by
    rw [controlledNSeq]
    exact H.controlledPrefixChain_nSeq_eq_of_lt_le
      ha_bound (i := i) (k := i + 1) (l := j + 1) (by omega) (by omega)
  simpa [controlledNSeq, histable] using hprefix

lemma AbstractBlockSpikeHypothesis.controlledCoeff_eq_diagonalCoeff
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    H.controlledCoeff ha_bound m =
      diagonalCoeff theta0 a c
        (H.controlledNSeq ha_bound) (H.controlledPsiSeq ha_bound) m := by
  have hprefix :=
    (H.controlledPrefixChain ha_bound (m + 1)).coeff_eq m (by omega)
  have hdiag :
      diagonalCoeff theta0 a c
          (H.controlledPrefixChain ha_bound (m + 1)).nSeq
          (H.controlledPrefixChain ha_bound (m + 1)).psiSeq m =
        diagonalCoeff theta0 a c
          (H.controlledNSeq ha_bound) (H.controlledPsiSeq ha_bound) m := by
    exact diagonalCoeff_congr_of_eq_on_lt theta0 a c
      (m := m + 1)
      (nSeq₁ := (H.controlledPrefixChain ha_bound (m + 1)).nSeq)
      (nSeq₂ := H.controlledNSeq ha_bound)
      (psiSeq₁ := (H.controlledPrefixChain ha_bound (m + 1)).psiSeq)
      (psiSeq₂ := H.controlledPsiSeq ha_bound)
      (by
        intro i hi
        rw [controlledNSeq]
        exact H.controlledPrefixChain_nSeq_eq_of_lt_le
          ha_bound (i := i) (k := i + 1) (l := m + 1) (by omega) (by omega))
      (by
        intro i hi
        rw [controlledPsiSeq]
        exact H.controlledPrefixChain_psiSeq_eq_of_lt_le
          ha_bound (i := i) (k := i + 1) (l := m + 1) (by omega) (by omega))
      m (by omega)
  exact hprefix.trans hdiag

lemma AbstractBlockSpikeHypothesis.controlledDiagonalCoeffBound
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) (m : ℕ) :
    |diagonalCoeff theta0 a c
      (H.controlledNSeq ha_bound) (H.controlledPsiSeq ha_bound) m| ≤ 3 := by
  rw [← H.controlledCoeff_eq_diagonalCoeff ha_bound m]
  exact H.controlledCoeffBound ha_bound m

noncomputable def recursiveSpikePackage
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) : ℕ → SpikePackage theta0
  | 0 => (H.chooseSpikeChoice 1).toPackage
  | m + 1 => (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).toPackage

lemma recursiveSpikePackage_succ_n_ge
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (m : ℕ) :
    (recursiveSpikePackage H m).n + 1 ≤ (recursiveSpikePackage H (m + 1)).n := by
  rw [recursiveSpikePackage]
  exact (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).n_ge

lemma recursiveSpikePackage_n_strict
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) :
    StrictMono fun m : ℕ => (recursiveSpikePackage H m).n :=
  strictMono_nat_of_lt_succ fun m =>
    Nat.lt_of_succ_le (recursiveSpikePackage_succ_n_ge H m)

lemma recursiveSpikePackage_R_ge_one
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (m : ℕ) :
    1 ≤ (recursiveSpikePackage H m).R := by
  cases m with
  | zero =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice 1).R_ge_one
  | succ m =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).R_ge_one

lemma recursiveSpikePackage_n_pos
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (m : ℕ) :
    0 < (recursiveSpikePackage H m).n := by
  cases m with
  | zero =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice 1).n_pos
  | succ m =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).n_pos

lemma recursiveSpikePackage_vanishes
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (m : ℕ) :
    VanishesNear theta0 (angleFunToRaw ((recursiveSpikePackage H m).psi)) := by
  cases m with
  | zero =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice 1).vanishes
  | succ m =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).vanishes

lemma recursiveSpikePackage_hit
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (m : ℕ) :
    F theta0 (recursiveSpikePackage H m).n (recursiveSpikePackage H m).psi = 1 := by
  cases m with
  | zero =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice 1).hit
  | succ m =>
      rw [recursiveSpikePackage]
      exact (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).hit

lemma recursiveSpikePackage_early_zero
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) (m j : ℕ)
    (hjpos : 1 ≤ j)
    (hle : j ≤ (recursiveSpikePackage H m).R * (recursiveSpikePackage H m).n)
    (hne : j ≠ (recursiveSpikePackage H m).n) :
    F theta0 j (recursiveSpikePackage H m).psi = 0 := by
  cases m with
  | zero =>
      rw [recursiveSpikePackage] at hle hne ⊢
      exact (H.chooseSpikeChoice 1).early_zero j hjpos hle hne
  | succ m =>
      rw [recursiveSpikePackage] at hle hne ⊢
      exact (H.chooseSpikeChoice ((recursiveSpikePackage H m).n + 1)).early_zero j hjpos hle hne

noncomputable def AbstractBlockSpikeHypothesis.diagonalSpikeData
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0) :
    DiagonalSpikeData theta0 where
  RSeq := fun m => (recursiveSpikePackage H m).R
  nSeq := fun m => (recursiveSpikePackage H m).n
  psiSeq := fun m => (recursiveSpikePackage H m).psi
  R_ge_one := recursiveSpikePackage_R_ge_one H
  n_pos := recursiveSpikePackage_n_pos H
  n_strict := recursiveSpikePackage_n_strict H
  vanishes := recursiveSpikePackage_vanishes H
  hit := recursiveSpikePackage_hit H
  early_zero := recursiveSpikePackage_early_zero H

lemma AbstractBlockSpikeHypothesis.angle_theorem_from_controlledDiagonalSpikeData
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI)
    (hcontrolled :
      ∀ c : ℝ, c ∈ A → ∀ a : ℕ → ℝ,
        (∀ m : ℕ, a m ∈ A) →
        clusterSet a = A →
        (∀ m : ℕ, |a m - c| ≤ 2) →
        ∃ _ : ControlledDiagonalSpikeData theta0 a c, True) :
    ∃ phi : AngleFun,
      clusterSet (fun m : ℕ => F theta0 (m.succ) phi) = A := by
  obtain ⟨c, hcA, a, ha_mem, ha_cluster, ha_bound⟩ :=
    exists_center_seq_clusterSet_eq_closed_nonempty_bounded
      hA_closed hA_nonempty hA_subset
  obtain ⟨D, _⟩ := hcontrolled c hcA a ha_mem ha_cluster ha_bound
  exact ⟨D.diagonalPhi, H.clusterSet_controlledDiagonalPhi_succ D ha_cluster hcA⟩

theorem AbstractBlockSpikeHypothesis.exists_controlledDiagonalSpikeData
    {theta0 : ℝ} {htheta0 : theta0 ∈ AngleI}
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {a : ℕ → ℝ} {c : ℝ}
    (ha_bound : ∀ m : ℕ, |a m - c| ≤ 2) :
    ∃ _ : ControlledDiagonalSpikeData theta0 a c, True := by
  exact ⟨{
    RSeq := H.controlledRSeq ha_bound
    nSeq := H.controlledNSeq ha_bound
    psiSeq := H.controlledPsiSeq ha_bound
    R_ge_one := H.controlledRSeq_ge_one ha_bound
    n_pos := H.controlledNSeq_pos ha_bound
    n_strict := H.controlledNSeq_strict ha_bound
    vanishes := H.controlledVanishes ha_bound
    hit := H.controlledHit ha_bound
    early_zero := H.controlledEarlyZero ha_bound
    coeff_bound := H.controlledDiagonalCoeffBound ha_bound
    norm_bound := H.controlledNormBound ha_bound
    future_bound := H.controlledFutureBound ha_bound }, trivial⟩

/-- First major milestone: the diagonal construction from abstract block spikes. -/
theorem angle_theorem_from_block_spikes
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ phi : AngleFun,
      clusterSet (fun m : ℕ => F theta0 (m.succ) phi) = A := by
  exact H.angle_theorem_from_controlledDiagonalSpikeData
    hA_closed hA_nonempty hA_subset
    (fun _c _hcA _a _ha_mem _ha_cluster ha_bound =>
      H.exists_controlledDiagonalSpikeData ha_bound)

end Erdos1151Formalization

end
