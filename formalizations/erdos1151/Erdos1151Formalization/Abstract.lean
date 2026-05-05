import Erdos1151Formalization.ClusterSequence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
  sorry

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
