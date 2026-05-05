import Erdos1151Formalization.ClusterSequence
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

/-- First major milestone: the diagonal construction from abstract block spikes. -/
theorem angle_theorem_from_block_spikes
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ phi : AngleFun,
      clusterSet (fun m : ℕ => F theta0 (m.succ) phi) = A := by
  sorry

end Erdos1151Formalization

end
