import Erdos1151Formalization.ClusterSequence
import Mathlib.Analysis.SpecificLimits.Basic
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

/-- Abstract block-spike data sufficient for the diagonal cluster-set theorem. -/
structure AbstractBlockSpikeHypothesis
    (theta0 : ℝ) (_htheta0 : theta0 ∈ AngleI) where
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
