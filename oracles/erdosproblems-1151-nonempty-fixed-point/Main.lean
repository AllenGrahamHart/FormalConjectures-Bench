import FormalConjecturesBench.Abstract
import FormalConjecturesBench.Spike

/-!
# Erdős Problem 1151, final target statement scaffold

The final theorem is stated now, but `chebLagEval` is currently a placeholder.
The intended route is:

1. prove `angle_theorem_from_block_spikes`;
2. prove concrete block spikes;
3. replace `chebLagEval` by the real Lagrange definition;
4. prove the Lagrange bridge and close this theorem.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos1151Formalization

lemma arccos_mem_angleI (x0 : ℝ) :
    Real.arccos x0 ∈ AngleI :=
  ⟨Real.arccos_nonneg x0, Real.arccos_le_pi x0⟩

noncomputable def concrete_finite_block_spike_hypothesis_angle
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI) :
    AbstractFiniteBlockSpikeHypothesis theta0 htheta0 := by
  refine {
    const_eval := ?_
    off_point_decay := ?_
    eta := etaSqrt (1 / (1 / 2 : ℝ))
    eta_nonneg := ?_
    eta_tendsto_zero := ?_
    exists_finite_spike := ?_ }
  · intro c n hnpos
    exact F_const_eval htheta0 c hnpos
  · intro psi hpsi
    exact off_point_decay htheta0 hpsi
  · exact etaSqrt_nonneg (by positivity)
  · exact etaSqrt_tendsto_zero (1 / (1 / 2 : ℝ))
  · simpa [etaSqrt] using
      exists_continuousSpike_finite_future_angle_all_odd htheta0

/-- Spatial fixed-point theorem, conditional on the angle-side block-spike
hypothesis at a matching angle. This is the completed Lagrange bridge from
`F` to `chebLagEval`; the remaining final-task input is the concrete proof of
`AbstractBlockSpikeHypothesis` for the explicit row functional. -/
theorem erdos1151_nonempty_fixed_point_from_block_spikes
    {x0 theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    (hx0 : x0 = Real.cos theta0)
    (H : AbstractBlockSpikeHypothesis theta0 htheta0)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  obtain ⟨phi, hphi⟩ :=
    angle_theorem_from_block_spikes htheta0 H hA_closed hA_nonempty hA_subset
  refine ⟨angleToSpace phi, ?_⟩
  rw [← hphi]
  apply clusterSet_congr
  intro m
  rw [hx0]
  exact chebLagEval_angleToSpace_eq_F htheta0 (Nat.succ_pos m) phi

/-- Final spatial theorem reduced to the concrete block-spike hypothesis at
the angle coordinate `arccos x0`. -/
theorem erdos1151_nonempty_fixed_point_from_arccos_block_spikes
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    (H : AbstractBlockSpikeHypothesis (Real.arccos x0)
      (arccos_mem_angleI x0))
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  exact erdos1151_nonempty_fixed_point_from_block_spikes
    (arccos_mem_angleI x0)
    (by simpa using (Real.cos_arccos hx0.1 hx0.2).symm)
    H hA_closed hA_nonempty hA_subset

/-- Final spatial theorem reduced to the remaining concrete analytic fields.
The constant-evaluation field of `AbstractBlockSpikeHypothesis` is already
proved by the Lagrange bridge and is supplied automatically here. -/
theorem erdos1151_nonempty_fixed_point_from_remaining_fields
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    (off_point_decay :
      ∀ psi : AngleFun,
        VanishesNear (Real.arccos x0) (angleFunToRaw psi) →
          Tendsto (fun n : ℕ => F (Real.arccos x0) n psi) Filter.atTop (nhds 0))
    (eta : ℕ → ℝ)
    (eta_nonneg : ∀ R, 0 ≤ eta R)
    (eta_tendsto_zero : Tendsto eta Filter.atTop (nhds 0))
    (exists_spike :
      ∀ R : ℕ, Odd R → 3 ≤ R →
        ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ, ∃ psi : AngleFun,
          N ≤ n ∧
          0 < n ∧
          VanishesNear (Real.arccos x0) (angleFunToRaw psi) ∧
          F (Real.arccos x0) n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F (Real.arccos x0) j psi = 0) ∧
          (∀ j : ℕ, R * n < j →
            |F (Real.arccos x0) j psi| ≤ eta R + delta) ∧
          ‖psi‖ ≤ C_R / Real.log (n : ℝ))
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  refine erdos1151_nonempty_fixed_point_from_arccos_block_spikes hx0 ?_
    hA_closed hA_nonempty hA_subset
  exact {
    const_eval := fun c n hnpos => F_const_eval (arccos_mem_angleI x0) c hnpos
    off_point_decay := off_point_decay
    eta := eta
    eta_nonneg := eta_nonneg
    eta_tendsto_zero := eta_tendsto_zero
    exists_spike := exists_spike }

/-- Final spatial theorem reduced to the natural square-root tail estimate
for the concrete block spikes. -/
theorem erdos1151_nonempty_fixed_point_from_sqrt_spikes
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    (C_eta : ℝ) (hC_eta : 0 ≤ C_eta)
    (off_point_decay :
      ∀ psi : AngleFun,
        VanishesNear (Real.arccos x0) (angleFunToRaw psi) →
          Tendsto (fun n : ℕ => F (Real.arccos x0) n psi) Filter.atTop (nhds 0))
    (exists_spike :
      ∀ R : ℕ, Odd R → 3 ≤ R →
        ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ, ∃ psi : AngleFun,
          N ≤ n ∧
          0 < n ∧
          VanishesNear (Real.arccos x0) (angleFunToRaw psi) ∧
          F (Real.arccos x0) n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F (Real.arccos x0) j psi = 0) ∧
          (∀ j : ℕ, R * n < j →
            |F (Real.arccos x0) j psi| ≤ etaSqrt C_eta R + delta) ∧
          ‖psi‖ ≤ C_R / Real.log (n : ℝ))
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  exact erdos1151_nonempty_fixed_point_from_remaining_fields hx0
    off_point_decay
    (etaSqrt C_eta)
    (etaSqrt_nonneg hC_eta)
    (etaSqrt_tendsto_zero C_eta)
    exists_spike
    hA_closed hA_nonempty hA_subset

/-- Final spatial theorem reduced to the removable-kernel construction for
off-point decay and the square-root block-spike estimate. -/
theorem erdos1151_nonempty_fixed_point_from_kernel_and_sqrt_spikes
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    (C_eta : ℝ) (hC_eta : 0 ≤ C_eta)
    (exists_kernel :
      ∀ psi : AngleFun,
        VanishesNear (Real.arccos x0) (angleFunToRaw psi) →
          ∃ H : AngleFun, ∀ n k : ℕ, k < n →
            (Real.sin (thetaNode n k) /
              (Real.cos (Real.arccos x0) - Real.cos (thetaNode n k))) *
              angleFunToRaw psi (thetaNode n k) =
                angleFunToRaw H (thetaNode n k))
    (exists_spike :
      ∀ R : ℕ, Odd R → 3 ≤ R →
        ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ, ∃ psi : AngleFun,
          N ≤ n ∧
          0 < n ∧
          VanishesNear (Real.arccos x0) (angleFunToRaw psi) ∧
          F (Real.arccos x0) n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F (Real.arccos x0) j psi = 0) ∧
          (∀ j : ℕ, R * n < j →
            |F (Real.arccos x0) j psi| ≤ etaSqrt C_eta R + delta) ∧
          ‖psi‖ ≤ C_R / Real.log (n : ℝ))
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  refine erdos1151_nonempty_fixed_point_from_sqrt_spikes hx0 C_eta hC_eta
    ?_ exists_spike hA_closed hA_nonempty hA_subset
  intro psi hpsi
  rcases exists_kernel psi hpsi with ⟨H, hH⟩
  exact off_point_decay_from_continuous_kernel (arccos_mem_angleI x0) hpsi hH

/-- Final spatial theorem reduced to constructing the removable raw kernel as
a continuous angle function, plus the square-root block-spike estimate. -/
theorem erdos1151_nonempty_fixed_point_from_removable_kernel_and_sqrt_spikes
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    (C_eta : ℝ) (hC_eta : 0 ≤ C_eta)
    (exists_removable_kernel :
      ∀ psi : AngleFun,
        VanishesNear (Real.arccos x0) (angleFunToRaw psi) →
          ∃ H : AngleFun, ∀ theta ∈ AngleI,
            angleFunToRaw H theta =
              removableKernelRaw (Real.arccos x0) psi theta)
    (exists_spike :
      ∀ R : ℕ, Odd R → 3 ≤ R →
        ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ, ∃ psi : AngleFun,
          N ≤ n ∧
          0 < n ∧
          VanishesNear (Real.arccos x0) (angleFunToRaw psi) ∧
          F (Real.arccos x0) n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F (Real.arccos x0) j psi = 0) ∧
          (∀ j : ℕ, R * n < j →
            |F (Real.arccos x0) j psi| ≤ etaSqrt C_eta R + delta) ∧
          ‖psi‖ ≤ C_R / Real.log (n : ℝ))
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  refine erdos1151_nonempty_fixed_point_from_kernel_and_sqrt_spikes
    hx0 C_eta hC_eta ?_ exists_spike hA_closed hA_nonempty hA_subset
  intro psi hpsi
  rcases exists_removable_kernel psi hpsi with ⟨H, hH⟩
  exact ⟨H, kernel_identity_of_removableKernelRaw (arccos_mem_angleI x0) hpsi hH⟩

/-- Final spatial theorem reduced only to the concrete square-root block-spike
estimate.  Off-point decay is now supplied by the removable-kernel construction. -/
theorem erdos1151_nonempty_fixed_point_from_concrete_sqrt_spikes
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    (C_eta : ℝ) (hC_eta : 0 ≤ C_eta)
    (exists_spike :
      ∀ R : ℕ, Odd R → 3 ≤ R →
        ∃ C_R > 0, ∀ N : ℕ, ∀ delta > 0, ∃ n : ℕ, ∃ psi : AngleFun,
          N ≤ n ∧
          0 < n ∧
          VanishesNear (Real.arccos x0) (angleFunToRaw psi) ∧
          F (Real.arccos x0) n psi = 1 ∧
          (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n →
            F (Real.arccos x0) j psi = 0) ∧
          (∀ j : ℕ, R * n < j →
            |F (Real.arccos x0) j psi| ≤ etaSqrt C_eta R + delta) ∧
          ‖psi‖ ≤ C_R / Real.log (n : ℝ))
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  refine erdos1151_nonempty_fixed_point_from_removable_kernel_and_sqrt_spikes
    hx0 C_eta hC_eta ?_ exists_spike hA_closed hA_nonempty hA_subset
  intro psi hpsi
  exact exists_removableKernelRaw_angleFun (arccos_mem_angleI x0) psi hpsi

/-- Erdős #1151, non-empty fixed-point scalar version. -/
theorem erdos1151_nonempty_fixed_point
    {x0 : ℝ} (hx0 : x0 ∈ SpaceI)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x0 f (m.succ)) = A := by
  refine erdos1151_nonempty_fixed_point_from_concrete_sqrt_spikes
    hx0 (1 / (1 / 2 : ℝ)) (by positivity) ?_
    hA_closed hA_nonempty hA_subset
  simpa [etaSqrt] using
    (exists_continuousSpike_global_future_angle_all_odd
      (arccos_mem_angleI x0))

end Erdos1151Formalization

end
