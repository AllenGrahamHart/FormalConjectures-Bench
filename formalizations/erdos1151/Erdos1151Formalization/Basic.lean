import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Erdős Problem 1151, basic angle-side definitions

This file starts with the fixed-point scalar interpretation.  The first
formalisation milestone is the angle-variable theorem for the explicit row
functional `F`; the Lagrange interpolation bridge is intentionally postponed.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Erdos1151Formalization

/-- Angle interval `[0, pi]`. -/
abbrev AngleI : Set ℝ := Set.Icc (0 : ℝ) Real.pi

/-- Spatial interval `[-1, 1]`. -/
abbrev SpaceI : Set ℝ := Set.Icc (-1 : ℝ) 1

/-- Continuous angle-side functions. -/
abbrev AngleFun := C(AngleI, ℝ)

/-- Continuous spatial-side functions. -/
abbrev SpaceFun := C(SpaceI, ℝ)

/-- The finite real cluster set of a real sequence. -/
def clusterSet (u : ℕ → ℝ) : Set ℝ :=
  {y | MapClusterPt y Filter.atTop u}

/-- Extend an angle-side continuous map by zero outside `[0, pi]`. -/
def angleFunToRaw (phi : AngleFun) : ℝ → ℝ :=
  fun theta => if h : theta ∈ AngleI then phi ⟨theta, h⟩ else 0

lemma angleFunToRaw_of_mem (phi : AngleFun) {theta : ℝ} (htheta : theta ∈ AngleI) :
    angleFunToRaw phi theta = phi ⟨theta, htheta⟩ := by
  simp [angleFunToRaw, htheta]

/-- The `k`-th Chebyshev-root angle in row `n`, zero-indexed. -/
def thetaNode (n k : ℕ) : ℝ :=
  ((2 * (k : ℝ) + 1) * Real.pi) / (2 * (n : ℝ))

/-- The corresponding Chebyshev root. -/
def xNode (n k : ℕ) : ℝ :=
  Real.cos (thetaNode n k)

/-- `theta0` is itself a row-`n` Chebyshev-root angle. -/
def IsNodeRow (theta0 : ℝ) (n : ℕ) : Prop :=
  Real.cos ((n : ℝ) * theta0) = 0

/-- The explicit Chebyshev-Lagrange row weight, meaningful for non-node rows. -/
def lambdaWeight (theta0 : ℝ) (n k : ℕ) : ℝ :=
  Real.cos ((n : ℝ) * theta0) / (n : ℝ)
    * ((-1 : ℝ) ^ k)
    * Real.sin (thetaNode n k)
    / (Real.cos theta0 - Real.cos (thetaNode n k))

/-- Raw explicit row functional in angle variables.

The `n = 0` value is arbitrary; final sequences use `m.succ`.
-/
def rowEval (theta0 : ℝ) (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  by
    classical
    exact
      if n = 0 then
        0
      else if IsNodeRow theta0 n then
        g theta0
      else
        (Finset.range n).sum fun k => lambdaWeight theta0 n k * g (thetaNode n k)

/-- Row functional on continuous angle maps. -/
def F (theta0 : ℝ) (n : ℕ) (phi : AngleFun) : ℝ :=
  rowEval theta0 n (angleFunToRaw phi)

/-- Continuous-linear evaluation against the zero extension of an angle map. -/
def angleEvalCLM (theta : ℝ) : AngleFun →L[ℝ] ℝ :=
  by
    classical
    exact
      if htheta : theta ∈ AngleI then
        ContinuousMap.evalCLM ℝ (⟨theta, htheta⟩ : AngleI)
      else
        0

lemma angleEvalCLM_apply (theta : ℝ) (phi : AngleFun) :
    angleEvalCLM theta phi = angleFunToRaw phi theta := by
  classical
  unfold angleEvalCLM angleFunToRaw
  split <;> simp [*]

/-- Continuous-linear version of the explicit row functional. -/
def FCLM (theta0 : ℝ) (n : ℕ) : AngleFun →L[ℝ] ℝ :=
  by
    classical
    exact
      if n = 0 then
        0
      else if IsNodeRow theta0 n then
        angleEvalCLM theta0
      else
        (Finset.range n).sum fun k =>
          (lambdaWeight theta0 n k) • angleEvalCLM (thetaNode n k)

lemma FCLM_apply (theta0 : ℝ) (n : ℕ) (phi : AngleFun) :
    FCLM theta0 n phi = F theta0 n phi := by
  classical
  unfold FCLM F rowEval
  split
  · simp
  · split
    · simp [angleEvalCLM_apply]
    · simp [angleEvalCLM_apply]

lemma F_add (theta0 : ℝ) (n : ℕ) (phi psi : AngleFun) :
    F theta0 n (phi + psi) = F theta0 n phi + F theta0 n psi := by
  rw [← FCLM_apply theta0 n (phi + psi), map_add]
  rw [FCLM_apply theta0 n phi, FCLM_apply theta0 n psi]

lemma F_smul (theta0 : ℝ) (n : ℕ) (c : ℝ) (phi : AngleFun) :
    F theta0 n (c • phi) = c * F theta0 n phi := by
  rw [← FCLM_apply theta0 n (c • phi), map_smul]
  rw [FCLM_apply theta0 n phi]
  rfl

lemma F_tsum {theta0 : ℝ} {n : ℕ} {phis : ℕ → AngleFun}
    (hphis : Summable phis) :
    F theta0 n (∑' m : ℕ, phis m) =
      ∑' m : ℕ, F theta0 n (phis m) := by
  rw [← FCLM_apply theta0 n (∑' m : ℕ, phis m)]
  rw [(FCLM theta0 n).map_tsum hphis]
  congr with m
  exact FCLM_apply theta0 n (phis m)

lemma F_tsum_smul {theta0 : ℝ} {n : ℕ} {coeff : ℕ → ℝ} {phis : ℕ → AngleFun}
    (hphis : Summable fun m : ℕ => coeff m • phis m) :
    F theta0 n (∑' m : ℕ, coeff m • phis m) =
      ∑' m : ℕ, coeff m * F theta0 n (phis m) := by
  rw [F_tsum hphis]
  congr with m
  exact F_smul theta0 n (coeff m) (phis m)

lemma F_const_add_tsum_smul
    {theta0 : ℝ} {n : ℕ} {c : ℝ} {coeff : ℕ → ℝ} {phis : ℕ → AngleFun}
    (hconst : F theta0 n (ContinuousMap.const AngleI c) = c)
    (hphis : Summable fun m : ℕ => coeff m • phis m) :
    F theta0 n (ContinuousMap.const AngleI c + ∑' m : ℕ, coeff m • phis m) =
      c + ∑' m : ℕ, coeff m * F theta0 n (phis m) := by
  rw [F_add, hconst, F_tsum_smul hphis]

/-- A raw function vanishes on an angle-neighbourhood of `theta0`. -/
def VanishesNear (theta0 : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps → g theta = 0

/-- Temporary placeholder for the spatial Lagrange evaluation.

This will be replaced by the real Chebyshev-root Lagrange interpolation
definition once the angle-side core has been built.
-/
def chebLagEval (_x0 : ℝ) (_f : SpaceFun) (_n : ℕ) : ℝ :=
  0

end Erdos1151Formalization

end
