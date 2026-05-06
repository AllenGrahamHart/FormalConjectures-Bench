import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Lagrange
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

lemma thetaNode_mem_angleI {n k : ℕ} (hk : k < n) :
    thetaNode n k ∈ AngleI := by
  have hnpos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hden_pos : 0 < 2 * (n : ℝ) := by positivity
  have hnum_le : 2 * (k : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    norm_cast
    omega
  constructor
  · unfold thetaNode
    positivity
  · unfold thetaNode
    calc
      ((2 * (k : ℝ) + 1) * Real.pi) / (2 * (n : ℝ))
          ≤ ((2 * (n : ℝ)) * Real.pi) / (2 * (n : ℝ)) := by
            gcongr
      _ = Real.pi := by
        field_simp [ne_of_gt hden_pos]

lemma thetaNode_pos {n k : ℕ} (hk : k < n) :
    0 < thetaNode n k := by
  have hnpos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  unfold thetaNode
  positivity

lemma thetaNode_lt_pi {n k : ℕ} (hk : k < n) :
    thetaNode n k < Real.pi := by
  have hnpos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hden_pos : 0 < 2 * (n : ℝ) := by positivity
  have hnum_lt : 2 * (k : ℝ) + 1 < 2 * (n : ℝ) := by
    norm_cast
    omega
  unfold thetaNode
  calc
    ((2 * (k : ℝ) + 1) * Real.pi) / (2 * (n : ℝ))
        < ((2 * (n : ℝ)) * Real.pi) / (2 * (n : ℝ)) := by
          gcongr
    _ = Real.pi := by
      field_simp [ne_of_gt hden_pos]

lemma thetaNode_succ_sub {n k : ℕ} (hnpos : 0 < n) :
    thetaNode n (k + 1) - thetaNode n k = Real.pi / (n : ℝ) := by
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  unfold thetaNode
  field_simp [hnne]
  norm_num
  ring

lemma abs_thetaNode_pair_sub {n r : ℕ} (hnpos : 0 < n) :
    |thetaNode n (2 * r) - thetaNode n (2 * r + 1)| =
      Real.pi / (n : ℝ) := by
  have h :=
    thetaNode_succ_sub (n := n) (k := 2 * r) hnpos
  have hsub :
      thetaNode n (2 * r) - thetaNode n (2 * r + 1) =
        -(Real.pi / (n : ℝ)) := by
    linarith
  rw [hsub, abs_neg, abs_of_nonneg]
  positivity

lemma sin_thetaNode_pos {n k : ℕ} (hk : k < n) :
    0 < Real.sin (thetaNode n k) :=
  Real.sin_pos_of_pos_of_lt_pi (thetaNode_pos hk) (thetaNode_lt_pi hk)

lemma xNode_mem_spaceI (n k : ℕ) : xNode n k ∈ SpaceI :=
  Real.cos_mem_Icc _

lemma thetaNode_strictMonoOn (n : ℕ) :
    StrictMonoOn (thetaNode n) (Finset.range n) := by
  rcases n with _ | n
  · intro k hk
    simp at hk
  · intro k hk l hl hkl
    have hscale_pos : 0 < Real.pi / (2 * ((n.succ : ℕ) : ℝ)) := by
      positivity
    have hkl_real : (k : ℝ) < (l : ℝ) := by
      exact_mod_cast hkl
    have hlin : 2 * (k : ℝ) + 1 < 2 * (l : ℝ) + 1 := by
      nlinarith
    unfold thetaNode
    calc
      ((2 * (k : ℝ) + 1) * Real.pi) / (2 * ((n.succ : ℕ) : ℝ))
          = (2 * (k : ℝ) + 1) * (Real.pi / (2 * ((n.succ : ℕ) : ℝ))) := by
            ring
      _ < (2 * (l : ℝ) + 1) * (Real.pi / (2 * ((n.succ : ℕ) : ℝ))) :=
            mul_lt_mul_of_pos_right hlin hscale_pos
      _ = ((2 * (l : ℝ) + 1) * Real.pi) / (2 * ((n.succ : ℕ) : ℝ)) := by
            ring

lemma xNode_strictAntiOn_range (n : ℕ) :
    StrictAntiOn (xNode n) (Finset.range n) := by
  unfold xNode
  exact Real.strictAntiOn_cos.comp_strictMonoOn
    (thetaNode_strictMonoOn n)
    (fun k hk => thetaNode_mem_angleI (Finset.mem_range.mp hk))

lemma xNode_injOn_range (n : ℕ) :
    Set.InjOn (fun k : ℕ => xNode n k) (Finset.range n) :=
  (xNode_strictAntiOn_range n).injOn

/-- `theta0` is itself a row-`n` Chebyshev-root angle. -/
def IsNodeRow (theta0 : ℝ) (n : ℕ) : Prop :=
  Real.cos ((n : ℝ) * theta0) = 0

lemma isNodeRow_thetaNode {n k : ℕ} (hk : k < n) :
    IsNodeRow (thetaNode n k) n := by
  have hnpos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
  unfold IsNodeRow thetaNode
  have hangle :
      (n : ℝ) * (((2 * (k : ℝ) + 1) * Real.pi) / (2 * (n : ℝ))) =
        Real.pi / 2 + (k : ℝ) * Real.pi := by
    field_simp [hnne]
    ring
  rw [hangle]
  simpa [Real.cos_pi_div_two] using Real.cos_add_nat_mul_pi (Real.pi / 2) k

lemma sin_n_mul_thetaNode {n k : ℕ} (hk : k < n) :
    Real.sin ((n : ℝ) * thetaNode n k) = (-1 : ℝ) ^ k := by
  have hnpos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos_nat)
  unfold thetaNode
  have hangle :
      (n : ℝ) * (((2 * (k : ℝ) + 1) * Real.pi) / (2 * (n : ℝ))) =
        Real.pi / 2 + (k : ℝ) * Real.pi := by
    field_simp [hnne]
    ring
  rw [hangle]
  simpa [Real.sin_pi_div_two] using Real.sin_add_nat_mul_pi (Real.pi / 2) k

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

lemma rowEval_eq_cos_div_mul_sum_of_not_isNodeRow
    {theta0 : ℝ} {n : ℕ} {g : ℝ → ℝ}
    (hnpos : 0 < n) (hnot : ¬ IsNodeRow theta0 n) :
    rowEval theta0 n g =
      (Real.cos ((n : ℝ) * theta0) / (n : ℝ)) *
        (Finset.range n).sum fun k =>
          ((-1 : ℝ) ^ k) *
            (Real.sin (thetaNode n k) /
              (Real.cos theta0 - Real.cos (thetaNode n k))) *
            g (thetaNode n k) := by
  classical
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  rw [rowEval, if_neg hnne, if_neg hnot, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [lambdaWeight]
  ring

/-- Row functional on continuous angle maps. -/
def F (theta0 : ℝ) (n : ℕ) (phi : AngleFun) : ℝ :=
  rowEval theta0 n (angleFunToRaw phi)

lemma F_eq_cos_div_mul_sum_of_not_isNodeRow
    {theta0 : ℝ} {n : ℕ} {phi : AngleFun}
    (hnpos : 0 < n) (hnot : ¬ IsNodeRow theta0 n) :
    F theta0 n phi =
      (Real.cos ((n : ℝ) * theta0) / (n : ℝ)) *
        (Finset.range n).sum fun k =>
          ((-1 : ℝ) ^ k) *
            (Real.sin (thetaNode n k) /
              (Real.cos theta0 - Real.cos (thetaNode n k))) *
            angleFunToRaw phi (thetaNode n k) := by
  exact rowEval_eq_cos_div_mul_sum_of_not_isNodeRow hnpos hnot

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

lemma alternating_sum_even_eq_sum_pairs (f : ℕ → ℝ) (q : ℕ) :
    (Finset.range (2 * q)).sum (fun k => ((-1 : ℝ) ^ k) * f k) =
      (Finset.range q).sum (fun r => f (2 * r) - f (2 * r + 1)) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hlen : 2 * (q + 1) = 2 * q + 1 + 1 := by omega
      rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      simp [(even_two_mul q).neg_one_pow, (odd_two_mul_add_one q).neg_one_pow]
      ring

lemma alternating_sum_odd_eq_sum_pairs_add (f : ℕ → ℝ) (q : ℕ) :
    (Finset.range (2 * q + 1)).sum (fun k => ((-1 : ℝ) ^ k) * f k) =
      (Finset.range q).sum (fun r => f (2 * r) - f (2 * r + 1)) +
        f (2 * q) := by
  rw [Finset.sum_range_succ, alternating_sum_even_eq_sum_pairs]
  simp [(even_two_mul q).neg_one_pow]

lemma abs_alternating_sum_even_le_sum_abs_pairs (f : ℕ → ℝ) (q : ℕ) :
    |(Finset.range (2 * q)).sum (fun k => ((-1 : ℝ) ^ k) * f k)| ≤
      (Finset.range q).sum (fun r => |f (2 * r) - f (2 * r + 1)|) := by
  rw [alternating_sum_even_eq_sum_pairs]
  exact Finset.abs_sum_le_sum_abs _ _

lemma abs_alternating_sum_odd_le_sum_abs_pairs_add (f : ℕ → ℝ) (q : ℕ) :
    |(Finset.range (2 * q + 1)).sum (fun k => ((-1 : ℝ) ^ k) * f k)| ≤
      (Finset.range q).sum (fun r => |f (2 * r) - f (2 * r + 1)|) +
        |f (2 * q)| := by
  rw [alternating_sum_odd_eq_sum_pairs_add]
  exact (abs_add_le _ _).trans
    (add_le_add (Finset.abs_sum_le_sum_abs _ _) (le_refl _))

/-- Alternating midpoint average appearing in the off-point decay estimate. -/
def alternatingMidpointAverage (H : AngleFun) (n : ℕ) : ℝ :=
  if n = 0 then
    0
  else
    (1 / (n : ℝ)) *
      (Finset.range n).sum fun k =>
        ((-1 : ℝ) ^ k) * angleFunToRaw H (thetaNode n k)

lemma alternatingMidpointAverage_of_pos
    (H : AngleFun) {n : ℕ} (hnpos : 0 < n) :
    alternatingMidpointAverage H n =
      (1 / (n : ℝ)) *
        (Finset.range n).sum fun k =>
          ((-1 : ℝ) ^ k) * angleFunToRaw H (thetaNode n k) := by
  simp [alternatingMidpointAverage, Nat.ne_of_gt hnpos]

lemma abs_angleFunToRaw_thetaNode_le_norm
    (H : AngleFun) {n k : ℕ} (hk : k < n) :
    |angleFunToRaw H (thetaNode n k)| ≤ ‖H‖ := by
  have hmem : thetaNode n k ∈ AngleI := thetaNode_mem_angleI hk
  rw [angleFunToRaw_of_mem H hmem]
  simpa [Real.norm_eq_abs] using
    ContinuousMap.norm_coe_le_norm H ⟨thetaNode n k, hmem⟩

lemma abs_alternatingMidpointAverage_le_of_pair_bound
    (H : AngleFun) {n : ℕ} (hnpos : 0 < n) {eps : ℝ} (heps : 0 ≤ eps)
    (hpair :
      ∀ r : ℕ, 2 * r + 1 < n →
        |angleFunToRaw H (thetaNode n (2 * r)) -
          angleFunToRaw H (thetaNode n (2 * r + 1))| ≤ eps) :
    |alternatingMidpointAverage H n| ≤ eps + ‖H‖ / (n : ℝ) := by
  rw [alternatingMidpointAverage_of_pos H hnpos]
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨q, hq⟩
    subst n
    have hqq : q + q = 2 * q := by omega
    rw [hqq] at hnpos hpair ⊢
    have htwopos : 0 < 2 * q := by simpa using hnpos
    have hsum :=
      abs_alternating_sum_even_le_sum_abs_pairs
        (fun k => angleFunToRaw H (thetaNode (2 * q) k)) q
    have hsum_pair :
        (Finset.range q).sum
            (fun r =>
              |angleFunToRaw H (thetaNode (2 * q) (2 * r)) -
                angleFunToRaw H (thetaNode (2 * q) (2 * r + 1))|) ≤
          (Finset.range q).sum fun _ : ℕ => eps := by
      refine Finset.sum_le_sum ?_
      intro r hr
      exact hpair r (by
        rw [Finset.mem_range] at hr
        omega)
    have hsum_eps :
        |(Finset.range (2 * q)).sum
            (fun k => ((-1 : ℝ) ^ k) *
              angleFunToRaw H (thetaNode (2 * q) k))| ≤
          (q : ℝ) * eps := by
      calc
        |(Finset.range (2 * q)).sum
            (fun k => ((-1 : ℝ) ^ k) *
              angleFunToRaw H (thetaNode (2 * q) k))|
            ≤ (Finset.range q).sum
                (fun r =>
                  |angleFunToRaw H (thetaNode (2 * q) (2 * r)) -
                    angleFunToRaw H (thetaNode (2 * q) (2 * r + 1))|) := hsum
        _ ≤ (Finset.range q).sum fun _ : ℕ => eps := hsum_pair
        _ = (q : ℝ) * eps := by simp
    have hscaled :
        |(1 / ((2 * q : ℕ) : ℝ)) *
            (Finset.range (2 * q)).sum
              (fun k => ((-1 : ℝ) ^ k) *
                angleFunToRaw H (thetaNode (2 * q) k))| ≤ eps := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / ((2 * q : ℕ) : ℝ)))]
      calc
        (1 / ((2 * q : ℕ) : ℝ)) *
            |(Finset.range (2 * q)).sum
              (fun k => ((-1 : ℝ) ^ k) *
                angleFunToRaw H (thetaNode (2 * q) k))|
            ≤ (1 / ((2 * q : ℕ) : ℝ)) * ((q : ℝ) * eps) := by
              exact mul_le_mul_of_nonneg_left hsum_eps (by positivity)
        _ ≤ eps := by
          have hden_ne : (((2 * q : ℕ) : ℝ)) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt htwopos
          have hqle : (q : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by
            exact_mod_cast (by omega : q ≤ 2 * q)
          have hcoef :
              (1 / ((2 * q : ℕ) : ℝ)) * (q : ℝ) ≤ 1 := by
            calc
              (1 / ((2 * q : ℕ) : ℝ)) * (q : ℝ)
                  ≤ (1 / ((2 * q : ℕ) : ℝ)) * ((2 * q : ℕ) : ℝ) := by
                    exact mul_le_mul_of_nonneg_left hqle
                      (show 0 ≤ (1 / ((2 * q : ℕ) : ℝ)) by positivity)
              _ = 1 := by field_simp [hden_ne]
          calc
            (1 / ((2 * q : ℕ) : ℝ)) * ((q : ℝ) * eps)
                = ((1 / ((2 * q : ℕ) : ℝ)) * (q : ℝ)) * eps := by ring
            _ ≤ 1 * eps := mul_le_mul_of_nonneg_right hcoef heps
            _ = eps := by ring
    exact hscaled.trans
      (le_add_of_nonneg_right
        (show 0 ≤ ‖H‖ / ((2 * q : ℕ) : ℝ) by
          exact div_nonneg (norm_nonneg H) (by positivity)))
  · rcases hOdd with ⟨q, hq⟩
    have hn_eq : n = 2 * q + 1 := by omega
    subst n
    have hsum :=
      abs_alternating_sum_odd_le_sum_abs_pairs_add
        (fun k => angleFunToRaw H (thetaNode (2 * q + 1) k)) q
    have hsum_pair :
        (Finset.range q).sum
            (fun r =>
              |angleFunToRaw H (thetaNode (2 * q + 1) (2 * r)) -
                angleFunToRaw H (thetaNode (2 * q + 1) (2 * r + 1))|) ≤
          (Finset.range q).sum fun _ : ℕ => eps := by
      refine Finset.sum_le_sum ?_
      intro r hr
      exact hpair r (by
        rw [Finset.mem_range] at hr
        omega)
    have hleft :
        |angleFunToRaw H (thetaNode (2 * q + 1) (2 * q))| ≤ ‖H‖ :=
      abs_angleFunToRaw_thetaNode_le_norm H (by omega)
    have hsum_eps :
        |(Finset.range (2 * q + 1)).sum
            (fun k => ((-1 : ℝ) ^ k) *
              angleFunToRaw H (thetaNode (2 * q + 1) k))| ≤
          (q : ℝ) * eps + ‖H‖ := by
      calc
        |(Finset.range (2 * q + 1)).sum
            (fun k => ((-1 : ℝ) ^ k) *
              angleFunToRaw H (thetaNode (2 * q + 1) k))|
            ≤ (Finset.range q).sum
                (fun r =>
                  |angleFunToRaw H (thetaNode (2 * q + 1) (2 * r)) -
                    angleFunToRaw H (thetaNode (2 * q + 1) (2 * r + 1))|) +
                |angleFunToRaw H (thetaNode (2 * q + 1) (2 * q))| := hsum
        _ ≤ (Finset.range q).sum (fun _ : ℕ => eps) + ‖H‖ :=
              add_le_add hsum_pair hleft
        _ = (q : ℝ) * eps + ‖H‖ := by simp
    have hscaled :
        |(1 / (((2 * q + 1 : ℕ) : ℝ))) *
            (Finset.range (2 * q + 1)).sum
              (fun k => ((-1 : ℝ) ^ k) *
                angleFunToRaw H (thetaNode (2 * q + 1) k))| ≤
          eps + ‖H‖ / (((2 * q + 1 : ℕ) : ℝ)) := by
      rw [abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (1 / (((2 * q + 1 : ℕ) : ℝ))))]
      calc
        (1 / (((2 * q + 1 : ℕ) : ℝ))) *
            |(Finset.range (2 * q + 1)).sum
              (fun k => ((-1 : ℝ) ^ k) *
                angleFunToRaw H (thetaNode (2 * q + 1) k))|
            ≤ (1 / (((2 * q + 1 : ℕ) : ℝ))) *
                ((q : ℝ) * eps + ‖H‖) := by
              exact mul_le_mul_of_nonneg_left hsum_eps (by positivity)
        _ ≤ eps + ‖H‖ / (((2 * q + 1 : ℕ) : ℝ)) := by
          have hden_ne : ((((2 * q + 1 : ℕ) : ℝ))) ≠ 0 := by
            exact_mod_cast (by omega : (2 * q + 1 : ℕ) ≠ 0)
          have hqle : (q : ℝ) ≤ (((2 * q + 1 : ℕ) : ℝ)) := by
            exact_mod_cast (by omega : q ≤ 2 * q + 1)
          have hcoef :
              (1 / (((2 * q + 1 : ℕ) : ℝ))) * (q : ℝ) ≤ 1 := by
            calc
              (1 / (((2 * q + 1 : ℕ) : ℝ))) * (q : ℝ)
                  ≤ (1 / (((2 * q + 1 : ℕ) : ℝ))) *
                      (((2 * q + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hqle
                      (show 0 ≤ (1 / (((2 * q + 1 : ℕ) : ℝ))) by positivity)
              _ = 1 := by field_simp [hden_ne]
          have hmain :
              (1 / (((2 * q + 1 : ℕ) : ℝ))) * ((q : ℝ) * eps) ≤ eps := by
            calc
              (1 / (((2 * q + 1 : ℕ) : ℝ))) * ((q : ℝ) * eps)
                  = ((1 / (((2 * q + 1 : ℕ) : ℝ))) * (q : ℝ)) * eps := by ring
              _ ≤ 1 * eps := mul_le_mul_of_nonneg_right hcoef heps
              _ = eps := by ring
          calc
            (1 / (((2 * q + 1 : ℕ) : ℝ))) * ((q : ℝ) * eps + ‖H‖)
                = (1 / (((2 * q + 1 : ℕ) : ℝ))) * ((q : ℝ) * eps) +
                    ‖H‖ / (((2 * q + 1 : ℕ) : ℝ)) := by ring
            _ ≤ eps + ‖H‖ / (((2 * q + 1 : ℕ) : ℝ)) :=
              add_le_add hmain (le_refl _)
    exact hscaled

lemma alternatingMidpointAverage_tendsto_zero (H : AngleFun) :
    Tendsto (fun n : ℕ => alternatingMidpointAverage H n)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  let eps₂ : ℝ := eps / 2
  have heps₂ : 0 < eps₂ := by positivity
  have huc : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous H.continuous
  rcases (Metric.uniformContinuous_iff.mp huc) eps₂ heps₂ with
    ⟨rho, hrho, hH⟩
  have hpi_lim :
      Tendsto (fun n : ℕ => Real.pi / (n : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have hpi_event :
      ∀ᶠ n : ℕ in Filter.atTop, Real.pi / (n : ℝ) < rho :=
    (tendsto_order.mp hpi_lim).2 rho hrho
  have hnorm_lim :
      Tendsto (fun n : ℕ => ‖H‖ / (n : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat ‖H‖
  have hnorm_event :
      ∀ᶠ n : ℕ in Filter.atTop, ‖H‖ / (n : ℝ) < eps₂ :=
    (tendsto_order.mp hnorm_lim).2 eps₂ heps₂
  rcases Filter.eventually_atTop.mp hpi_event with ⟨Npi, hNpi⟩
  rcases Filter.eventually_atTop.mp hnorm_event with ⟨Nnorm, hNnorm⟩
  refine ⟨max 1 (max Npi Nnorm), ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hpi_lt : Real.pi / (n : ℝ) < rho :=
    hNpi n (by omega)
  have hnorm_lt : ‖H‖ / (n : ℝ) < eps₂ :=
    hNnorm n (by omega)
  have hpair :
      ∀ r : ℕ, 2 * r + 1 < n →
        |angleFunToRaw H (thetaNode n (2 * r)) -
          angleFunToRaw H (thetaNode n (2 * r + 1))| ≤ eps₂ := by
    intro r hr
    have hk0 : 2 * r < n := by omega
    have hk1 : 2 * r + 1 < n := hr
    have hmem0 : thetaNode n (2 * r) ∈ AngleI :=
      thetaNode_mem_angleI hk0
    have hmem1 : thetaNode n (2 * r + 1) ∈ AngleI :=
      thetaNode_mem_angleI hk1
    have hdist :
        dist (⟨thetaNode n (2 * r), hmem0⟩ : AngleI)
          (⟨thetaNode n (2 * r + 1), hmem1⟩ : AngleI) < rho := by
      have hdiff := abs_thetaNode_pair_sub (n := n) (r := r) hnpos
      simpa [Subtype.dist_eq, Real.dist_eq, hdiff] using hpi_lt
    have hout := hH hdist
    have hlt :
        |angleFunToRaw H (thetaNode n (2 * r)) -
          angleFunToRaw H (thetaNode n (2 * r + 1))| < eps₂ := by
      rw [angleFunToRaw_of_mem H hmem0, angleFunToRaw_of_mem H hmem1]
      simpa [Real.dist_eq] using hout
    exact le_of_lt hlt
  have hbound :=
    abs_alternatingMidpointAverage_le_of_pair_bound H hnpos
      (le_of_lt heps₂) hpair
  have hlt : |alternatingMidpointAverage H n| < eps := by
    have htail : eps₂ + ‖H‖ / (n : ℝ) < eps := by
      dsimp [eps₂] at hnorm_lt ⊢
      linarith
    exact lt_of_le_of_lt hbound htail
  simpa [Real.dist_eq] using hlt

lemma F_eq_cos_mul_alternatingMidpointAverage_of_not_isNodeRow
    {theta0 : ℝ} {n : ℕ} {phi H : AngleFun}
    (hnpos : 0 < n) (hnot : ¬ IsNodeRow theta0 n)
    (hkernel :
      ∀ k : ℕ, k < n →
        (Real.sin (thetaNode n k) /
          (Real.cos theta0 - Real.cos (thetaNode n k))) *
          angleFunToRaw phi (thetaNode n k) =
            angleFunToRaw H (thetaNode n k)) :
    F theta0 n phi =
      Real.cos ((n : ℝ) * theta0) * alternatingMidpointAverage H n := by
  rw [F_eq_cos_div_mul_sum_of_not_isNodeRow hnpos hnot]
  rw [alternatingMidpointAverage_of_pos H hnpos]
  have hsum :
      (Finset.range n).sum
          (fun k =>
            ((-1 : ℝ) ^ k) *
              (Real.sin (thetaNode n k) /
                (Real.cos theta0 - Real.cos (thetaNode n k))) *
              angleFunToRaw phi (thetaNode n k)) =
        (Finset.range n).sum
          (fun k => ((-1 : ℝ) ^ k) * angleFunToRaw H (thetaNode n k)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [mul_assoc, hkernel k (Finset.mem_range.mp hk)]
  rw [hsum]
  ring

lemma F_at_thetaNode {n k : ℕ} (phi : AngleFun) (hk : k < n) :
    F (thetaNode n k) n phi =
      phi ⟨thetaNode n k, thetaNode_mem_angleI hk⟩ := by
  have hnne : n ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)
  unfold F rowEval
  simpa [hnne, isNodeRow_thetaNode hk] using
    angleFunToRaw_of_mem phi (thetaNode_mem_angleI hk)

/-- A raw function vanishes on an angle-neighbourhood of `theta0`. -/
def VanishesNear (theta0 : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ eps > 0, ∀ theta ∈ AngleI, |theta - theta0| < eps → g theta = 0

lemma angleFunToRaw_continuousOn (phi : AngleFun) :
    ContinuousOn (angleFunToRaw phi) AngleI := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Set.restrict AngleI (angleFunToRaw phi) = phi := by
    ext theta
    exact angleFunToRaw_of_mem phi theta.2
  rw [h]
  exact phi.continuous

lemma VanishesNear.eq_zero
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {g : ℝ → ℝ} (hg : VanishesNear theta0 g) :
    g theta0 = 0 := by
  rcases hg with ⟨eps, heps, hzero⟩
  exact hzero theta0 htheta0 (by simpa using heps)

lemma rowEval_of_isNodeRow_vanishesNear
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {g : ℝ → ℝ} (hg : VanishesNear theta0 g)
    {n : ℕ} (hnpos : 0 < n) (hnode : IsNodeRow theta0 n) :
    rowEval theta0 n g = 0 := by
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  simp [rowEval, hnne, hnode, VanishesNear.eq_zero htheta0 hg]

lemma F_of_isNodeRow_vanishesNear
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi : AngleFun} (hphi : VanishesNear theta0 (angleFunToRaw phi))
    {n : ℕ} (hnpos : 0 < n) (hnode : IsNodeRow theta0 n) :
    F theta0 n phi = 0 := by
  exact rowEval_of_isNodeRow_vanishesNear htheta0 hphi hnpos hnode

lemma abs_F_le_abs_alternatingMidpointAverage_of_kernel
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi H : AngleFun} (hphi : VanishesNear theta0 (angleFunToRaw phi))
    (hkernel :
      ∀ n k : ℕ, k < n →
        (Real.sin (thetaNode n k) /
          (Real.cos theta0 - Real.cos (thetaNode n k))) *
          angleFunToRaw phi (thetaNode n k) =
            angleFunToRaw H (thetaNode n k))
    {n : ℕ} (hnpos : 0 < n) :
    |F theta0 n phi| ≤ |alternatingMidpointAverage H n| := by
  by_cases hnode : IsNodeRow theta0 n
  · rw [F_of_isNodeRow_vanishesNear htheta0 hphi hnpos hnode, abs_zero]
    exact abs_nonneg _
  · rw [F_eq_cos_mul_alternatingMidpointAverage_of_not_isNodeRow
      hnpos hnode (fun k hk => hkernel n k hk)]
    rw [abs_mul]
    simpa using
      mul_le_mul_of_nonneg_right
        (Real.abs_cos_le_one ((n : ℝ) * theta0))
        (abs_nonneg (alternatingMidpointAverage H n))

lemma off_point_decay_from_continuous_kernel
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi H : AngleFun}
    (hphi : VanishesNear theta0 (angleFunToRaw phi))
    (hkernel :
      ∀ n k : ℕ, k < n →
        (Real.sin (thetaNode n k) /
          (Real.cos theta0 - Real.cos (thetaNode n k))) *
          angleFunToRaw phi (thetaNode n k) =
            angleFunToRaw H (thetaNode n k)) :
    Tendsto (fun n : ℕ => F theta0 n phi) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have havg := alternatingMidpointAverage_tendsto_zero H
  rw [Metric.tendsto_atTop] at havg
  rcases havg eps heps with ⟨N, hN⟩
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hFbound :=
    abs_F_le_abs_alternatingMidpointAverage_of_kernel htheta0 hphi
      hkernel hnpos
  have havg_lt : |alternatingMidpointAverage H n| < eps := by
    have hdist := hN n (by omega)
    simpa [Real.dist_eq] using hdist
  have hlt : |F theta0 n phi| < eps :=
    lt_of_le_of_lt hFbound havg_lt
  simpa [Real.dist_eq] using hlt

/-- Raw removable-kernel candidate for the off-point decay quotient.  At the
removable point itself we set the value to zero. -/
def removableKernelRaw (theta0 : ℝ) (phi : AngleFun) : ℝ → ℝ :=
  fun theta =>
    if theta = theta0 then
      0
    else
      (Real.sin theta / (Real.cos theta0 - Real.cos theta)) *
        angleFunToRaw phi theta

lemma removableKernelRaw_eq_of_ne
    {theta0 theta : ℝ} (phi : AngleFun) (hne : theta ≠ theta0) :
    removableKernelRaw theta0 phi theta =
      (Real.sin theta / (Real.cos theta0 - Real.cos theta)) *
        angleFunToRaw phi theta := by
  simp [removableKernelRaw, hne]

lemma removableKernelRaw_eq_zero
    (theta0 : ℝ) (phi : AngleFun) :
    removableKernelRaw theta0 phi theta0 = 0 := by
  simp [removableKernelRaw]

lemma kernel_identity_of_removableKernelRaw
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi H : AngleFun}
    (hphi : VanishesNear theta0 (angleFunToRaw phi))
    (hH : ∀ theta ∈ AngleI,
      angleFunToRaw H theta = removableKernelRaw theta0 phi theta) :
    ∀ n k : ℕ, k < n →
      (Real.sin (thetaNode n k) /
        (Real.cos theta0 - Real.cos (thetaNode n k))) *
        angleFunToRaw phi (thetaNode n k) =
          angleFunToRaw H (thetaNode n k) := by
  intro n k hk
  have hmem : thetaNode n k ∈ AngleI := thetaNode_mem_angleI hk
  by_cases htheta : thetaNode n k = theta0
  · have hraw_zero : angleFunToRaw phi (thetaNode n k) = 0 := by
      rw [htheta]
      exact VanishesNear.eq_zero htheta0 hphi
    rw [hraw_zero, mul_zero, hH (thetaNode n k) hmem]
    simp [removableKernelRaw, htheta]
  · rw [hH (thetaNode n k) hmem]
    simp [removableKernelRaw, htheta]

lemma off_point_decay_from_removableKernelRaw
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi H : AngleFun}
    (hphi : VanishesNear theta0 (angleFunToRaw phi))
    (hH : ∀ theta ∈ AngleI,
      angleFunToRaw H theta = removableKernelRaw theta0 phi theta) :
    Tendsto (fun n : ℕ => F theta0 n phi) Filter.atTop (nhds 0) := by
  exact off_point_decay_from_continuous_kernel htheta0 hphi
    (kernel_identity_of_removableKernelRaw htheta0 hphi hH)

lemma continuous_removableKernelRaw_restrict
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi : AngleFun} (hphi : VanishesNear theta0 (angleFunToRaw phi)) :
    Continuous fun x : AngleI => removableKernelRaw theta0 phi x.1 := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.1 = theta0
  · rcases hphi with ⟨eps, heps, hzero⟩
    have habs_tend :
        Tendsto (fun y : AngleI => |y.1 - theta0|) (𝓝 x) (𝓝 0) := by
      have hval :
          Tendsto (fun y : AngleI => y.1) (𝓝 x) (𝓝 theta0) := by
        have hvalx :
            Tendsto (fun y : AngleI => (y : ℝ)) (𝓝 x) (𝓝 (x : ℝ)) :=
          continuous_subtype_val.continuousAt
        simpa [hx] using hvalx
      simpa using (hval.sub (tendsto_const_nhds (x := theta0))).abs
    have hevent :
        ∀ᶠ y : AngleI in 𝓝 x, |y.1 - theta0| < eps :=
      (tendsto_order.mp habs_tend).2 eps heps
    have hconst : ContinuousAt (fun _ : AngleI => (0 : ℝ)) x :=
      continuousAt_const
    refine hconst.congr ?_
    filter_upwards [hevent] with y hy
    by_cases hytheta : y.1 = theta0
    · simp [removableKernelRaw, hytheta]
    · have hyzero : angleFunToRaw phi y.1 = 0 :=
        hzero y.1 y.2 hy
      simp [removableKernelRaw, hytheta, hyzero]
  · have hxsub_ne : x ≠ (⟨theta0, htheta0⟩ : AngleI) := by
      intro h
      exact hx (congrArg Subtype.val h)
    have hne_event :
        ∀ᶠ y : AngleI in 𝓝 x, y.1 ≠ theta0 := by
      filter_upwards [eventually_ne_nhds hxsub_ne] with y hy hyeq
      exact hy (Subtype.ext hyeq)
    have hcos_ne : Real.cos theta0 ≠ Real.cos x.1 := by
      intro hcos
      have htheta_eq : theta0 = x.1 :=
        Real.injOn_cos htheta0 x.2 hcos
      exact hx htheta_eq.symm
    have hden : Real.cos theta0 - Real.cos x.1 ≠ 0 := sub_ne_zero.mpr hcos_ne
    have hcont :
        ContinuousAt (fun y : AngleI =>
          (Real.sin y.1 / (Real.cos theta0 - Real.cos y.1)) * phi y) x := by
      exact ((Real.continuous_sin.comp continuous_subtype_val).continuousAt.div
        ((continuous_const.sub
          (Real.continuous_cos.comp continuous_subtype_val)).continuousAt) hden).mul
        phi.continuous.continuousAt
    refine hcont.congr ?_
    filter_upwards [hne_event] with y hy
    rw [← angleFunToRaw_of_mem phi y.2]
    simp [removableKernelRaw, hy]

lemma exists_removableKernelRaw_angleFun
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    (phi : AngleFun) (hphi : VanishesNear theta0 (angleFunToRaw phi)) :
    ∃ H : AngleFun, ∀ theta ∈ AngleI,
      angleFunToRaw H theta = removableKernelRaw theta0 phi theta := by
  let H : AngleFun :=
    { toFun := fun x : AngleI => removableKernelRaw theta0 phi x.1
      continuous_toFun := continuous_removableKernelRaw_restrict htheta0 hphi }
  refine ⟨H, ?_⟩
  intro theta htheta
  exact angleFunToRaw_of_mem H htheta

/-- Off-point decay for the explicit row functional. -/
lemma off_point_decay
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {phi : AngleFun}
    (hphi : VanishesNear theta0 (angleFunToRaw phi)) :
    Tendsto (fun n : ℕ => F theta0 n phi) Filter.atTop (nhds 0) := by
  rcases exists_removableKernelRaw_angleFun htheta0 phi hphi with ⟨H, hH⟩
  exact off_point_decay_from_removableKernelRaw htheta0 hphi hH

/-- Convert an angle-side continuous function to a spatial-side continuous
function using the inverse cosine coordinate. -/
def angleToSpace (phi : AngleFun) : SpaceFun where
  toFun := fun x =>
    phi ⟨Real.arccos x.1, Real.arccos_nonneg x.1, Real.arccos_le_pi x.1⟩
  continuous_toFun := by
    exact phi.continuous.comp
      (Continuous.subtype_mk (Real.continuous_arccos.comp continuous_subtype_val) _)

lemma angleToSpace_apply (phi : AngleFun) (x : SpaceI) :
    angleToSpace phi x =
      phi ⟨Real.arccos x.1, Real.arccos_nonneg x.1, Real.arccos_le_pi x.1⟩ :=
  rfl

lemma angleToSpace_at_cos
    (phi : AngleFun) {theta : ℝ} (htheta : theta ∈ AngleI) :
    angleToSpace phi
      ⟨Real.cos theta, Real.neg_one_le_cos theta, Real.cos_le_one theta⟩ =
        phi ⟨theta, htheta⟩ := by
  rw [angleToSpace_apply]
  congr
  exact Real.arccos_cos htheta.1 htheta.2

lemma angleToSpace_at_arccos (phi : AngleFun) (x : SpaceI) :
    angleToSpace phi x =
      phi ⟨Real.arccos x.1, Real.arccos_nonneg x.1, Real.arccos_le_pi x.1⟩ :=
  rfl

lemma angleToSpace_const (c : ℝ) :
    angleToSpace (ContinuousMap.const AngleI c) =
      ContinuousMap.const SpaceI c := by
  ext x
  rfl

/-- Chebyshev-root Lagrange interpolation evaluated at a fixed point.

For row `n`, this is the degree `< n` polynomial interpolating `f` at the
`n` roots `xNode n k`, evaluated at `x0`. For `n = 0`, mathlib's empty
interpolant is `0`, matching the arbitrary zero convention used by `rowEval`.
-/
def chebLagEval (x0 : ℝ) (f : SpaceFun) (n : ℕ) : ℝ :=
  Polynomial.eval x0
    (Lagrange.interpolate (Finset.range n) (fun k : ℕ => xNode n k)
      (fun k : ℕ => f ⟨xNode n k, xNode_mem_spaceI n k⟩))

lemma chebLagEval_zero (x0 : ℝ) (f : SpaceFun) :
    chebLagEval x0 f 0 = 0 := by
  simp [chebLagEval]

lemma chebLagEval_const_succ (x0 c : ℝ) (n : ℕ) :
    chebLagEval x0 (ContinuousMap.const SpaceI c) n.succ = c := by
  let s : Finset ℕ := Finset.range n.succ
  let v : ℕ → ℝ := fun k => xNode n.succ k
  let r : ℕ → ℝ := fun _ => c
  have hs : s.Nonempty := ⟨0, by simp [s]⟩
  have hpoly : Lagrange.interpolate s v r = Polynomial.C c := by
    have hr : r = c • (1 : ℕ → ℝ) := by
      ext k
      simp [r]
    rw [hr, map_smul]
    rw [Lagrange.interpolate_one (xNode_injOn_range n.succ) hs]
    rw [Polynomial.smul_eq_C_mul c, mul_one]
  rw [chebLagEval]
  change Polynomial.eval x0 (Lagrange.interpolate s v r) = c
  rw [hpoly]
  simp

lemma chebLagEval_const_of_pos {x0 c : ℝ} {n : ℕ} (hnpos : 0 < n) :
    chebLagEval x0 (ContinuousMap.const SpaceI c) n = c := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero 0 hnpos)
  | succ n => exact chebLagEval_const_succ x0 c n

lemma chebLagEval_at_node_of_injOn
    {n k : ℕ} (f : SpaceFun)
    (hnodes : Set.InjOn (fun j : ℕ => xNode n j) (Finset.range n))
    (hk : k ∈ Finset.range n) :
    chebLagEval (xNode n k) f n =
      f ⟨xNode n k, xNode_mem_spaceI n k⟩ := by
  rw [chebLagEval]
  exact Lagrange.eval_interpolate_at_node
    (fun j : ℕ => f ⟨xNode n j, xNode_mem_spaceI n j⟩) hnodes hk

lemma chebLagEval_at_node
    {n k : ℕ} (f : SpaceFun) (hk : k < n) :
    chebLagEval (xNode n k) f n =
      f ⟨xNode n k, xNode_mem_spaceI n k⟩ :=
  chebLagEval_at_node_of_injOn f (xNode_injOn_range n)
    (Finset.mem_range.mpr hk)

lemma chebyshev_T_eval_xNode {n k : ℕ} (hk : k < n) :
    (Polynomial.Chebyshev.T ℝ n).eval (xNode n k) = 0 := by
  simpa [xNode, Polynomial.Chebyshev.T_real_cos] using
    isNodeRow_thetaNode hk

lemma chebyshev_U_eval_xNode_mul_sin {n k : ℕ} (hk : k < n) :
    (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (xNode n k) *
        Real.sin (thetaNode n k) =
      (-1 : ℝ) ^ k := by
  calc
    (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (xNode n k) *
        Real.sin (thetaNode n k)
        = Real.sin (((((n : ℤ) - 1) + 1 : ℤ) : ℝ) * thetaNode n k) := by
          simp [xNode,
            (Polynomial.Chebyshev.U_real_cos
              (θ := thetaNode n k) (n := ((n : ℤ) - 1)))]
    _ = Real.sin ((n : ℝ) * thetaNode n k) := by
          congr 1
          norm_num
    _ = (-1 : ℝ) ^ k := sin_n_mul_thetaNode hk

lemma cheb_nodal_eq_inv_leadingCoeff_mul_T (n : ℕ) :
    Lagrange.nodal (Finset.range n) (fun k : ℕ => xNode n k) =
      Polynomial.C ((2 : ℝ) ^ (n - 1))⁻¹ * Polynomial.Chebyshev.T ℝ n := by
  have hpow_ne : (2 : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hscale_ne : (((2 : ℝ) ^ (n - 1))⁻¹) ≠ 0 := inv_ne_zero hpow_ne
  refine Polynomial.eq_of_degree_le_of_eval_index_eq
    (s := Finset.range n) (v := fun k : ℕ => xNode n k)
    (f := Lagrange.nodal (Finset.range n) (fun k : ℕ => xNode n k))
    (g := Polynomial.C ((2 : ℝ) ^ (n - 1))⁻¹ * Polynomial.Chebyshev.T ℝ n)
    (xNode_injOn_range n) ?_ ?_ ?_ ?_
  · rw [Lagrange.degree_nodal]
  · rw [Lagrange.degree_nodal, Finset.card_range,
      Polynomial.degree_C_mul hscale_ne, Polynomial.Chebyshev.degree_T,
      Int.natAbs_natCast]
  · rw [(Lagrange.nodal_monic
      (s := Finset.range n) (v := fun k : ℕ => xNode n k)).leadingCoeff]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.Chebyshev.leadingCoeff_T, Int.natAbs_natCast]
    exact (inv_mul_cancel₀ hpow_ne).symm
  · intro k hk
    rw [Lagrange.eval_nodal_at_node hk, Polynomial.eval_mul, Polynomial.eval_C,
      chebyshev_T_eval_xNode (Finset.mem_range.mp hk), mul_zero]

lemma cheb_nodal_eval_cos_eq (n : ℕ) (theta : ℝ) :
    Polynomial.eval (Real.cos theta)
        (Lagrange.nodal (Finset.range n) (fun k : ℕ => xNode n k)) =
      ((2 : ℝ) ^ (n - 1))⁻¹ * Real.cos ((n : ℝ) * theta) := by
  rw [cheb_nodal_eq_inv_leadingCoeff_mul_T n, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos]
  norm_num

lemma cheb_nodal_derivative_eval_xNode_mul_sin
    {n k : ℕ} (hk : k < n) :
    Polynomial.eval (xNode n k)
        (Polynomial.derivative
          (Lagrange.nodal (Finset.range n) (fun j : ℕ => xNode n j))) *
        Real.sin (thetaNode n k) =
      ((2 : ℝ) ^ (n - 1))⁻¹ * (n : ℝ) * (-1 : ℝ) ^ k := by
  have hderiv := congrArg Polynomial.derivative
    (cheb_nodal_eq_inv_leadingCoeff_mul_T n)
  calc
    Polynomial.eval (xNode n k)
        (Polynomial.derivative
          (Lagrange.nodal (Finset.range n) (fun j : ℕ => xNode n j))) *
        Real.sin (thetaNode n k)
        =
          (((2 : ℝ) ^ (n - 1))⁻¹ * (n : ℝ)) *
            ((Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)).eval (xNode n k) *
              Real.sin (thetaNode n k)) := by
            rw [hderiv]
            simp [Polynomial.Chebyshev.T_derivative_eq_U, mul_assoc, mul_left_comm, mul_comm]
    _ = ((2 : ℝ) ^ (n - 1))⁻¹ * (n : ℝ) * (-1 : ℝ) ^ k := by
          rw [chebyshev_U_eval_xNode_mul_sin hk]

lemma cheb_nodalWeight_eq {n k : ℕ} (hk : k < n) :
    Lagrange.nodalWeight (Finset.range n) (fun j : ℕ => xNode n j) k =
      (2 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ k *
        Real.sin (thetaNode n k) / (n : ℝ) := by
  let D : ℝ := Polynomial.eval (xNode n k)
    (Polynomial.derivative
      (Lagrange.nodal (Finset.range n) (fun j : ℕ => xNode n j)))
  let s : ℝ := Real.sin (thetaNode n k)
  let L : ℝ := (2 : ℝ) ^ (n - 1)
  let e : ℝ := (-1 : ℝ) ^ k
  have hsin_ne : s ≠ 0 := ne_of_gt (by
    dsimp [s]
    exact sin_thetaNode_pos hk)
  have hL_ne : L ≠ 0 := by
    dsimp [L]
    exact pow_ne_zero _ (by norm_num)
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))
  have he_ne : e ≠ 0 := by
    dsimp [e]
    exact pow_ne_zero _ (by norm_num)
  have he_sq : e ^ 2 = 1 := by
    dsimp [e]
    rw [← pow_mul]
    have hEven : Even (k * 2) := ⟨k, by ring⟩
    exact hEven.neg_one_pow
  have hD_mul : D * s = L⁻¹ * (n : ℝ) * e := by
    dsimp [D, s, L, e]
    exact cheb_nodal_derivative_eval_xNode_mul_sin hk
  have hD_eq : D = (L⁻¹ * (n : ℝ) * e) / s := by
    rw [eq_div_iff hsin_ne]
    exact hD_mul
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_range.mpr hk)]
  change D⁻¹ = L * e * s / (n : ℝ)
  rw [hD_eq]
  field_simp [hL_ne, hn_ne, he_ne, hsin_ne]
  exact he_sq.symm

lemma chebLagEval_eq_barycentric_of_not_node
    {x0 : ℝ} {n : ℕ} (f : SpaceFun)
    (hx : ∀ k : ℕ, k ∈ Finset.range n → x0 ≠ xNode n k) :
    chebLagEval x0 f n =
      Polynomial.eval x0 (Lagrange.nodal (Finset.range n) (fun k : ℕ => xNode n k)) *
        ∑ k ∈ Finset.range n,
          Lagrange.nodalWeight (Finset.range n) (fun j : ℕ => xNode n j) k *
            (x0 - xNode n k)⁻¹ *
              f ⟨xNode n k, xNode_mem_spaceI n k⟩ := by
  rw [chebLagEval]
  exact Lagrange.eval_interpolate_not_at_node
    (fun k : ℕ => f ⟨xNode n k, xNode_mem_spaceI n k⟩) hx

lemma chebLagEval_angleToSpace_at_node
    {n k : ℕ} (phi : AngleFun) (hk : k < n) :
    chebLagEval (xNode n k) (angleToSpace phi) n =
      phi ⟨thetaNode n k, thetaNode_mem_angleI hk⟩ := by
  rw [chebLagEval_at_node (angleToSpace phi) hk]
  simpa [xNode] using angleToSpace_at_cos phi (thetaNode_mem_angleI hk)

lemma angleToSpace_xNode_eq_angleFunToRaw
    {n k : ℕ} (phi : AngleFun) (hk : k < n) :
    angleToSpace phi ⟨xNode n k, xNode_mem_spaceI n k⟩ =
      angleFunToRaw phi (thetaNode n k) := by
  rw [angleFunToRaw_of_mem phi (thetaNode_mem_angleI hk)]
  simpa [xNode] using angleToSpace_at_cos phi (thetaNode_mem_angleI hk)

lemma F_eq_chebLagEval_angleToSpace_at_node
    {n k : ℕ} (phi : AngleFun) (hk : k < n) :
    F (thetaNode n k) n phi =
      chebLagEval (xNode n k) (angleToSpace phi) n := by
  rw [F_at_thetaNode phi hk, chebLagEval_angleToSpace_at_node phi hk]

lemma cos_ne_xNode_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n : ℕ} (hnot : ¬ IsNodeRow theta0 n) :
    ∀ k : ℕ, k ∈ Finset.range n → Real.cos theta0 ≠ xNode n k := by
  intro k hk hcos
  have hklt : k < n := Finset.mem_range.mp hk
  have htheta_node : thetaNode n k ∈ AngleI := thetaNode_mem_angleI hklt
  have htheta_eq : theta0 = thetaNode n k := by
    apply Real.injOn_cos htheta0 htheta_node
    simpa [xNode] using hcos
  exact hnot (by simpa [htheta_eq] using isNodeRow_thetaNode hklt)

lemma chebLagEval_angleToSpace_eq_barycentric_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n : ℕ} (hnot : ¬ IsNodeRow theta0 n) (phi : AngleFun) :
    chebLagEval (Real.cos theta0) (angleToSpace phi) n =
      Polynomial.eval (Real.cos theta0)
          (Lagrange.nodal (Finset.range n) (fun k : ℕ => xNode n k)) *
        ∑ k ∈ Finset.range n,
          Lagrange.nodalWeight (Finset.range n) (fun j : ℕ => xNode n j) k *
            (Real.cos theta0 - xNode n k)⁻¹ *
              angleFunToRaw phi (thetaNode n k) := by
  rw [chebLagEval_eq_barycentric_of_not_node (angleToSpace phi)
    (cos_ne_xNode_of_not_isNodeRow htheta0 hnot)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [angleToSpace_xNode_eq_angleFunToRaw phi (Finset.mem_range.mp hk)]

lemma chebLagEval_angleToSpace_eq_F_of_not_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n : ℕ} (hnpos : 0 < n) (hnot : ¬ IsNodeRow theta0 n)
    (phi : AngleFun) :
    chebLagEval (Real.cos theta0) (angleToSpace phi) n =
      F theta0 n phi := by
  rw [chebLagEval_angleToSpace_eq_barycentric_of_not_isNodeRow htheta0 hnot phi]
  rw [cheb_nodal_eval_cos_eq n theta0]
  unfold F rowEval
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  simp [hnne, hnot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hL_ne : (2 : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hnne
  have hden_ne :
      Real.cos theta0 - Real.cos (thetaNode n k) ≠ 0 := by
    have hcos_ne := cos_ne_xNode_of_not_isNodeRow htheta0 hnot k hk
    simpa [xNode, sub_eq_zero] using hcos_ne
  rw [cheb_nodalWeight_eq hklt]
  unfold lambdaWeight xNode
  field_simp [hL_ne, hn_ne, hden_ne]

lemma exists_thetaNode_of_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n : ℕ} (_hnpos : 0 < n) (hnode : IsNodeRow theta0 n) :
    ∃ k : ℕ, k < n ∧ theta0 = thetaNode n k := by
  have hTzero : (Polynomial.Chebyshev.T ℝ n).eval (Real.cos theta0) = 0 := by
    simpa [Polynomial.Chebyshev.T_real_cos, IsNodeRow] using hnode
  have hroot : Real.cos theta0 ∈ (Polynomial.Chebyshev.T ℝ n).roots := by
    exact (Polynomial.mem_roots (Polynomial.Chebyshev.T_ne_zero (R := ℝ) n)).mpr hTzero
  rw [Polynomial.Chebyshev.roots_T_real n] at hroot
  simp at hroot
  rcases hroot with ⟨k, hk, hcos⟩
  have hklt : k < n := hk
  have htheta_node : thetaNode n k ∈ AngleI := thetaNode_mem_angleI hklt
  have htheta_eq : theta0 = thetaNode n k := by
    apply Real.injOn_cos htheta0 htheta_node
    simpa [thetaNode] using hcos.symm
  exact ⟨k, hklt, htheta_eq⟩

lemma chebLagEval_angleToSpace_eq_F_of_isNodeRow
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n : ℕ} (hnpos : 0 < n) (hnode : IsNodeRow theta0 n)
    (phi : AngleFun) :
    chebLagEval (Real.cos theta0) (angleToSpace phi) n =
      F theta0 n phi := by
  rcases exists_thetaNode_of_isNodeRow htheta0 hnpos hnode with ⟨k, hk, htheta_eq⟩
  rw [htheta_eq]
  simpa [xNode] using (F_eq_chebLagEval_angleToSpace_at_node phi hk).symm

lemma chebLagEval_angleToSpace_eq_F
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    {n : ℕ} (hnpos : 0 < n) (phi : AngleFun) :
    chebLagEval (Real.cos theta0) (angleToSpace phi) n =
      F theta0 n phi := by
  by_cases hnode : IsNodeRow theta0 n
  · exact chebLagEval_angleToSpace_eq_F_of_isNodeRow htheta0 hnpos hnode phi
  · exact chebLagEval_angleToSpace_eq_F_of_not_isNodeRow htheta0 hnpos hnode phi

lemma F_const_eval
    {theta0 : ℝ} (htheta0 : theta0 ∈ AngleI)
    (c : ℝ) {n : ℕ} (hnpos : 0 < n) :
    F theta0 n (ContinuousMap.const AngleI c) = c := by
  rw [← chebLagEval_angleToSpace_eq_F htheta0 hnpos
    (ContinuousMap.const AngleI c)]
  rw [angleToSpace_const c]
  exact chebLagEval_const_of_pos hnpos

end Erdos1151Formalization

end
