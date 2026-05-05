# Erdős Problem #1151 — Lean formalisation brief

This is a Codex-oriented plan for formalising the **non-empty fixed-point scalar version** of Erdős Problem #1151 in Lean 4/mathlib.

The aim is not to make the code below compile immediately. The aim is to provide a detailed blueprint: definitions, normalisations, theorem statements, proof dependencies, and places where the informal proof needs to be expanded into Lean-grade lemmas.

## 0. Sources and status

Primary sources used for this brief:

- Problem page: `https://www.erdosproblems.com/forum/thread/1151`
- Submitted note: `https://www.ulam.ai/research/erdos1151.pdf`
- mathlib Lagrange interpolation docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Lagrange.html`
- mathlib Chebyshev roots/extrema docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.html`
- mathlib Chebyshev polynomial docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/Chebyshev.html`
- mathlib cluster point docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ClusterPt.html`
- mathlib Möbius docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Moebius.html`
- mathlib separability/dense sequence docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Bases.html`

The website says the original statement is ambiguous and that a claimed solution has been posted, but the problem has no formalised statement recorded on the site. The submitted note treats the scalar fixed-point interpretation: fix `x₀ ∈ [-1,1]`, evaluate the Chebyshev-root Lagrange interpolants at this fixed point, and prescribe the finite real cluster values of that scalar sequence.

## 1. Chosen target theorem and non-goals

### Revised implementation strategy

The target theorem below remains the final goal, but the implementation should
not start by proving the full Chebyshev/Lagrange bridge.  The first executable
formal core should be the angle-variable theorem for the explicit row functional
`F`, proved from an abstract block-spike hypothesis.  This separates the
diagonal construction and cluster-set argument from the hardest analytic and
API-heavy estimates.

Recommended proof chain:

```text
AbstractBlockSpikeHypothesis
  ⇒ angle_theorem_from_block_spikes
  ⇒ concrete block spikes from primitive rows, Möbius cancellation, and tents
  ⇒ angle_theorem_nonempty
  ⇒ Lagrange/Chebyshev bridge
  ⇒ erdos1151_nonempty_fixed_point
```

This is a deliberate change from a source-order formalisation.  It gives an
early compiled theorem that exercises the diagonal construction before we spend
time on the primitive mass estimate and the polynomial interpolation bridge.

### Target theorem

Formalise the following theorem first:

> For every fixed `x₀ ∈ [-1,1]` and every nonempty closed set `A ⊆ [-1,1]`, there exists a continuous function `f : [-1,1] → ℝ` such that the set of finite real cluster values of
>
> ```text
> n ↦ L_n f(x₀)
> ```
>
> is exactly `A`, where `L_n f` is the degree `< n` polynomial interpolating `f` at the `n` roots of the Chebyshev polynomial `T_n`.

In Lean terms, use `MapClusterPt y atTop u` for “`y` is a finite real cluster value of the sequence `u`”.

A schematic final statement:

```lean
noncomputable section
open scoped BigOperators Topology
open Filter Set Polynomial

namespace Erdos1151

/-- The finite real cluster set of a real sequence. -/
def clusterSet (u : ℕ → ℝ) : Set ℝ :=
  { y | MapClusterPt y Filter.atTop u }

/-- Chebyshev-root Lagrange interpolation evaluated at a fixed real point.
    `n` is the number of interpolation nodes. For `n = 0`, define it as `0`
    or avoid this case; the final sequence should use `n.succ`. -/
def chebLagEval
    (x₀ : ℝ)
    (f : C(Set.Icc (-1 : ℝ) 1, ℝ))
    (n : ℕ) : ℝ :=
  -- See Section 5 below.
  sorry

/-- Erdős #1151, non-empty fixed-point scalar version. -/
theorem erdos1151_nonempty_fixed_point
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (-1 : ℝ) 1)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      clusterSet (fun m : ℕ => chebLagEval x₀ f (m.succ)) = A := by
  sorry

end Erdos1151
```

### Non-goals for the first pass

Do **not** initially formalise:

1. The `A = ∅` classification. The submitted note uses Erdős’s corrected strong-divergence theorem for the positive direction and a forced-subsequence argument for the negative direction. This is a separate project.
2. The “domain-set” reading of the problem.
3. The “same cluster set for every `x`” reading.
4. Any statement involving divergence to infinity. We only need finite real cluster values for nonempty closed `A`.

The proof below is self-contained for the nonempty case, except for ordinary mathlib facts about real analysis, Chebyshev polynomials, finite sums, divisors, Möbius inversion, compactness, separability, and cluster points.

## 2. High-level strategy

The submitted proof works in angle variables.

Write

```text
x = cos θ,       θ ∈ [0,π],
x₀ = cos θ₀,    θ₀ ∈ [0,π].
```

The Chebyshev roots are

```text
x_{k,n} = cos θ_{k,n},
θ_{k,n} = (2k+1)π/(2n),       0 ≤ k < n.
```

For a continuous angle function `φ : [0,π] → ℝ`, define the row functional

```text
F_n φ = L_n f(x₀),     where f(cos θ) = φ(θ).
```

If `x₀` is not a row-`n` node, the explicit formula is

```text
F_n φ = ∑_{k=0}^{n-1} λ_{k,n}(θ₀) φ(θ_{k,n}),

λ_{k,n}(θ₀)
  = cos(n θ₀) / n
    * (-1)^k
    * sin(θ_{k,n}) / (cos θ₀ - cos θ_{k,n}).
```

If `x₀` is a row-`n` node, then

```text
F_n φ = φ(θ₀).
```

The construction then builds continuous “block spikes” `ψ_m` such that:

```text
F_{n_m} ψ_m = 1,
F_j ψ_m = 0       for earlier rows j ≤ R_m n_m, j ≠ n_m,
|F_j ψ_m| small   for future rows j > R_m n_m,
‖ψ_m‖∞ small,
ψ_m vanishes near θ₀.
```

Choose a sequence `(a_m)` in `A` whose cluster set is exactly `A`. Recursively choose coefficients `b_m` so that, for

```text
φ = c + ∑_{m=0}^∞ b_m ψ_m,
```

one has

```text
F_{n_m} φ = a_m.
```

All non-selected rows tend to `c ∈ A`. Hence the full cluster set is exactly `A`.

## 3. Recommended module/file layout

A practical decomposition:

```text
Erdos1151/
  Basic.lean
    intervals, nodes, row functional, clusterSet

  Abstract.lean
    AbstractBlockSpikeHypothesis and angle_theorem_from_block_spikes

  OffPointDecay.lean
    alternating midpoint sum lemma and F_n ψ → 0 for ψ vanishing near θ₀

  DyadicRows.lean
    good dyadic row lemma

  PrimitiveRows.lean
    primitive nodes, primitive mass lower bound, row occurrence lemmas

  AlgebraicSpike.lean
    finite Möbius spike on primitive nodes

  BlockSpike.lean
    continuous tent-function spike and future-row estimates

  ClusterSequence.lean
    sequence in A with cluster set A; selected/nonselected cluster-set lemmas

  Construction.lean
    concrete block-spike theorem and angle_theorem_nonempty

  LagrangeBridge.lean
    proof that explicit row functional equals Lagrange interpolation at Chebyshev roots

  Main.lean
    transfer from angle theorem to original `f : [-1,1] → ℝ`
```

For early iteration, it is fine to put everything in one file with many local `sorry`s, but this dependency graph is the best long-term structure.

The first pass should build only `Basic.lean`, `Abstract.lean`, and a skeletal
`Main.lean`.  `LagrangeBridge.lean` should be postponed until the abstract
diagonal theorem is working.

## 4. Imports and namespace setup

Start broad; narrow later.

```lean
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Topology
open Filter Set Polynomial

namespace Erdos1151
```

Some module names may need adjustment. If import churn becomes annoying during early work, temporarily use:

```lean
import Mathlib
```

and later reduce imports.

## 5. Core definitions

### 5.1 Intervals

Use subtypes for continuous functions, but use raw real functions for finite row algebra.

```lean
abbrev AngleI : Set ℝ := Set.Icc (0 : ℝ) Real.pi
abbrev SpaceI : Set ℝ := Set.Icc (-1 : ℝ) 1

abbrev AngleFun := C(AngleI, ℝ)
abbrev SpaceFun := C(SpaceI, ℝ)
```

Useful coercion helpers:

```lean
/-- Extend an angle continuous map by zero outside `[0,π]`.
    Row evaluations will only use points in `[0,π]`, so the outside value is irrelevant. -/
def AngleFun.toRaw (φ : AngleFun) : ℝ → ℝ :=
  fun θ => if h : θ ∈ AngleI then φ ⟨θ, h⟩ else 0

lemma AngleFun.toRaw_of_mem (φ : AngleFun) {θ : ℝ} (hθ : θ ∈ AngleI) :
    φ.toRaw θ = φ ⟨θ, hθ⟩ := by
  simp [AngleFun.toRaw, hθ]
```

### 5.2 Chebyshev root angles and nodes

Use `0`-indexed nodes. This matches mathlib’s `roots_T_real` formula.

```lean
/-- The `k`-th Chebyshev-root angle in row `n`, zero-indexed. -/
def θnode (n k : ℕ) : ℝ :=
  ((2 * (k : ℝ) + 1) * Real.pi) / (2 * (n : ℝ))

/-- The corresponding Chebyshev root. -/
def xnode (n k : ℕ) : ℝ :=
  Real.cos (θnode n k)
```

Basic lemmas to prove early:

```lean
lemma θnode_pos {n k : ℕ} (hn : 0 < n) :
    0 < θnode n k := by
  sorry

lemma θnode_lt_pi {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    θnode n k < Real.pi := by
  sorry

lemma θnode_mem_Icc {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    θnode n k ∈ AngleI := by
  exact ⟨le_of_lt (θnode_pos hn), le_of_lt (θnode_lt_pi hn hk)⟩

lemma xnode_mem_Icc {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    xnode n k ∈ SpaceI := by
  -- cos maps `[0,π]` into `[-1,1]`; `nlinarith` with `Real.neg_one_le_cos`, `Real.cos_le_one`.
  sorry
```

Injectivity of `xnode n` on `Finset.range n` is needed for Lagrange interpolation.

```lean
lemma xnode_injOn_range {n : ℕ} (hn : 0 < n) :
    Set.InjOn (xnode n) (Finset.range n : Set ℕ) := by
  -- Option A: use strict monotonicity of `θnode n k` and strict antitonicity of cos on `[0,π]`.
  -- Option B: use `Polynomial.Chebyshev.roots_T_real_nodup n` and translate `Nodup` to `InjOn`.
  sorry
```

Option B should be cleaner because mathlib already has:

```lean
Polynomial.Chebyshev.roots_T_real_nodup
Polynomial.Chebyshev.roots_T_real
```

with roots listed as

```lean
Real.cos ((2 * ↑k + 1) * Real.pi / (2 * ↑n)),  k ∈ Finset.range n.
```

### 5.3 Node rows

For `θ₀ ∈ [0,π]`, `x₀ = cos θ₀` is a row-`n` Chebyshev node iff `cos(n θ₀) = 0`. Define node rows this way, because it makes later algebra cleaner.

```lean
def IsNodeRow (θ₀ : ℝ) (n : ℕ) : Prop :=
  Real.cos ((n : ℝ) * θ₀) = 0
```

Prove the bridge to actual nodes:

```lean
lemma isNodeRow_iff_exists_node
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI) {n : ℕ} (hn : 0 < n) :
    IsNodeRow θ₀ n ↔ ∃ k ∈ Finset.range n, θ₀ = θnode n k := by
  -- Use zeros of cos: `cos t = 0` iff `t = (m + 1/2)π` modulo π`.
  -- Or use Chebyshev roots: `T_n(cos θ₀)=cos(nθ₀)`, roots are exactly the nodes,
  -- and cos is injective on `[0,π]`.
  sorry
```

This lemma may be one of the trickier trig lemmas. It is not needed in every algebraic step if `rowEval` is defined directly using `IsNodeRow`, but it is needed for the Lagrange bridge.

### 5.4 Lagrange weights and explicit row functional

Define the weight for non-node rows. With zero-indexing, the sign is `(-1)^k`.

```lean
/-- The explicit Chebyshev-Lagrange row weight. Meaningful for `0 < n` and non-node rows. -/
def λ (θ₀ : ℝ) (n k : ℕ) : ℝ :=
  Real.cos ((n : ℝ) * θ₀) / (n : ℝ)
    * ((-1 : ℝ) ^ k)
    * Real.sin (θnode n k)
    / (Real.cos θ₀ - Real.cos (θnode n k))
```

Define a row functional on raw functions `g : ℝ → ℝ`.

```lean
/-- Explicit row functional in angle variables, on raw real functions.
    The `n = 0` value is arbitrary; final sequences use `n.succ`. -/
def rowEval (θ₀ : ℝ) (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  if hn : n = 0 then 0
  else if hnode : IsNodeRow θ₀ n then g θ₀
  else ∑ k in Finset.range n, λ θ₀ n k * g (θnode n k)

/-- Row functional on continuous angle maps. -/
def F (θ₀ : ℝ) (n : ℕ) (φ : AngleFun) : ℝ :=
  rowEval θ₀ n φ.toRaw
```

For infinite sums, define a continuous linear version.

```lean
/-- Continuous linear row functional on `C([0,π], ℝ)`.
    Implement by cases: node row = evaluation at θ₀; non-node row = finite linear combination
    of evaluations at θnode n k. -/
def FCLM (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI) (n : ℕ) : AngleFun →L[ℝ] ℝ :=
  sorry

lemma FCLM_apply (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI) (n : ℕ) (φ : AngleFun) :
    FCLM θ₀ hθ₀ n φ = F θ₀ n φ := by
  sorry
```

Implementation details for `FCLM`:

- Evaluation at a point of a compact domain is continuous linear: search for `ContinuousMap.evalCLM`, `ContinuousMap.evalContinuousLinearMap`, or use an existing lemma. If hard to find, define a continuous linear map manually.
- A finite sum of continuous linear maps is continuous linear.
- For a node row, use `φ ↦ φ ⟨θ₀,hθ₀⟩`.
- For a non-node row, use `∑ k ∈ range n, λ θ₀ n k • eval_{θnode n k}`.

### 5.5 The original Lagrange interpolation operator

Define Chebyshev-root interpolation on the spatial interval.

```lean
/-- Values of a continuous `f : [-1,1] → ℝ` at Chebyshev roots. -/
def chebValues (f : SpaceFun) (n : ℕ) : ℕ → ℝ :=
  fun k =>
    if hk : k < n then
      f ⟨xnode n k, xnode_mem_Icc (Nat.pos_of_ne_zero ?_) hk⟩
    else 0
```

The above sketch has a problem: `xnode_mem_Icc` needs `0 < n`; in the `n=0` branch this is irrelevant. Better define `chebLagEval` by cases:

```lean
def chebLagEval (x₀ : ℝ) (f : SpaceFun) (n : ℕ) : ℝ :=
  if hn : n = 0 then 0
  else
    let nodes : ℕ → ℝ := xnode n
    let values : ℕ → ℝ := fun k =>
      if hk : k < n then
        f ⟨xnode n k, xnode_mem_Icc (Nat.pos_of_ne_zero hn) hk⟩
      else 0
    Polynomial.eval x₀ ((Lagrange.interpolate (Finset.range n) nodes) values)
```

Prove basic interpolation lemmas using mathlib:

```lean
lemma chebLagEval_at_node
    {n k : ℕ} (hn : 0 < n) (hk : k < n)
    (f : SpaceFun) :
    chebLagEval (xnode n k) f n =
      f ⟨xnode n k, xnode_mem_Icc hn hk⟩ := by
  -- unfold `chebLagEval`; use `Lagrange.eval_interpolate_at_node`
  -- with `xnode_injOn_range hn`.
  sorry
```

The main bridge lemma:

```lean
/-- If `f(x) = φ(arccos x)` and `x₀ = cos θ₀`, then Lagrange evaluation equals `F`. -/
lemma chebLagEval_eq_F
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    (φ : AngleFun)
    (n : ℕ) :
    chebLagEval (Real.cos θ₀) (angleToSpace φ) n = F θ₀ n φ := by
  -- For n=0, both definitions are 0.
  -- For node row: use `isNodeRow_iff_exists_node`, interpolation at a node, and `arccos_cos`.
  -- For non-node row: use explicit Lagrange weight formula.
  sorry
```

Here `angleToSpace` is:

```lean
/-- Given `φ : [0,π] → ℝ`, produce `f : [-1,1] → ℝ` by `f(x) = φ(arccos x)`. -/
def angleToSpace (φ : AngleFun) : SpaceFun :=
  { toFun := fun x =>
      φ ⟨Real.arccos x.1, by
        constructor
        · exact Real.arccos_nonneg x.1
        · exact Real.arccos_le_pi x.1
      ⟩
    continuous_toFun := by
      -- Continuity of `Subtype.val`, `Real.arccos`, and `φ`.
      sorry }
```

Important lemma:

```lean
lemma angleToSpace_at_cos
    (φ : AngleFun) {θ : ℝ} (hθ : θ ∈ AngleI) :
    angleToSpace φ ⟨Real.cos θ, by
      constructor
      · exact Real.neg_one_le_cos θ
      · exact Real.cos_le_one θ
    ⟩ = φ ⟨θ, hθ⟩ := by
  -- Use `Real.arccos_cos` under `0 ≤ θ ≤ π`.
  sorry
```

### 5.6 Cluster sets

```lean
def clusterSet (u : ℕ → ℝ) : Set ℝ :=
  { y | MapClusterPt y Filter.atTop u }
```

Useful lemmas:

```lean
lemma tendsto_atTop_cluster
    {u : ℕ → ℝ} {y : ℝ}
    (hu : Tendsto u atTop (nhds y)) :
    y ∈ clusterSet u := by
  exact Filter.Tendsto.mapClusterPt hu

lemma clusterSet_subset_of_eventually_mem_closed
    {u : ℕ → ℝ} {A : Set ℝ} (hA : IsClosed A)
    (hu : ∀ᶠ n in atTop, u n ∈ A) :
    clusterSet u ⊆ A := by
  intro y hy
  exact hA.mem_of_mapClusterPt hy hu
```

Mathlib has `MapClusterPt`, `mapClusterPt_iff_frequently`, `MapClusterPt.of_comp`, `Filter.Tendsto.mapClusterPt`, and `IsClosed.mem_of_mapClusterPt`.

## 6. Lemma dependency graph

The proof should be developed in this order:

```text
Basic node/trig lemmas
  ↓
Lagrange weight formula and rowEval/Lagrange bridge
  ↓
Off-point decay
  ↓
Good dyadic rows
  ↓
Primitive nodes and primitive occurrence lemmas
  ↓
Primitive mass lower bound
  ↓
Finite algebraic spike
  ↓
Continuous block spike
  ↓
Sequence in A with cluster set A
  ↓
Diagonal construction in angle variables
  ↓
Transfer back to f : [-1,1] → ℝ
```

A very effective iteration strategy is to first state the block spike lemma as a theorem with `sorry`, prove the final diagonal construction from it, and then work backwards to fill the spike lemma.

## 7. Lagrange weight formula

### Mathematical statement

For `0 < n`, `θ₀ ∈ [0,π]`, and `¬ IsNodeRow θ₀ n`,

```text
L_n f(cos θ₀)
  = ∑_{k=0}^{n-1}
      [ cos(nθ₀)/n * (-1)^k * sin θ_{k,n}/(cos θ₀ - cos θ_{k,n}) ]
      * φ(θ_{k,n}).
```

### Proof plan

1. Let `T_n` be the Chebyshev polynomial of the first kind.
2. The nodes `xnode n k` are the roots of `T_n`.
3. The Lagrange basis polynomial at `xnode n k` is

   ```text
   ℓ_{k,n}(t) = T_n(t) / (T'_n(xnode n k) * (t - xnode n k)).
   ```

4. Use the derivative identity

   ```text
   T'_n = n U_{n-1}.
   ```

   mathlib has `Polynomial.Chebyshev.T_derivative_eq_U`.

5. Use the trigonometric evaluation

   ```text
   U_{n-1}(cos θ_{k,n}) = sin(n θ_{k,n}) / sin θ_{k,n}
                         = (-1)^k / sin θ_{k,n}.
   ```

6. Use

   ```text
   T_n(cos θ₀) = cos(n θ₀).
   ```

7. Substitute into `ℓ_{k,n}(cos θ₀)`.

### Lean theorem skeletons

```lean
lemma chebyshev_T_eval_cos (n : ℕ) (θ : ℝ) :
    Polynomial.eval (Real.cos θ) (Polynomial.Chebyshev.T ℝ (n : ℤ)) =
      Real.cos ((n : ℝ) * θ) := by
  -- Check if this already exists in `Chebyshev.Basic`; if not, prove by induction.
  sorry

lemma chebyshev_U_eval_cos
    {n : ℕ} {θ : ℝ} (hθsin : Real.sin θ ≠ 0) :
    Polynomial.eval (Real.cos θ) (Polynomial.Chebyshev.U ℝ ((n : ℤ) - 1)) =
      Real.sin ((n : ℝ) * θ) / Real.sin θ := by
  -- Check existing trig Chebyshev lemmas first.
  sorry

lemma sin_n_θnode (n k : ℕ) (hn : 0 < n) (hk : k < n) :
    Real.sin ((n : ℝ) * θnode n k) = (-1 : ℝ) ^ k := by
  -- `n * ((2k+1)π/(2n)) = (2k+1)π/2`.
  -- Use `Real.sin_add_int_mul_two_pi`, or reduce to `sin (π/2 + kπ)`.
  sorry

lemma lagrange_basis_cheb_weight
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    {n k : ℕ} (hn : 0 < n) (hk : k < n)
    (hnot : ¬ IsNodeRow θ₀ n) :
    Polynomial.eval (Real.cos θ₀)
      (Lagrange.basis (Finset.range n) (xnode n) k) = λ θ₀ n k := by
  -- Use `Lagrange` barycentric/nodal lemmas if easier:
  -- `Lagrange.eval_interpolate_not_at_node` or `eval_interpolate_not_at_node'`.
  -- Otherwise prove basis formula directly from Chebyshev root polynomial.
  sorry

lemma chebLagEval_eq_weight_sum
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    (φ : AngleFun) {n : ℕ} (hn : 0 < n)
    (hnot : ¬ IsNodeRow θ₀ n) :
    chebLagEval (Real.cos θ₀) (angleToSpace φ) n =
      ∑ k in Finset.range n, λ θ₀ n k * φ.toRaw (θnode n k) := by
  sorry
```

### Important fallback

The Chebyshev/Lagrange bridge is intentionally postponed.  First formalise the
angle theorem using `F` as the definition of the row functional.  Then add the
bridge later.  This still gives a meaningful formal core of the submitted proof
and reduces the risk of spending the first sessions on polynomial API details.

## 8. Off-point decay

### Mathematical statement

If `g` is continuous on `[0,π]` and vanishes on a neighbourhood of `θ₀`, then

```text
rowEval θ₀ n g → 0.
```

In the note, for non-node rows,

```text
rowEval θ₀ n g
  = cos(nθ₀)/n * ∑_{k=0}^{n-1} (-1)^k H(θ_{k,n}),

H(θ) = g(θ) sin θ / (cos θ₀ - cos θ).
```

Because `g` vanishes near `θ₀`, `H` extends continuously across `θ₀`. Pair consecutive terms:

```text
|∑_{k=0}^{n-1} (-1)^k H(θ_{k,n})|
  ≤ (n/2) * ω_H(π/n) + ‖H‖∞,
```

so after dividing by `n`, this tends to zero.

### Lean-friendly formulation

Avoid defining a modulus of continuity explicitly. Prove an epsilon lemma from uniform continuity.

```lean
def VanishesNear (θ₀ : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ ε > 0, ∀ θ ∈ AngleI, |θ - θ₀| < ε → g θ = 0

lemma alternating_midpoint_average_tendsto_zero
    (H : AngleFun) :
    Tendsto
      (fun n : ℕ =>
        if hn : n = 0 then 0 else
          ((1 : ℝ) / n) *
            ∑ k in Finset.range n,
              ((-1 : ℝ) ^ k) * H.toRaw (θnode n k))
      atTop (nhds 0) := by
  -- Pair k=2r and k=2r+1.
  -- Use uniform continuity of `H` on compact `[0,π]`.
  -- Bound any leftover term by `‖H‖ / n`.
  sorry
```

Then:

```lean
lemma off_point_decay_raw
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g AngleI)
    (hg_vanish : VanishesNear θ₀ g) :
    Tendsto (fun n : ℕ => rowEval θ₀ n g) atTop (nhds 0) := by
  -- Node rows give `g θ₀ = 0` eventually/immediately because vanishing near θ₀.
  -- Non-node rows use the explicit H and `alternating_midpoint_average_tendsto_zero`.
  sorry

lemma off_point_decay
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    {φ : AngleFun}
    (hφ_vanish : VanishesNear θ₀ φ.toRaw) :
    Tendsto (fun n : ℕ => F θ₀ n φ) atTop (nhds 0) := by
  apply off_point_decay_raw hθ₀
  · -- continuity of `φ.toRaw` on `[0,π]`
    sorry
  · exact hφ_vanish
```

### Details for the alternating sum proof

For `n = 2q`, pair `k=2r` and `k=2r+1`:

```text
θ_{2r+1,n} - θ_{2r,n} = π/n.
```

For `n = 2q+1`, there is one leftover term. Bound it by `‖H‖∞`.

A useful auxiliary lemma:

```lean
lemma abs_alternating_midpoint_sum_le
    (H : AngleFun) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε)
    (hH : ∀ a ∈ AngleI, ∀ b ∈ AngleI,
       |a - b| ≤ Real.pi / n → |H.toRaw a - H.toRaw b| ≤ ε) :
    |∑ k in Finset.range n, ((-1 : ℝ)^k) * H.toRaw (θnode n k)|
      ≤ (n / 2 : ℕ) * ε + ‖H‖ := by
  sorry
```

It may be easier not to state this exact bound and instead prove the tendsto result directly.

## 9. Good dyadic rows

### Mathematical statement

For every `θ₀ ∈ [0,π]` and every odd positive integer `R`, there are arbitrarily large powers of two `n = 2^r` such that

```text
|cos(n θ₀)| ≥ κ(θ₀,R) > 0,
cos(n s θ₀) ≠ 0    for every odd s ≤ R.
```

The submitted proof actually gets `κ` depending only on `θ₀`, but dependence on `R` is harmless.

### Lean theorem skeleton

```lean
def IsPowTwo (n : ℕ) : Prop := ∃ r : ℕ, n = 2 ^ r

def GoodDyadicRow (θ₀ : ℝ) (R n : ℕ) : Prop :=
  IsPowTwo n ∧
  0 < n ∧
  Odd R ∧
  0 < R ∧
  (∃ κ > 0, |Real.cos ((n : ℝ) * θ₀)| ≥ κ) ∧
  (∀ s : ℕ, Odd s → s ≤ R → Real.cos ((n * s : ℕ : ℝ) * θ₀) ≠ 0)
```

For actual use, expose the lower bound as data:

```lean
structure GoodRowData (θ₀ : ℝ) (R n : ℕ) where
  pow_two : IsPowTwo n
  n_pos : 0 < n
  R_odd : Odd R
  R_pos : 0 < R
  kappa : ℝ
  kappa_pos : 0 < kappa
  cos_n_lower : kappa ≤ |Real.cos ((n : ℝ) * θ₀)|
  cos_ns_ne_zero : ∀ s : ℕ, Odd s → s ≤ R →
    Real.cos (((n * s : ℕ) : ℝ) * θ₀) ≠ 0
```

Existence lemma:

```lean
lemma exists_arbitrarily_large_good_dyadic
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI)
    (R : ℕ) (hRodd : Odd R) (hRpos : 0 < R) :
    ∃ κ > 0, ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ IsPowTwo n ∧ 0 < n ∧
      κ ≤ |Real.cos ((n : ℝ) * θ₀)| ∧
      ∀ s : ℕ, Odd s → s ≤ R →
        Real.cos (((n * s : ℕ) : ℝ) * θ₀) ≠ 0 := by
  sorry
```

### Proof details

Let `α = θ₀/π`.

#### Irrational case

If `α` is irrational, then `cos(n s θ₀) = 0` would imply

```text
n s α = m + 1/2,
```

hence `α` is rational. Contradiction.

For the lower bound: if `|cos(π y)| < 1/2`, then doubling moves `y` modulo `1` into a region where `|cos(2π y)| ≥ 1/2`. Thus at least one of every adjacent pair `r, r+1` has

```text
|cos(2^r θ₀)| ≥ 1/2.
```

So arbitrarily large powers of two work with `κ = 1/2`.

#### Rational case

Write `α = a/b` in lowest terms and `b = 2^h b₀` with `b₀` odd. For `r ≥ h`, the number `2^r s a / b` has odd denominator after reduction for each odd `s`, so it cannot be congruent to `1/2` modulo an integer. Therefore

```text
cos(2^r s θ₀) ≠ 0.
```

For `cos(2^r θ₀)`, the values are eventually periodic and none are zero, so their absolute values have a positive minimum. Use this as `κ`.

### Likely pain points

- Formal rational/irrational split for `θ₀ / π`.
- Modular arithmetic over `ℝ / ℤ`. It may be simpler to avoid quotient notation and work directly with integer equations using periodicity of `cos`.
- Extracting “odd denominator after reduction”. Search mathlib for rational denominator API before proving custom lemmas.

A possible simplification: state and prove a less pretty lemma using `∃ κ > 0, ∀ N, ∃ r ≥ N, ...` with powers `2^r` directly. This avoids a separate `IsPowTwo` predicate in the proof.

## 10. Primitive nodes

### Definitions

A primitive node of order `d` is

```text
θ = (2k+1)π/(2d),     gcd(2k+1,d)=1,     0 ≤ k < d.
```

Use index sets rather than finite sets of real angles when possible.

```lean
/-- Primitive numerator indices for order `d`. -/
def primIdx (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun k => Nat.Coprime (2 * k + 1) d)

lemma mem_primIdx_iff {d k : ℕ} :
    k ∈ primIdx d ↔ k < d ∧ Nat.Coprime (2 * k + 1) d := by
  simp [primIdx]

/-- Total variation of the primitive part of row `d`. -/
def Vprim (θ₀ : ℝ) (d : ℕ) : ℝ :=
  ∑ k in primIdx d, |λ θ₀ d k|
```

### Occurrence of primitive nodes in later rows

A primitive node of order `d` occurs in row `n` iff

```text
n = d * s
```

for some odd `s`. More precisely, if `θ = (2k+1)π/(2d)` with `gcd(2k+1,d)=1`, then it is a row-`n` node iff `d ∣ n` and `n/d` is odd.

Lean skeleton:

```lean
lemma primitive_node_occurs_iff
    {d k n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hk : k ∈ primIdx d) :
    (∃ l ∈ Finset.range n, θnode n l = θnode d k) ↔
      d ∣ n ∧ Odd (n / d) := by
  sorry
```

If `n = d*s` with `s` odd, the corresponding row-`n` index is

```text
l = ((2k+1)s - 1)/2.
```

You will need a lemma that this is `< n`.

### Weight transformation

If a primitive node of order `d` occurs in row `n = d*s`, with `s` odd, and neither row is a node row for `θ₀`, then

```text
λ_n(θ) = γ(n,d) λ_d(θ)

γ(n,d) = d/n * (-1)^((n/d - 1)/2) * cos(nθ₀)/cos(dθ₀).
```

With `n = d*s`:

```text
γ(d*s,d) = 1/s * χ(s) * cos(d*s*θ₀)/cos(d*θ₀),
χ(s) = (-1)^((s-1)/2).
```

Define:

```lean
def χ (s : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((s - 1) / 2)

def γ (θ₀ : ℝ) (n d : ℕ) : ℝ :=
  (d : ℝ) / (n : ℝ)
    * χ (n / d)
    * Real.cos ((n : ℝ) * θ₀) / Real.cos ((d : ℝ) * θ₀)
```

Skeleton:

```lean
lemma λ_occurs_eq_gamma_mul
    {θ₀ : ℝ} {d n k l : ℕ}
    (hd : 0 < d) (hn : 0 < n)
    (hk : k ∈ primIdx d)
    (hdiv : d ∣ n) (hodd : Odd (n / d))
    (hθ : θnode n l = θnode d k)
    (hnotn : ¬ IsNodeRow θ₀ n)
    (hnotd : ¬ IsNodeRow θ₀ d) :
    λ θ₀ n l = γ θ₀ n d * λ θ₀ d k := by
  -- Expand `λ`; same `sin θ` and denominator.
  -- The only changes are `cos(nθ₀)/n` vs `cos(dθ₀)/d` and sign.
  sorry
```

For row `n*u` and primitive order `n*s` with `s ∣ u`, the ratio becomes:

```text
γ(nu,ns) = s/u * χ(u/s) * cos(nu θ₀)/cos(ns θ₀).
```

This exact simplification is used in the Möbius cancellation.

## 11. Primitive mass lower bound

### Mathematical statement

For fixed `θ₀` and odd `R`, there is `c_R > 0` such that, for all sufficiently large powers of two `n` and every odd `s ≤ R` with `cos(ns θ₀) ≠ 0`,

```text
Vprim θ₀ (n*s) ≥ c_R * |cos(ns θ₀)| * log n.
```

Lean skeleton:

```lean
lemma primitive_mass_lower_bound
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI)
    (R : ℕ) (hRodd : Odd R) (hRpos : 0 < R) :
    ∃ cR > 0, ∃ N : ℕ, ∀ n s : ℕ,
      N ≤ n → IsPowTwo n → 0 < n →
      Odd s → s ≤ R →
      Real.cos (((n * s : ℕ) : ℝ) * θ₀) ≠ 0 →
      cR * |Real.cos (((n * s : ℕ) : ℝ) * θ₀)| * Real.log (n : ℝ)
        ≤ Vprim θ₀ (n * s) := by
  sorry
```

### Proof details

Let `d = n*s`. Since `n` is a power of two and `s` is odd, a row-`d` numerator `m = 2k+1` is primitive iff

```text
gcd(m,s)=1.
```

because `m` is odd and `n` is a power of two.

#### Interior case: `0 < θ₀ < π`

Choose a closed interval `J ⊂ (0,π)` centred at `θ₀`. On `J`, prove

```text
sin θ / |cos θ₀ - cos θ| ≥ c / |θ - θ₀|.
```

For primitive nodes in `J`, using `θ = mπ/(2d)`, obtain

```text
|λ_d(θ)|
  ≥ c * |cos(dθ₀)| / (d * |θ - θ₀|)
  ≍ c * |cos(dθ₀)| / |m - 2dθ₀/π|.
```

Now sum over odd `m` with `gcd(m,s)=1` and `|m - 2dθ₀/π| ≤ c_J d`.

Key elementary number-theory lemma:

```lean
lemma bounded_gaps_odd_coprime
    (R : ℕ) :
    ∃ G : ℕ, 0 < G ∧ ∀ s : ℕ, Odd s → s ≤ R →
      ∀ a : ℕ, ∃ m : ℕ,
        a ≤ m ∧ m ≤ a + G ∧ Odd m ∧ Nat.Coprime m s := by
  -- Since the allowed residues modulo `2*s` are periodic.
  -- Can take `G = 2 * R + 1` or `G = 2 * Nat.factorial R + 1`.
  -- Simpler proof: among `a, a+1, ..., a+2*s` there is an odd residue coprime to s.
  sorry
```

Then derive a harmonic lower bound:

```lean
lemma harmonic_lower_from_bounded_gaps
    {S : Set ℕ} {G : ℕ} (hG : 0 < G)
    (hgap : ∀ a, ∃ m ∈ S, a ≤ m ∧ m ≤ a + G)
    :
    -- Schematic: sum over S near a real center of 1 / distance ≥ c_G log N.
    sorry := by
  sorry
```

Do not try to make the first version maximally elegant. It is enough to get any positive constant depending on `R`.

#### Endpoint cases: `θ₀ = 0` or `θ₀ = π`

For `θ₀ = 0`, near zero:

```text
sin θ / (1 - cos θ) ≍ 1/θ.
```

At a node `θ = mπ/(2d)`, this gives

```text
|λ_d(θ)| ≳ |cos(dθ₀)| / m.
```

Sum over primitive odd `m ≤ c d`.

For `θ₀ = π`, use the symmetric variable `2d - m`.

### Suggested implementation shortcut

This is probably the most tedious estimate in the whole project. Isolate it aggressively. Use existential constants and avoid explicit best constants.

Prove a more general local estimate:

```lean
lemma local_kernel_lower_bound
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI) :
    ∃ c > 0, ∃ ρ > 0,
      ∀ θ ∈ AngleI,
        θ ≠ θ₀ → |θ - θ₀| < ρ →
        c / |θ - θ₀| ≤
          |Real.sin θ / (Real.cos θ₀ - Real.cos θ)| := by
  -- This handles interior and endpoints in one theorem if proved carefully.
  -- Otherwise split into three cases.
  sorry
```

Then primitive mass is mostly a counting/harmonic-sum theorem.

## 12. Finite algebraic spike

### Mathematical statement

Fix `θ₀` and odd `R`. Let `n` be a sufficiently large good dyadic row. For odd `s ≤ R`, define

```text
a_s = μ(s) χ(s) cos(ns θ₀) / (s cos(n θ₀)).
```

On primitive nodes of order `n*s`, set

```text
v(θ) = a_s / Vprim(θ₀,n*s) * sign(λ_{n*s}(θ)).
```

Set `v=0` at all other nodes in rows `1, ..., Rn`.

Then for every `1 ≤ j ≤ Rn`,

```text
rowEval θ₀ j v = 1    if j = n,
rowEval θ₀ j v = 0    if j ≠ n.
```

Moreover

```text
‖v‖∞ ≤ C_R / log n.
```

### Definitions

Möbius and character:

```lean
def μR (s : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius s : ℤ) : ℝ)

-- χ already defined as `(-1)^((s-1)/2)`.
```

Coefficient:

```lean
def spikeCoeff (θ₀ : ℝ) (n s : ℕ) : ℝ :=
  μR s * χ s * Real.cos (((n * s : ℕ) : ℝ) * θ₀)
    / ((s : ℝ) * Real.cos ((n : ℝ) * θ₀))
```

Sign helper. Check whether mathlib’s `Real.sign` has the right API. If not, define your own.

```lean
def rsign (x : ℝ) : ℝ :=
  if x < 0 then -1 else if x = 0 then 0 else 1

lemma mul_rsign_eq_abs (x : ℝ) : x * rsign x = |x| := by
  unfold rsign
  split_ifs with hneg hzero hpos <;> nlinarith [abs_of_neg hneg, abs_of_nonneg (le_of_not_gt hneg)]
```

Spike function as a raw function is awkward because it must identify whether a real angle is a primitive node of some order `n*s`. Prefer to define the finite spike through its values on row nodes first, then later build a continuous function matching those values.

One possible structure:

```lean
structure FiniteSpikeData (θ₀ : ℝ) (R n : ℕ) where
  val : ℝ → ℝ
  support_property : Prop
  early_rows : ∀ j : ℕ, 1 ≤ j → j ≤ R * n →
    rowEval θ₀ j val = (if j = n then 1 else 0)
  norm_bound : Prop
```

For a more proof-friendly definition, use finite index pairs:

```lean
/-- Odd `s ≤ R`. -/
def oddUpTo (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter Odd

/-- Indices `(s,k)` for primitive nodes of order `n*s`. -/
def spikeIdx (n R : ℕ) : Finset (ℕ × ℕ) :=
  (oddUpTo R).sigma (fun s => primIdx (n * s))
    |>.map
      { toFun := fun p => (p.1, p.2)
        inj' := by intro a b h; exact Sigma.ext_iff.mp h }
```

The exact syntax above may not work; the idea is to create a finite set of pairs `(s,k)` where `s` is odd and `k` indexes a primitive node of order `n*s`.

Then the value at that node is

```lean
def finiteSpikeValueAtPrimitive (θ₀ : ℝ) (n s k : ℕ) : ℝ :=
  spikeCoeff θ₀ n s / Vprim θ₀ (n * s) * rsign (λ θ₀ (n * s) k)
```

Finally define `v : ℝ → ℝ` by finite lookup:

```lean
def finiteSpikeRaw (θ₀ : ℝ) (R n : ℕ) : ℝ → ℝ :=
  fun θ =>
    ∑ p in spikeIdx n R,
      if θ = θnode (n * p.1) p.2 then
        finiteSpikeValueAtPrimitive θ₀ n p.1 p.2
      else 0
```

This sum definition avoids needing a decidable “find” function. You will need uniqueness lemmas showing at most one summand is nonzero.

### Möbius cancellation

Core algebra when `j = n*u`, `u` odd and `u ≤ R`:

```text
F_{nu} v = ∑_{s | u} γ(nu,ns) a_s.
```

For each divisor `s | u`,

```text
γ(nu,ns) a_s
  = χ(u) cos(nu θ₀) / (u cos(n θ₀)) * μ(s).
```

Therefore

```text
F_{nu} v
  = χ(u) cos(nu θ₀) / (u cos(n θ₀)) * ∑_{s|u} μ(s).
```

The divisor sum is `1` if `u=1` and `0` otherwise.

Lean lemma for Möbius sum:

```lean
lemma sum_moebius_divisors_real {u : ℕ} (hu : 0 < u) :
    (∑ s in Nat.divisors u, μR s) = (if u = 1 then 1 else 0) := by
  -- Use `ArithmeticFunction.coe_zeta_mul_coe_moebius` or
  -- `ArithmeticFunction.moebius_mul_coe_zeta` and unfold Dirichlet convolution.
  sorry
```

Then:

```lean
lemma finite_algebraic_spike
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI)
    (R : ℕ) (hRodd : Odd R) (hRpos : 0 < R) :
    ∃ C_R > 0, ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      -- good dyadic row hypotheses, including lower bound on `cos(nθ₀)`
      IsPowTwo n → 0 < n →
      (∀ s : ℕ, Odd s → s ≤ R →
        Real.cos (((n * s : ℕ) : ℝ) * θ₀) ≠ 0) →
      0 < |Real.cos ((n : ℝ) * θ₀)| →
      let v := finiteSpikeRaw θ₀ R n
      (∀ j : ℕ, 1 ≤ j → j ≤ R * n →
          rowEval θ₀ j v = (if j = n then 1 else 0)) ∧
      (∀ θ : ℝ, |v θ| ≤ C_R / Real.log (n : ℝ)) := by
  sorry
```

### Norm bound

Use primitive mass:

```text
Vprim(θ₀,n*s) ≥ c_R |cos(ns θ₀)| log n.
```

Also, from good rows,

```text
|cos(nθ₀)| ≥ κ > 0.
```

Thus

```text
|a_s| ≤ C * |cos(nsθ₀)| / s,
|a_s| / Vprim(θ₀,n*s) ≤ C_R / log n.
```

Since `R` is fixed, summing over possible duplicate lookup terms still only changes the constant by a factor depending on `R`.

## 13. Continuous block spike

### Mathematical statement

For fixed `θ₀`, there is a sequence `η_R → 0` over odd `R` such that: for each odd `R`, sufficiently large good dyadic `n`, and each `δ > 0`, there is `ψ ∈ C[0,π]` with

```text
(i)   ψ vanishes on a neighbourhood of θ₀,
(ii)  F_n ψ = 1,
(iii) F_j ψ = 0 for 1 ≤ j ≤ Rn, j ≠ n,
(iv)  |F_j ψ| ≤ η_R + δ for every j > Rn,
(v)   ‖ψ‖∞ ≤ C_R / log n.
```

The proof turns the finite spike `v` into a continuous tent function supported in tiny disjoint intervals around the finite primitive node set `P`.

### Use explicit tents

For a point `p`, radius `r > 0`, and height `a`, define

```lean
def tent (p r a : ℝ) : ℝ → ℝ :=
  fun θ => a * max 0 (1 - |θ - p| / r)
```

Prove:

```lean
lemma continuous_tent {p r a : ℝ} : Continuous (tent p r a) := by
  sorry

lemma tent_apply_center {p r a : ℝ} (hr : r ≠ 0) :
    tent p r a p = a := by
  simp [tent, hr]

lemma tent_eq_zero_of_radius_le {p r a θ : ℝ} (hr : 0 < r)
    (h : r ≤ |θ - p|) :
    tent p r a θ = 0 := by
  sorry
```

Then define the continuous spike as a finite sum of tents:

```lean
def continuousSpikeRaw
    (P : Finset ℝ) (radius : ℝ → ℝ) (height : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => ∑ p in P, tent p (radius p) (height p) θ
```

Package as `AngleFun` by restricting to `[0,π]`.

### Choosing radii

Let `P` be the finite set where the finite spike is nonzero. It is disjoint from `θ₀`. Define

```text
ρ = dist(P, θ₀) > 0.
```

In Lean, avoid an actual `dist(P,θ₀)` definition. Prove an existence lemma:

```lean
lemma finite_set_positive_separation
    {P : Finset ℝ} {θ₀ : ℝ}
    (hdisj : ∀ p ∈ P, p ≠ θ₀) :
    ∃ ρ > 0, ∀ p ∈ P, ρ ≤ |p - θ₀| := by
  -- Use finite minimum of positive distances.
  sorry
```

Choose radii around each `p ∈ P` such that:

1. intervals are pairwise disjoint;
2. no interval contains `θ₀`;
3. intervals contain no row-`j` nodes for `j ≤ K` except the intended exact atom in `P`;
4. total interval length is very small.

A robust existential lemma:

```lean
lemma choose_tent_radii
    {P E : Finset ℝ} {θ₀ : ℝ}
    (hPdisj : ∀ p ∈ P, p ≠ θ₀)
    (hPE : ∀ p ∈ P, p ∈ E)
    : ∀ ε > 0,
      ∃ rad : ℝ → ℝ,
        (∀ p ∈ P, 0 < rad p) ∧
        (∀ p ∈ P, rad p ≤ ε) ∧
        -- disjoint closed intervals around distinct P-points
        (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
          Disjoint (Set.Icc (p - rad p) (p + rad p))
                   (Set.Icc (q - rad q) (q + rad q))) ∧
        -- no θ₀ in intervals
        (∀ p ∈ P, θ₀ ∉ Set.Icc (p - rad p) (p + rad p)) ∧
        -- no unwanted E-points in intervals
        (∀ p ∈ P, ∀ e ∈ E, e ≠ p →
          e ∉ Set.Icc (p - rad p) (p + rad p)) := by
  -- Since `P ∪ E ∪ {θ₀}` is finite, take radii smaller than half the minimum
  -- positive distance between distinct relevant points, and smaller than ε.
  sorry
```

Here `E` should be the finite set of all nodes in rows `1,...,K`.

```lean
def nodesUpTo (K : ℕ) : Finset ℝ :=
  (Finset.Icc 1 K).bind (fun j =>
    (Finset.range j).image (fun k => θnode j k))
```

### Future-row estimates

For rows `j > Rn`, split row nodes in the support into:

1. exact atoms, i.e. row-`j` nodes equal to points in `P`;
2. non-exact nodes lying inside the small intervals.

#### Exact atoms

If `j = n*u` with `u > R` odd, exact atoms contribute

```text
∑_{s | u, s ≤ R} γ(nu,ns) a_s.
```

Using the same calculation as before:

```text
= χ(u) cos(nuθ₀)/(u cos(nθ₀)) * ∑_{s|u, s≤R} μ(s).
```

Since `∑_{s|u} μ(s)=0` for `u>1`, this is

```text
-χ(u) cos(nuθ₀)/(u cos(nθ₀)) * ∑_{s|u, s>R} μ(s).
```

Bound:

```text
≤ C * τ(u) / u ≤ C / sqrt(R).
```

The divisor bound can be very crude. Prove:

```lean
lemma card_divisors_le_two_mul_sqrt (u : ℕ) :
    (Nat.divisors u).card ≤ 2 * Nat.sqrt u + 1 := by
  sorry
```

or any weaker bound implying `τ(u)/u ≤ C/sqrt(R)` for `u > R`.

A simple theorem sufficient for the proof:

```lean
lemma divisor_count_over_u_bound {R u : ℕ} (hRu : R < u) :
    ((Nat.divisors u).card : ℝ) / (u : ℝ) ≤ 3 / Real.sqrt (R : ℝ) := by
  -- Pair divisors d ≤ sqrt u and u/d ≥ sqrt u.
  sorry
```

Then set

```text
η_R = C / sqrt(R).
```

Formal statement:

```lean
def eta (C : ℝ) (R : ℕ) : ℝ := C / Real.sqrt (R : ℝ)

lemma eta_tendsto_zero (C : ℝ) :
    Tendsto (fun R : ℕ => eta C R) atTop (nhds 0) := by
  sorry
```

#### Non-exact nodes

If support intervals are at distance at least `ρ/2` from `θ₀`, then for all non-node rows:

```text
|λ_{k,j}| ≤ C / (j ρ)
```

Do this by compactness rather than explicit trig estimates:

```lean
lemma kernel_bound_away_from θ₀ hθ₀ ρ hρ :
    ∃ C > 0, ∀ θ ∈ AngleI,
      ρ ≤ |θ - θ₀| →
      |Real.sin θ / (Real.cos θ₀ - Real.cos θ)| ≤ C := by
  -- The function is continuous on the compact closed set where `ρ ≤ |θ-θ₀|`.
  -- Denominator is nonzero there.
  sorry
```

Then:

```lean
lemma lambda_bound_away
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C > 0, ∀ j k : ℕ,
      0 < j → k < j →
      ρ ≤ |θnode j k - θ₀| →
      |λ θ₀ j k| ≤ C / (j : ℝ) := by
  sorry
```

Count grid points in intervals:

```lean
lemma row_grid_count_in_intervals
    (intervals : Finset (ℝ × ℝ)) -- endpoints or center/radius representation
    (j : ℕ) :
    -- Number of row-j nodes in union of intervals ≤ C * (j * totalLength + numberIntervals).
    sorry := by
  sorry
```

For intervals centred at `P` with radii `rad p`, the total length is

```text
|I| = ∑_{p∈P} 2 rad p.
```

The non-exact contribution is bounded by

```text
C * ‖v‖∞ * ( |I|/ρ + |P|/(jρ) ).
```

The proof chooses `K > Rn` so large that

```text
‖v‖∞ |P| / (K ρ) < δ/4,
```

then chooses the intervals with total length so small that

```text
C ‖v‖∞ |I| / ρ < δ/4.
```

For `j > K`, this makes non-exact contribution `< δ`.

### Block spike theorem skeleton

```lean
structure BlockSpike
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI)
    (R n : ℕ) (η δ : ℝ) where
  ψ : AngleFun
  vanishes : VanishesNear θ₀ ψ.toRaw
  hit : F θ₀ n ψ = 1
  early_zero : ∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F θ₀ j ψ = 0
  future_small : ∀ j : ℕ, R * n < j → |F θ₀ j ψ| ≤ η + δ
  norm_small : Prop -- e.g. ‖ψ‖ ≤ C_R / log n

lemma exists_block_spike
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI) :
    ∃ η : ℕ → ℝ,
      Tendsto η atTop (nhds 0) ∧
      ∀ R : ℕ, Odd R → 0 < R →
        ∃ C_R > 0, ∃ N : ℕ, ∀ n : ℕ,
          N ≤ n →
          -- good dyadic hypotheses for this R
          IsPowTwo n → 0 < n →
          (∀ s : ℕ, Odd s → s ≤ R →
            Real.cos (((n * s : ℕ) : ℝ) * θ₀) ≠ 0) →
          0 < |Real.cos ((n : ℝ) * θ₀)| →
          ∀ δ > 0,
            ∃ ψ : AngleFun,
              VanishesNear θ₀ ψ.toRaw ∧
              F θ₀ n ψ = 1 ∧
              (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F θ₀ j ψ = 0) ∧
              (∀ j : ℕ, R * n < j → |F θ₀ j ψ| ≤ η R + δ) ∧
              ‖ψ‖ ≤ C_R / Real.log (n : ℝ) := by
  sorry
```

This theorem is the main bottleneck.

## 14. Constructing a sequence in `A` with cluster set exactly `A`

The note says “concatenate finite `1/r`-nets of `A`.” In Lean, the most convenient method may be separability.

Because `A ⊆ [-1,1]`, `A` as a subtype is compact, hence separable. But in `ℝ`, separability is already available. Mathlib has:

```lean
TopologicalSpace.exists_dense_seq
TopologicalSpace.denseSeq
TopologicalSpace.denseRange_denseSeq
```

For nonempty `A`, define the subtype:

```lean
abbrev ASubtype (A : Set ℝ) := {x : ℝ // x ∈ A}
```

Assuming `[TopologicalSpace.SeparableSpace (ASubtype A)]` and `[Nonempty (ASubtype A)]`, get a dense sequence:

```lean
let d : ℕ → ASubtype A := TopologicalSpace.denseSeq (ASubtype A)
```

Now repeat each dense point infinitely often. For example:

```lean
def repeatedDenseSeq (d : ℕ → ℝ) : ℕ → ℝ :=
  fun n => d (Nat.unpair n).1
```

Each `d i` appears infinitely often along `n = Nat.pair i t`.

The cluster set of `repeatedDenseSeq d` is the closure of `range d`. If `range d` is dense in `A` and all values lie in closed `A`, then the cluster set is exactly `A`.

The theorem to prove:

```lean
lemma exists_seq_clusterSet_eq_closed_nonempty
    {A : Set ℝ} (hA_closed : IsClosed A) (hA_nonempty : A.Nonempty) :
    ∃ a : ℕ → ℝ,
      (∀ m, a m ∈ A) ∧ clusterSet a = A := by
  -- Use dense sequence in subtype A, repeated infinitely often.
  sorry
```

Since the final theorem assumes `A ⊆ [-1,1]`, also get boundedness. Rather than prove a general bound, simply use:

```lean
lemma A_bound_with_c
    {A : Set ℝ} (hA_subset : A ⊆ SpaceI) {c : ℝ} (hc : c ∈ A) :
    ∀ a ∈ A, |a - c| ≤ 2 := by
  intro a ha
  have haI := hA_subset ha
  have hcI := hA_subset hc
  -- interval arithmetic
  nlinarith [haI.1, haI.2, hcI.1, hcI.2, abs_sub_le_iff.mp ?]
  sorry
```

Simpler: in the final construction take `B = 3`, and prove `|a - c| ≤ B` by interval arithmetic.

## 15. Diagonal construction in angle variables

### The angle theorem

State the main theorem in angle variables first.

```lean
theorem angle_theorem_nonempty
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ φ : AngleFun,
      clusterSet (fun m : ℕ => F θ₀ (m.succ) φ) = A := by
  sorry
```

### Data choices

1. Choose `c ∈ A`.
2. Choose `a : ℕ → ℝ` with `∀m, a m ∈ A` and `clusterSet a = A`.
3. Let `B = 3`, so `|a_m - c| ≤ B` for all `m`.
4. From `exists_block_spike`, get `η : ℕ → ℝ` with `η R → 0`.
5. Choose odd integers `R_m → ∞` and positive `δ_m` so that

   ```text
   ε_m := η(R_m) + δ_m
   ∑ ε_m < 1/8.
   ```

Lean-friendly explicit bound:

```text
ε_m ≤ 2^(-(m+5)).
```

Since `η R → 0`, choose odd `R_m ≥ 3` so that

```text
η(R_m) ≤ 2^(-(m+6)).
```

Then choose

```text
δ_m = 2^(-(m+6)).
```

Hence `ε_m ≤ 2^(-(m+5))`, and the sum is at most `1/16 < 1/8` if indexing starts at `0`.

If proving summability of these explicit powers is annoying, choose any summable positive sequence `epsTarget m`, e.g. `(1/16) * (1/2)^m`, and use standard `Summable` lemmas.

### Choosing rows and spikes

Choose recursively good dyadic rows `n_m` and block spikes `ψ_m` such that:

```text
n_m > R_i n_i      for all i < m,
‖ψ_m‖∞ ≤ 2^{-m}/(4B),
F_{n_m} ψ_m = 1,
F_j ψ_m = 0 for j ≤ R_m n_m, j ≠ n_m,
|F_j ψ_m| ≤ ε_m for j > R_m n_m,
ψ_m vanishes near θ₀.
```

The norm condition is possible because block spike gives

```text
‖ψ_m‖∞ ≤ C_{R_m}/log n_m,
```

and good dyadic rows are arbitrarily large.

Lean construction suggestion:

- First prove an existence lemma for the entire sequences `(n_m, ψ_m)` using dependent choice or recursive `Classical.choose`.
- Keep the resulting properties in named lemmas:

```lean
lemma n_strictMono : StrictMono nSeq := ...
lemma n_tendsto_atTop : Tendsto nSeq atTop atTop := n_strictMono.tendsto_atTop
lemma n_separated : ∀ i m, i < m → RSeq i * nSeq i < nSeq m := ...
lemma ψ_hit : ∀ m, F θ₀ (nSeq m) (ψSeq m) = 1 := ...
lemma ψ_early_zero : ... := ...
lemma ψ_future_small : ... := ...
lemma ψ_norm_small : ∀ m, ‖ψSeq m‖ ≤ 2^(-(m+something)) := ...
lemma ψ_vanishes : ∀ m, VanishesNear θ₀ (ψSeq m).toRaw := ...
```

### Coefficients

Define coefficients recursively:

```text
b_m = a_m - c - ∑_{i<m} b_i F_{n_m} ψ_i.
```

Lean:

```lean
def bSeq (a : ℕ → ℝ) (c : ℝ) (nSeq : ℕ → ℕ) (ψSeq : ℕ → AngleFun) : ℕ → ℝ :=
  Nat.rec
    (a 0 - c)
    (fun m bPrev =>
      -- This simple Nat.rec only gives previous value, not all previous values.
      -- Better use well-founded recursion or define by `WellFounded.fix`.
      sorry)
```

Better: define using `Nat.strongRec` or `WellFounded.fix`:

```lean
def bSeq : ℕ → ℝ :=
  fun m =>
    a m - c - ∑ i in Finset.range m, bSeq i * F θ₀ (nSeq m) (ψSeq i)
```

Lean will not accept this direct recursive definition. Use:

```lean
def bSeq : ℕ → ℝ
  | m =>
    a m - c - ∑ i in Finset.range m, bSeq i * F θ₀ (nSeq m) (ψSeq i)
termination_by m => m
```

This should work because recursive calls are on `i < m`; you may need `decreasing_by` using `Finset.mem_range.mp`.

Bound:

```lean
lemma bSeq_bound (m : ℕ) : |bSeq m| ≤ 2 * B := by
  -- Strong induction.
  -- |b_m| ≤ |a_m-c| + ∑_{i<m} |b_i| |F_{n_m} ψ_i|
  -- For i<m, n_m > R_i n_i, so future_small for ψ_i gives ≤ ε_i.
  -- Then ≤ B + 2B * ∑_{i<m} ε_i < 2B.
  sorry
```

### Define the function

Use the summable series in `AngleFun`:

```lean
def φ : AngleFun :=
  ContinuousMap.const AngleI c + ∑' m : ℕ, (bSeq m) • ψSeq m
```

Need prove summability:

```lean
lemma summable_spikes : Summable (fun m : ℕ => (bSeq m) • ψSeq m) := by
  -- Norm bound: ‖b_m • ψ_m‖ ≤ (2B) * 2^{-m}/(4B) = 2^{-m}/2.
  -- Compare to geometric summable sequence.
  sorry
```

Then row evaluation commutes with the infinite sum:

```lean
lemma F_φ_eq_tsum (j : ℕ) :
    F θ₀ j φ = c + ∑' m : ℕ, bSeq m * F θ₀ j (ψSeq m) := by
  -- Use `FCLM θ₀ hθ₀ j` and `ContinuousLinearMap.map_tsum`.
  sorry
```

For the constant term, prove:

```lean
lemma F_const_one (j : ℕ) (hj : 0 < j) :
    F θ₀ j (ContinuousMap.const AngleI (1 : ℝ)) = 1 := by
  -- Interpolation of constant function is constant.
  -- For explicit rowEval: in node case immediate; in non-node case sum of Lagrange basis weights = 1.
  -- Easier after Lagrange bridge using `Lagrange.interpolate_one`.
  sorry

lemma F_const (j : ℕ) (hj : 0 < j) :
    F θ₀ j (ContinuousMap.const AngleI c) = c := by
  -- linearity from `FCLM` and `F_const_one`.
  sorry
```

In the submitted proof, the constant term is simply `c`. If proving `F_const` via explicit weights is annoying, use the Lagrange bridge and mathlib’s `Lagrange.interpolate_one`.

### Selected rows

At selected row `n_m`:

- Future spikes `i > m` vanish exactly because `n_m < n_i ≤ R_i n_i` and `n_m ≠ n_i`.
- Current spike gives `1`.
- Earlier spikes are corrected by the definition of `b_m`.

Formal lemma:

```lean
lemma F_selected_row (m : ℕ) :
    F θ₀ (nSeq m) φ = a m := by
  rw [F_φ_eq_tsum]
  -- Split tsum into i<m, i=m, i>m.
  -- Use future exact zeros for i>m.
  -- Use hit for i=m.
  -- Use definition of bSeq m.
  sorry
```

To split a `tsum`, it may be easier to prove the sequence has finite support after `m` for the selected row:

```lean
have h_tail_zero : ∀ i > m, bSeq i * F θ₀ (nSeq m) (ψSeq i) = 0 := ...
```

Then use a lemma like:

```lean
tsum_eq_sum_of_support_subset
```

or prove by `Summable.hasSum` plus finite sum manipulation.

### Non-selected rows tend to `c`

Let `Selected := Set.range nSeq`. Along rows not in `Selected`, prove

```text
F_n φ → c.
```

For fixed `M`, split:

```text
F_n φ - c = ∑_{m≤M} b_m F_n ψ_m + ∑_{m>M} b_m F_n ψ_m.
```

- Finite part tends to `0` by off-point decay because each `ψ_m` vanishes near `θ₀`.
- Tail is uniformly bounded by

  ```text
  2B ∑_{m>M} ε_m.
  ```

For non-selected `n`, if `n ≤ R_m n_m`, then exact early-zero applies; if `n > R_m n_m`, future-small applies.

Skeleton:

```lean
def Selected (nSeq : ℕ → ℕ) : Set ℕ := Set.range nSeq

lemma tendsto_nonselected_to_c :
    Tendsto
      (fun n : ℕ => F θ₀ n φ)
      (atTop ⊓ Filter.principal (Selected nSeq)ᶜ)
      (nhds c) := by
  -- epsilon proof with finite/tail split.
  sorry
```

### Cluster-set equality

The full sequence has:

```text
u(n_m) = a_m,
```

and nonselected rows tend to `c ∈ A`.

A reusable lemma:

```lean
lemma clusterSet_of_selected_rows_and_complement_tendsto
    {u a : ℕ → ℝ} {nSeq : ℕ → ℕ} {A : Set ℝ} {c : ℝ}
    (hn_strict : StrictMono nSeq)
    (hu_selected : ∀ m, u (nSeq m) = a m)
    (ha_cluster : clusterSet a = A)
    (hcA : c ∈ A)
    (hcomp : Tendsto u (atTop ⊓ Filter.principal (Set.range nSeq)ᶜ) (nhds c)) :
    clusterSet u = A := by
  -- Prove both inclusions.
  -- Inclusion A ⊆ clusterSet u:
  --   if y clusters along a, then y clusters along u ∘ nSeq; since nSeq tends to atTop,
  --   use `MapClusterPt.of_comp` to get y clusters along u.
  -- Inclusion clusterSet u ⊆ A:
  --   split cluster points along selected/complement filters.
  --   selected part corresponds to `a`; complement part tends to c.
  sorry
```

For the second inclusion, there are two possible approaches:

1. **Filter split:** use that `atTop` is the sup/join of its restrictions to `Selected` and `Selectedᶜ`, then use `clusterPt_sup`.
2. **Subsequence split:** use `MapClusterPt.tendsto_subseq` in first-countable spaces, then extract a subsequence that is eventually/infrequently selected or nonselected.

The filter split is probably shorter once the filter lemmas are found.

## 16. Transfer to the original theorem

Once `angle_theorem_nonempty` is proved:

1. Given `x₀ ∈ [-1,1]`, set

   ```lean
   θ₀ := Real.arccos x₀
   ```

2. Prove `θ₀ ∈ AngleI`.
3. Get `φ : AngleFun` from the angle theorem.
4. Define `f := angleToSpace φ`.
5. Use `Real.cos_arccos` to show `x₀ = cos θ₀`.
6. Use `chebLagEval_eq_F` pointwise to transfer cluster sets.

Skeleton:

```lean
theorem erdos1151_nonempty_fixed_point
    {x₀ : ℝ} (hx₀ : x₀ ∈ SpaceI)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ f : SpaceFun,
      clusterSet (fun m : ℕ => chebLagEval x₀ f (m.succ)) = A := by
  let θ₀ := Real.arccos x₀
  have hθ₀ : θ₀ ∈ AngleI := by
    constructor
    · exact Real.arccos_nonneg x₀
    · exact Real.arccos_le_pi x₀
  obtain ⟨φ, hφ⟩ := angle_theorem_nonempty hθ₀ hA_closed hA_nonempty hA_subset
  refine ⟨angleToSpace φ, ?_⟩
  have hxcos : Real.cos θ₀ = x₀ := by
    -- `Real.cos_arccos` needs `x₀ ∈ [-1,1]` or `|x₀| ≤ 1`.
    exact Real.cos_arccos x₀
  -- Show the two sequences are pointwise equal, then rewrite clusterSet.
  apply Set.ext
  intro y
  simp [clusterSet]
  -- use eventual/pointwise equality:
  -- `chebLagEval x₀ (angleToSpace φ) (m.succ) = F θ₀ (m.succ) φ`
  sorry
```

## 17. Detailed theorem list for implementation

Here is a proposed theorem bank. Add these names as stubs first, then fill them in roughly in order.

### Basic/trig

```lean
lemma θnode_mem_Icc ...
lemma xnode_mem_Icc ...
lemma xnode_injOn_range ...
lemma isNodeRow_iff_exists_node ...
lemma chebyshev_T_eval_cos ...
lemma chebyshev_U_eval_cos ...
lemma sin_n_θnode ...
lemma cos_n_θnode_eq_zero ...
```

### Lagrange bridge

```lean
lemma lagrange_basis_cheb_weight ...
lemma chebLagEval_at_node ...
lemma chebLagEval_eq_weight_sum ...
lemma F_const ...
lemma chebLagEval_eq_F ...
```

### Off-point decay

```lean
lemma alternating_midpoint_average_tendsto_zero ...
lemma off_point_decay_raw ...
lemma off_point_decay ...
```

### Good rows

```lean
lemma cos_mul_eq_zero_implies_rational_angle ...
lemma exists_arbitrarily_large_good_dyadic ...
```

### Primitive rows

```lean
lemma mem_primIdx_iff ...
lemma primitive_node_occurs_iff ...
lemma λ_occurs_eq_gamma_mul ...
lemma Vprim_pos_of_cos_ne_zero ...
lemma primitive_mass_lower_bound ...
```

### Möbius algebraic spike

```lean
lemma χ_mul_of_odd ...
lemma sum_moebius_divisors_real ...
lemma finite_spike_row_eval_eq_divisor_sum ...
lemma finite_algebraic_spike ...
```

### Continuous block spike

```lean
lemma continuous_tent ...
lemma tent_apply_center ...
lemma tent_eq_zero_of_radius_le ...
lemma finite_set_positive_separation ...
lemma choose_tent_radii ...
lemma kernel_bound_away_from ...
lemma lambda_bound_away ...
lemma row_grid_count_in_intervals ...
lemma divisor_count_over_u_bound ...
lemma eta_tendsto_zero ...
lemma exists_block_spike ...
```

### Cluster/sequence construction

```lean
lemma exists_seq_clusterSet_eq_closed_nonempty ...
lemma choose_R_delta_summable ...
lemma choose_rows_and_spikes ...
lemma bSeq_bound ...
lemma summable_spikes ...
lemma F_selected_row ...
lemma tendsto_nonselected_to_c ...
lemma clusterSet_of_selected_rows_and_complement_tendsto ...
lemma angle_theorem_nonempty ...
```

### Main theorem

```lean
lemma angleToSpace_at_cos ...
theorem erdos1151_nonempty_fixed_point ...
```

## 18. Risk assessment and mitigation

### Highest-risk lemmas

1. `primitive_mass_lower_bound`
2. `exists_block_spike`
3. `chebLagEval_eq_F`

### Medium-risk lemmas

1. `exists_arbitrarily_large_good_dyadic`
2. `clusterSet_of_selected_rows_and_complement_tendsto`
3. `row_grid_count_in_intervals`
4. `choose_rows_and_spikes`

### Lower-risk lemmas

1. `exists_seq_clusterSet_eq_closed_nonempty`
2. `off_point_decay`
3. `sum_moebius_divisors_real`
4. `summable_spikes`

### Mitigation plan

First prove the final construction from an abstract block-spike hypothesis. That gives a useful compiled theorem independent of the hardest estimates. This is now the recommended first major milestone, not merely a mitigation fallback.

Suggested intermediate theorem:

```lean
/-- Abstract diagonal theorem: if suitable block spikes exist, every nonempty closed
    `A ⊆ [-1,1]` is a cluster set. -/
theorem angle_theorem_from_block_spikes
    (block_spikes : AbstractBlockSpikeHypothesis θ₀)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ φ : AngleFun,
      clusterSet (fun m : ℕ => F θ₀ (m.succ) φ) = A := by
  sorry
```

Then formalise `AbstractBlockSpikeHypothesis` from the actual primitive-row construction.

## 19. Common Lean pitfalls

### Indexing

The note uses `1 ≤ k ≤ n`; this brief uses `0 ≤ k < n`.

Conversion:

```text
note k_note = k_lean + 1
θ_{k_note,n} = (2 k_note - 1)π/(2n)
             = (2 k_lean + 1)π/(2n).
```

The sign becomes `(-1)^k_lean`.

### Positive rows

Most formulas require `0 < n`. The final sequence should use `m.succ`. Keep `n=0` branches arbitrary and prove all important lemmas with `0 < n`.

### Coercions

Expect many goals involving `(n : ℝ)`, `(n * s : ℕ : ℝ)`, and `((n : ℝ) * (s : ℝ))`. Add local simp lemmas where safe:

```lean
norm_num
ring_nf
field_simp [Nat.cast_ne_zero.mpr hn.ne']
```

### `log n`

Use `Real.log_pos` only after proving `1 < (n : ℝ)`. Since good rows are arbitrarily large, require `N ≥ 2` before using norm bounds.

### Sign function

Do not fight `Real.sign` if its API is inconvenient. Define a local `rsign` and prove only the two lemmas needed:

```lean
x * rsign x = |x|
|rsign x| ≤ 1
```

### Finite real sets

Avoid comparing real angles by computation. Use finite sets and existential separation lemmas. If necessary, keep duplicate-free facts as explicit hypotheses in local construction lemmas.

### Continuous maps and `tsum`

It is worth defining `FCLM`; without a continuous linear map, interchanging `F` with an infinite sum will be painful.

### Use `Classical`

This project is nonconstructive. Use:

```lean
open Classical
attribute [local instance] Classical.decEq
```

or simply rely on `classical` inside proofs. This is not an unproved axiom in the project-specific sense; it is standard Lean/mathlib classical reasoning.

## 20. Suggested initial coding sequence

1. Create `Basic.lean` with intervals, nodes, `clusterSet`, `rowEval`, `F`, and a temporary placeholder for `chebLagEval`.
2. Create `Abstract.lean` with `AbstractBlockSpikeHypothesis`.
3. Prove `angle_theorem_from_block_spikes` from the abstract interface.  Use `sorry` only inside the theorem while building the proof skeleton; avoid adding project-specific axioms.
4. Fill `exists_seq_clusterSet_eq_closed_nonempty`.
5. Fill the cluster merge lemma.
6. Fill summability and continuous linear map/t-sum manipulation, including `FCLM`.
7. Prove off-point decay for `F`.
8. Prove the constant-row lemma `F θ₀ n (const c) = c` for `0 < n`.
9. Prove finite algebraic spike assuming primitive mass.
10. Prove continuous block spike assuming finite algebraic spike and the counting estimates.
11. Prove primitive mass, using existential constants rather than sharp bounds.
12. Prove good dyadic rows.
13. Replace the temporary `chebLagEval` placeholder with the real Lagrange interpolation definition.
14. Prove the Lagrange/Chebyshev bridge and transfer to the final statement.

This order gives useful compilation checkpoints and avoids getting stuck at the hardest analytic estimate before the final construction is tested.

## 21. Abstract block-spike interface

This is the interface I recommend using while developing the final construction.

```lean
structure AbstractBlockSpikeHypothesis
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI) where
  /-- Constant functions are fixed by positive rows. -/
  const_eval : ∀ c : ℝ, ∀ n : ℕ, 0 < n →
    F θ₀ n (ContinuousMap.const AngleI c) = c

  /-- The off-point decay lemma needed for finite sums of old spikes. -/
  off_point_decay : ∀ ψ : AngleFun,
    VanishesNear θ₀ ψ.toRaw →
      Tendsto (fun n : ℕ => F θ₀ n ψ) atTop (nhds 0)

  η : ℕ → ℝ
  η_nonneg : ∀ R, 0 ≤ η R
  η_tendsto_zero : Tendsto η atTop (nhds 0)

  /-- For every odd `R`, arbitrarily large selected rows admit block spikes. -/
  exists_spike :
    ∀ R : ℕ, Odd R → 3 ≤ R →
      ∃ C_R > 0, ∀ N : ℕ, ∀ δ > 0, ∃ n : ℕ, ∃ ψ : AngleFun,
        N ≤ n ∧
        0 < n ∧
        VanishesNear θ₀ ψ.toRaw ∧
        F θ₀ n ψ = 1 ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F θ₀ j ψ = 0) ∧
        (∀ j : ℕ, R * n < j → |F θ₀ j ψ| ≤ η R + δ) ∧
        ‖ψ‖ ≤ C_R / Real.log (n : ℝ)
```

This interface hides all dyadic/primitive details. The real block-spike theorem should imply this by choosing `n` to be a sufficiently large good dyadic row.

Then the diagonal theorem becomes much cleaner:

```lean
theorem angle_theorem_from_block_spikes
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ AngleI)
    (H : AbstractBlockSpikeHypothesis θ₀ hθ₀)
    {A : Set ℝ} (hA_closed : IsClosed A)
    (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ φ : AngleFun,
      clusterSet (fun m : ℕ => F θ₀ (m.succ) φ) = A := by
  sorry
```

This theorem should be the first major target.

## 22. How the real block-spike theorem should imply the abstract interface

The concrete theorem will likely look like:

```lean
theorem concrete_block_spike
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI) :
    ∃ η : ℕ → ℝ,
      (∀ R, 0 ≤ η R) ∧
      Tendsto η atTop (nhds 0) ∧
      ∀ R : ℕ, Odd R → 3 ≤ R →
        ∃ C_R > 0, ∃ N₀ : ℕ, ∀ n : ℕ,
          N₀ ≤ n → GoodConcreteRow θ₀ R n →
          ∀ δ > 0, ∃ ψ : AngleFun,
            VanishesNear θ₀ ψ.toRaw ∧
            F θ₀ n ψ = 1 ∧
            (∀ j : ℕ, 1 ≤ j → j ≤ R * n → j ≠ n → F θ₀ j ψ = 0) ∧
            (∀ j : ℕ, R * n < j → |F θ₀ j ψ| ≤ η R + δ) ∧
            ‖ψ‖ ≤ C_R / Real.log (n : ℝ) := by
  sorry
```

Together with:

```lean
lemma exists_good_concrete_row_arbitrarily_large
    (θ₀ : ℝ) (hθ₀ : θ₀ ∈ AngleI)
    (R : ℕ) (hRodd : Odd R) (hR : 3 ≤ R) :
    ∀ N, ∃ n, N ≤ n ∧ GoodConcreteRow θ₀ R n := by
  sorry
```

Then construct `AbstractBlockSpikeHypothesis`.

## 23. Final sanity checks

Before declaring success, verify these statements compile with no project-specific axioms:

```lean
#print axioms erdos1151_nonempty_fixed_point
```

Expected axioms are the ordinary Lean/mathlib background axioms such as choice/propext/quot.sound, depending on imports. There should be no custom `axiom`, no `unsafe`, and no remaining `sorry`.

Also test a few simplification lemmas:

```lean
#check Lagrange.interpolate
#check Lagrange.eval_interpolate_at_node
#check Lagrange.eval_interpolate_not_at_node
#check Polynomial.Chebyshev.roots_T_real
#check Polynomial.Chebyshev.roots_T_real_nodup
#check Polynomial.Chebyshev.T_derivative_eq_U
#check MapClusterPt
#check mapClusterPt_iff_frequently
#check IsClosed.mem_of_mapClusterPt
#check TopologicalSpace.exists_dense_seq
#check ArithmeticFunction.moebius
#check ArithmeticFunction.coe_zeta_mul_coe_moebius
```

## 24. Informal proof compressed into Lean milestones

The entire formal proof can be thought of as this chain:

1. `F_n` is a continuous linear functional on `C[0,π]` representing Chebyshev-root Lagrange evaluation at `x₀ = cos θ₀`.
2. If `ψ` vanishes near `θ₀`, then `F_n ψ → 0`.
3. There are arbitrarily large dyadic rows `n` where `cos(nθ₀)` is bounded away from zero and the finitely many `cos(nsθ₀)` needed for `s≤R` are nonzero.
4. Primitive nodes of order `ns` have total weight at least `c_R |cos(nsθ₀)| log n`.
5. Möbius inversion gives a finite value assignment on primitive nodes that hits row `n` and cancels all rows `≤ Rn` except `n`.
6. Tiny tents turn this finite assignment into a continuous function without changing early rows; future rows are bounded by `η_R + δ`, with `η_R → 0`.
7. A summable sequence of such block spikes lets us prescribe selected row values `a_m` whose cluster set is `A`, while all nonselected rows converge to a fixed `c ∈ A`.
8. Therefore the total cluster set is `A`.
9. Transfer from angle variables to the original interval using `f(x)=φ(arccos x)`.
