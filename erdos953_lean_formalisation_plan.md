# Lean formalisation scaffold for the Poisson-Bessel proof of Erdős Problem #953

This document is a detailed implementation plan for formalising the short note

`https://www.ulam.ai/research/erdos953-short.pdf`

in Lean 4 using only mathlib.  It is intended as a scaffold for Codex: theorem names and imports below are approximate, and some Lean snippets are deliberately schematic.  The final Lean development should contain no `axiom`, no `constant` standing for an unproved theorem, and no remaining `sorry`.

The plan focuses on the new upper bound

\[
  M(R) \le C R^{1/2} \qquad (R\ge 1),
\]

and the equivalent robust finite estimate

\[
  |P| \le C\,\delta^{-2} X^{1/2}.
\]

The lower-bound consequence `M(R) = R^{1/2+o(1)}` uses Sárközy's construction.  Unless that construction is also formalised, do not state the asymptotic equality as a theorem in the final Lean file.  It can be mentioned as an informal corollary, or the project can add a separate formalisation of the relevant Sárközy papers later.

---

## 0. Quick mathematical sanity check and formalisation risks

I do not see a fatal mathematical obstruction in the short proof.  The core Delsarte/positive-definite argument is standard once the kernel has the advertised properties.  The algebra in the Poisson-side term estimate also looks coherent: the `b < a` case has leading real part `-a D^{-3/2}`, and the `b > a` case gives

\[
  -sD^{-3/2} - 3a^2sD^{-5/2} + \frac{15}{2}s^3D^{-5/2} + R,
\]

which can be made non-positive by taking `s0` small and `L` large.

However, for formalisation, the following points must be repaired or expanded.

1. **Poisson summation justification.**  The note says to insert a Gaussian factor and apply Schwartz-class Poisson summation.  Multiplying `e^{-s|x|}` by a Gaussian does not make it smooth at `0`.  This is not fatal: mathlib has a general one-dimensional Poisson summation theorem for continuous functions with suitable decay of the function and its Fourier transform.  Use that theorem instead of a Schwartz-only statement.

2. **Bessel functions.**  Do not expect a ready-made `J0` in mathlib.  Define the required `J0` by a circle average, or define only the specific circle-average function needed here.  The proof needs two things about this `J0`: positive definiteness of the radial kernel, and the Laplace transform identity
   \[
     \int_0^\infty e^{-\lambda x}J_0(2\pi t x)\,dx
       = (\lambda^2 + (2\pi t)^2)^{-1/2}, \qquad \Re\lambda>0.
   \]
   These should be formalised as project lemmas, not assumed.

3. **Asymptotic notation.**  Replace every `O(...)`, `\ll`, and “choose `L` large, `s0` small” with existential constants and explicit inequalities.  It is fine to prove lemmas of the form `∃ L s0 c, ...`; it is not necessary to compute attractive constants.

4. **Measurable reduction.**  The upper reduction uses inner regularity of Lebesgue measure and finite nets in compact metric spaces.  Mathlib has regular-measure infrastructure, but this part is still tedious.  Formalise the finite-point robust theorem first, then add the measure-theoretic wrapper.

---

## 1. Suggested project layout

Use small files.  The analytic proof is long enough that a monolithic file will be hard for Codex to repair.

```text
Erdos953/
  Basic.lean                  -- Euclidean plane, distance-to-integers, admissible sets
  Delsarte.lean               -- abstract positive-definite-kernel point bound
  CircleBessel.lean           -- definition of J0 by circle average and positivity
  LaplaceBessel.lean          -- Laplace transform identity and Fourier transforms
  PoissonKernel.lean          -- Poisson-side formula K_s = sum_m T_m
  ComplexPowBounds.lean       -- local Taylor/remainder bounds for complex cpow
  TermNegativity.lean         -- T_m <= 0 and one negative term
  RobustPointBound.lean       -- N(X,δ) / finite-set theorem
  MeasureReduction.lean       -- measurable M(R) <= sup δ^2 N(R,δ)
  Main.lean                   -- final upper bound theorem
```

The core proof dependency chain should be:

```text
Basic
  -> Delsarte
  -> CircleBessel
  -> LaplaceBessel
  -> PoissonKernel
  -> ComplexPowBounds
  -> TermNegativity
  -> RobustPointBound
  -> MeasureReduction
  -> Main
```

The first target should be to make `Delsarte.lean` and `RobustPointBound.lean` compile with the kernel properties as hypotheses.  Then prove the kernel properties in the analytic files.

---

## 2. Global conventions and target theorem statements

### 2.1 Imports

Start with broad imports, then trim later.

```lean
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.MetricSpace.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
```

Some of these names may have moved; ask Codex to use `#check` / `#find` to locate current names.

### 2.2 The plane

Use the finite-dimensional Euclidean space already supported by mathlib.

```lean
noncomputable section
open scoped Real BigOperators Topology ENNReal
open MeasureTheory Filter Finset

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)
```

For points `x y : Plane`, `dist x y` is the Euclidean distance.  Avoid manually unfolding into coordinates except in the circle-parameterisation file.

### 2.3 Distance to the integer lattice in `ℝ`

The robust condition is

\[
  \|t\|_{\mathbb Z} := \inf_{n\in\mathbb Z}|t-n| \ge \delta.
\]

For formal work, avoid an actual `iInf` if possible.  Use the logically equivalent predicate

\[
  \forall n: \mathbb Z,\quad \delta \le |t-n|.
\]

This is exactly what the proof needs.

```lean
namespace Erdos953

def AwayFromIntegers (δ t : ℝ) : Prop :=
  ∀ n : ℤ, δ ≤ |t - (n : ℝ)|

def AwayFromPositiveIntegers (η t : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → η ≤ |t - (n : ℝ)|
```

Basic lemmas:

```lean
lemma away_zero_le_dist {δ t : ℝ} (hδ : 0 ≤ δ)
    (h : AwayFromIntegers δ t) : δ ≤ |t| := by
  -- use h 0 and simp

lemma away_of_away_pos_and_ge_delta
    {δ η t : ℝ} (hδη : δ ≤ η) (hpos : AwayFromPositiveIntegers η t)
    (ht : δ ≤ t) : AwayFromIntegers δ t := by
  -- n = 0 follows from ht and t >= 0;
  -- n > 0 follows from hpos;
  -- n < 0 follows since t >= 0 and |t - n| >= t >= δ or >= 1.
```

For robust point sets, `t = dist p q ≥ 0`.  If the set is also Euclidean `δ`-separated, then the `n = 0` integer is handled.

### 2.4 Finite robust point theorem: preferred target

Rather than defining `N(X,δ)` first, prove the theorem for every finite set.  This avoids early work on existence of a maximum.

```lean
def RobustFiniteSet (X δ : ℝ) (P : Finset Plane) : Prop :=
  (∀ p ∈ P, dist p 0 ≤ X) ∧
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q → AwayFromIntegers δ (dist p q))

/-- Main finite robust estimate. -/
theorem robust_finite_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * δ⁻² * Real.sqrt X := by
  -- final proof after kernel package
```

This is Theorem 3 in finite-set form.

### 2.5 Measurable upper theorem

Define admissibility and `M`.  Use closed balls; open/closed does not matter for the asymptotic bound, and closed balls simplify compactness.

```lean
def NoPositiveIntegerDistances (A : Set Plane) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ n : ℕ, 0 < n → dist x y ≠ (n : ℝ)

def AdmissibleSet (R : ℝ) (A : Set Plane) : Prop :=
  MeasurableSet A ∧ A ⊆ Metric.closedBall (0 : Plane) R ∧ NoPositiveIntegerDistances A

noncomputable def area (A : Set Plane) : ℝ :=
  (volume A).toReal

noncomputable def M (R : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ A : Set Plane, AdmissibleSet R A ∧ area A = a}

/-- Main upper-bound theorem from the paper. -/
theorem erdos953_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  -- MeasureReduction + robust_finite_bound
```

Do not formalise the `R^{1/2+o(1)}` statement unless Sárközy's lower bound has been formalised.

---

## 3. Abstract Delsarte kernel package

This is the most important modularisation.  Prove the finite bound from a kernel satisfying three properties: positive definiteness, diagonal size, and off-diagonal negativity.

### 3.1 Kernel package structure

Let `K s t` be a real scalar kernel depending on a small parameter `s > 0` and radial distance `t ≥ 0`.

```lean
structure DelsarteKernelPackage where
  K : ℝ → ℝ → ℝ
  A : ℝ
  cneg : ℝ
  Cdiag : ℝ
  s0 : ℝ
  A_pos : 0 < A
  cneg_pos : 0 < cneg
  Cdiag_pos : 0 < Cdiag
  s0_pos : 0 < s0

  /-- Positive definiteness on the plane, in radial form. -/
  pos_def :
    ∀ (s : ℝ), 0 < s → s < s0 →
      ∀ (P : Finset Plane),
        0 ≤ ∑ p in P, ∑ q in P, K s (dist p q)

  /-- Diagonal bound.  Since `dist p p = 0`. -/
  diag_bound :
    ∀ (s : ℝ), 0 < s → s < s0 → K s 0 ≤ Cdiag * s⁻²

  /-- Off-diagonal negativity away from integers. -/
  offdiag_bound :
    ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A * s) t →
      K s t ≤ - cneg * (1 + t)⁻¹/2
```

Lean may not parse `(1 + t)⁻¹/2` as intended.  Prefer a helper:

```lean
def invSqrtOnePlus (t : ℝ) : ℝ := (Real.sqrt (1 + t))⁻¹
```

Then use

```lean
K s t ≤ - cneg * invSqrtOnePlus t
```

This avoids real-power branch complications.

### 3.2 Delsarte finite bound from package

Statement:

```lean
theorem robust_finite_bound_from_kernel
    (pkg : DelsarteKernelPackage) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * δ⁻² * Real.sqrt X := by
```

Proof details:

1. Choose a scaling constant `B` so that `s = δ / B` satisfies `s < s0` and `δ ≥ A*s`.

   A convenient existential choice:

   ```lean
   let B : ℝ := max (2 * pkg.A) ((10 * pkg.s0)⁻¹)
   let s : ℝ := δ / B
   ```

   Prove:

   ```lean
   have hBpos : 0 < B := by positivity / linarith
   have hspos : 0 < s := by positivity
   have hss0 : s < pkg.s0 := by
     -- from δ < 1/10 and B ≥ (10*s0)^{-1}
   have hdelta_ge_As : pkg.A * s ≤ δ := by
     -- from B ≥ A, in fact B ≥ 2A
   ```

2. Let `n = P.card` as a real.

   ```lean
   let nR : ℝ := P.card
   ```

3. From positive definiteness:

   \[
     0 \le \sum_{p,q\in P}K_s(d(p,q)).
   \]

4. Split diagonal and off-diagonal.

   Recommended lemma:

   ```lean
   lemma sum_pair_split_diag_offdiag (P : Finset Plane) (F : Plane → Plane → ℝ) :
      ∑ p in P, ∑ q in P, F p q =
        ∑ p in P, F p p +
        ∑ p in P, ∑ q in P.filter (fun q => q ≠ p), F p q := by
      -- use Finset.sum_filter, sum_ite, and `by_cases q = p`
   ```

   Or use `Finset.sum_product` on `P.product P` and split by `{(p,q) | p=q}`.

5. Bound diagonal:

   ```lean
   have hdiag :
      ∑ p in P, pkg.K s (dist p p) ≤ (P.card : ℝ) * pkg.Cdiag * s⁻² := by
      -- simp [dist_self], use pkg.diag_bound
   ```

6. Bound off-diagonal.  For `p ≠ q`, robust condition gives `AwayFromIntegers δ (dist p q)`.  Since `A*s ≤ δ`, it gives `AwayFromIntegers (A*s) (dist p q)`.  Also `dist p q ≤ 2X` by triangle:

   ```lean
   have hdist_le_2X : dist p q ≤ 2 * X := by
     have hpX := hP.1 p hp
     have hqX := hP.1 q hq
     calc
       dist p q ≤ dist p 0 + dist q 0 := by
         -- metric triangle, possibly rewrite dist_comm
       _ ≤ X + X := by linarith
       _ = 2 * X := by ring
   ```

   Since `t ↦ invSqrtOnePlus t` is decreasing for `t ≥ 0`, from `dist p q ≤ 2X` get

   \[
     (1+d(p,q))^{-1/2} \ge (1+2X)^{-1/2}.
   \]

   Multiplying by negative `-cneg` reverses direction in the expected way:

   ```lean
   pkg.K s (dist p q) ≤ -pkg.cneg * invSqrtOnePlus (2 * X)
   ```

   Lemma to prove:

   ```lean
   lemma invSqrtOnePlus_anti {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
      invSqrtOnePlus v ≤ invSqrtOnePlus u := by
     -- unfold invSqrtOnePlus; use Real.sqrt_le_sqrt, inv_anti₀
   ```

7. Count off-diagonal pairs: there are `P.card * (P.card - 1)`.  In real form:

   ```lean
   ∑ p in P, ∑ q in P.filter (fun q => q ≠ p), C
     = (P.card : ℝ) * ((P.card : ℝ) - 1) * C
   ```

   For Lean, use natural cardinal first:

   ```lean
   (P.filter (fun q => q ≠ p)).card = P.card - 1
   ```

   since `p ∈ P`.  Then coerce to `ℝ`.

8. Combine:

   \[
   0 \le C_{diag} n s^{-2}
       - c_{neg} n(n-1)(1+2X)^{-1/2}.
   \]

9. If `P.card ≤ 1`, finish by enlarging `C`.

10. If `2 ≤ P.card`, divide by positive `n` and rearrange:

    \[
      n - 1 \le (C_{diag}/c_{neg}) s^{-2}\sqrt{1+2X}.
    \]

    Since `X ≥ 1`, prove

    \[
      \sqrt{1+2X} \le \sqrt{3X} = \sqrt 3\sqrt X.
    \]

    In Lean, avoid equality of square roots if it is annoying; prove a crude bound like

    ```lean
    lemma sqrt_one_add_two_mul_le_three_mul_sqrt {X : ℝ} (hX : 1 ≤ X) :
      Real.sqrt (1 + 2 * X) ≤ 2 * Real.sqrt X
    ```

    because `1+2X ≤ 4X` for `X≥1`, so square roots give `≤ sqrt(4X) = 2 sqrt X`.

11. Convert `s^{-2}` to `B^2 * δ^{-2}`:

    Since `s = δ / B`,

    \[
      s^{-2} = B^2\delta^{-2}
    \]

    for positive `δ,B`.  In Lean:

    ```lean
    have hs_inv_sq : s⁻² = B^2 * δ⁻² := by
      field_simp [s, hδ.ne', hBpos.ne']
      ring
    ```

12. Choose final constant, e.g.

    ```lean
    let Cfinal := max 10 (4 * pkg.Cdiag / pkg.cneg * B^2)
    ```

    Add factors from the square-root bound and `n ≤ 1` case.

This abstract theorem should be made to compile early.  It validates the global proof architecture before tackling analysis.

---

## 4. The circle-average Bessel function and positive definiteness

The paper writes `J0`.  For Lean, define exactly the function needed.

### 4.1 Definition by angular average

The standard identity is

\[
  J_0(u)=\int_0^1 \exp(iu\cos(2\pi\theta))\,d\theta.
\]

The imaginary part integrates to zero, so this is real.  Define it as the real part of the complex integral.

```lean
namespace CircleBessel

noncomputable def J0c (u : ℝ) : ℂ :=
  ∫ θ in (0)..(1), Complex.exp (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))

noncomputable def J0 (u : ℝ) : ℝ := (J0c u).re
```

Depending on interval integral support for complex-valued functions, the definition may be easier with `∂volume.restrict (Set.Icc 0 1)` rather than `∫ θ in 0..1`.

Suggested alternative:

```lean
noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

noncomputable def J0c (u : ℝ) : ℂ :=
  ∫ θ, Complex.exp (Complex.I * (u : ℂ) * Complex.ofReal (Real.cos (2 * Real.pi * θ)))
    ∂unitIntervalMeasure
```

Then prove `unitIntervalMeasure Set.univ = 1` if needed.

Basic lemmas:

```lean
lemma J0c_zero : J0c 0 = 1 := by
  -- integrand is 1, measure of [0,1] is 1

lemma J0_zero : J0 0 = 1 := by
  simp [J0, J0c_zero]

lemma norm_J0c_le_one (u : ℝ) : ‖J0c u‖ ≤ 1 := by
  -- norm integral <= integral norm = 1

lemma abs_J0_le_one (u : ℝ) : |J0 u| ≤ 1 := by
  -- |re z| <= ‖z‖ and previous lemma
```

### 4.2 Vector circle parameterisation

For positive definiteness, introduce the vector on the unit circle:

```lean
noncomputable def circlePoint (θ : ℝ) : Plane :=
  ![Real.cos (2 * Real.pi * θ), Real.sin (2 * Real.pi * θ)]
```

The exact vector syntax may need adjustment.  Alternative:

```lean
def circlePoint (θ : ℝ) : Fin 2 → ℝ := fun j =>
  if j = 0 then Real.cos (2 * Real.pi * θ) else Real.sin (2 * Real.pi * θ)
```

Prove:

```lean
lemma norm_circlePoint (θ : ℝ) : ‖circlePoint θ‖ = 1 := by
  -- unfold Euclidean norm; use cos_sq_add_sin_sq
```

For `x : Plane`, define the circle average

```lean
noncomputable def circleExpAverage (k : ℕ) (x : Plane) : ℂ :=
  ∫ θ in (0)..(1),
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
      Complex.ofReal (inner (circlePoint θ) x))
```

Then prove the radial identity:

```lean
lemma circleExpAverage_eq_J0_norm (k : ℕ) (x : Plane) :
    circleExpAverage k x = J0c (2 * Real.pi * (k : ℝ) * ‖x‖) := by
```

Proof idea:

1. If `x = 0`, both sides are `1`.
2. If `x ≠ 0`, write `x = ‖x‖ • u` with `‖u‖=1`.
3. In two dimensions, choose an angle `φ` such that `u = (cos φ, sin φ)`.  This angle-existence lemma may not be directly in mathlib.
4. Then
   \[
   \langle (\cos 2\pi\theta,\sin 2\pi\theta), x\rangle
     = \|x\|\cos(2\pi\theta-\phi).
   \]
5. Use translation invariance/periodicity of the integral over `[0,1]`.

This radial identity is tedious.  Two implementation options:

- **Option A:** Prove it fully.  This is cleanest mathematically.
- **Option B:** Define `J0` for scalar `t` by evaluating `circleExpAverage k` at the vector `(t,0)` only, and separately prove positive definiteness for the scalar kernel using a rotation lemma stated just for finite point differences.  This is not really easier.
- **Option C:** Use Haar measure on the unit circle if mathlib has enough infrastructure for `O(2)` rotations.  This may be elegant but risks more typeclass overhead.

For Codex, start with Option A and create helper lemmas:

```lean
lemma exists_angle_of_unit_vector (u : Plane) (hu : ‖u‖ = 1) :
    ∃ φ : ℝ, u = ![Real.cos φ, Real.sin φ] := by
  -- use atan2 if available; otherwise prove from coordinates using `Real.exists_cos_eq_and_sin_eq`
```

Search mathlib for lemmas around `Real.arctan2`, `Complex.arg`, and `Complex.abs`.

### 4.3 Positive definiteness of one frequency

For fixed `k`, prove

\[
  \sum_{p,q\in P} J_0(2\pi k\|p-q\|)
    = \int_0^1 \left|\sum_{p\in P} e^{2\pi i k\langle \omega_\theta,p\rangle}\right|^2 d\theta\ge0.
\]

Lean statement:

```lean
lemma J0_frequency_pos_def (k : ℕ) (P : Finset Plane) :
    0 ≤ ∑ p in P, ∑ q in P, J0 (2 * Real.pi * (k : ℝ) * dist p q) := by
```

Proof details:

1. Use `dist p q = ‖p - q‖`.
2. Use `circleExpAverage_eq_J0_norm k (p - q)`.
3. Expand inner product:
   `inner ω (p - q) = inner ω p - inner ω q`.
4. Use `Complex.exp (a - b) = Complex.exp a / Complex.exp b`, and since the exponents are purely imaginary, this equals `exp(a) * conj(exp(b))`.
5. Interchange finite sums and integral:

   ```lean
   integral_finset_sum
   ```

   Search for `integral_finset_sum`, `Finset.sum_integral`.

6. Conclude the integral is `∫ θ, ‖∑ p in P, exp(...)‖^2`, whose integrand is nonnegative.

Recommended helper:

```lean
lemma complex_sum_mul_conj_eq_normSq (z : Plane → ℂ) (P : Finset Plane) :
    (∑ p in P, z p) * star (∑ p in P, z p)
      = Complex.ofReal (‖∑ p in P, z p‖ ^ 2) := by
```

Or use `Complex.normSq` if easier.

### 4.4 The actual kernel and diagonal bound

Define weights

\[
  w_s(k) = (k + 2sk^2)e^{-sk}, \quad k\ge1.
\]

Use `ℕ+` or natural numbers with `k+1`.  `ℕ+` is more faithful but can make coercions harder.  A simple natural-indexed version:

```lean
noncomputable def weight (s : ℝ) (n : ℕ) : ℝ :=
  let k : ℝ := (n + 1 : ℕ)
  (k + 2 * s * k^2) * Real.exp (-s * k)

noncomputable def K_bessel (s t : ℝ) : ℝ :=
  ∑' n : ℕ, weight s n * J0 (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)
```

Prove weights are nonnegative for `s>0`:

```lean
lemma weight_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0 ≤ weight s n := by
  -- k>0, exp positive
```

Positive definiteness for `K_bessel`:

```lean
lemma K_bessel_pos_def {s : ℝ} (hs : 0 < s) (P : Finset Plane) :
    0 ≤ ∑ p in P, ∑ q in P, K_bessel s (dist p q) := by
```

Proof idea:

1. Show summability of `n ↦ weight s n` using exponential decay.
2. Interchange `tsum` with finite sums.
3. Each frequency is nonnegative by `J0_frequency_pos_def` and weight nonnegative.
4. Use `tsum_nonneg`.

Diagonal:

```lean
lemma K_bessel_zero_eq (s : ℝ) :
    K_bessel s 0 = ∑' n : ℕ, weight s n := by
  -- J0 0 = 1
```

Need bound

\[
  \sum_{k\ge1} (k+2sk^2)e^{-sk} \le C s^{-2}, \quad 0<s<1.
\]

A good formal route uses exact geometric series with `r = exp(-s)`:

\[
  \sum_{k\ge1} k r^k = \frac{r}{(1-r)^2},
  \qquad
  \sum_{k\ge1} k^2 r^k = \frac{r(1+r)}{(1-r)^3}.
\]

Then for `0<s≤1`, prove

\[
  1-e^{-s} \ge e^{-1}s.
\]

because

\[
  1-e^{-s} = \int_0^s e^{-u}\,du \ge s e^{-1}.
\]

If the integral proof is annoying, use convexity/mean value theorem for `exp`, or prove a cruder lemma by monotonicity of `(1-exp(-s))/s`.

Then:

\[
  \sum k e^{-sk} \le e^2 s^{-2},
\]

and

\[
  2s\sum k^2e^{-sk} \le 4e^3 s^{-2}.
\]

The exact constants do not matter.  Suggested statement:

```lean
lemma K_bessel_diag_bound :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ s : ℝ, 0 < s → s < 1 → K_bessel s 0 ≤ Cdiag * s⁻² := by
```

Later, the package can set `pkg.Cdiag` to this existential constant, and `pkg.s0 ≤ 1`.

---

## 5. Poisson-side formula without Schwartz shortcuts

This is the analytic identity behind the term formula.  The clean formalisation should avoid differentiating Poisson summation with respect to `s`.  Instead, apply Poisson summation separately to three continuous exponentially decaying even functions.

### 5.1 Definitions

For `s>0`, `t≥0`, and `x:ℝ`, define

\[
  f_0(x)=e^{-s|x|}J_0(2\pi t|x|),
\]

\[
  f_1(x)=|x|e^{-s|x|}J_0(2\pi t|x|),
\]

\[
  f_2(x)=|x|^2e^{-s|x|}J_0(2\pi t|x|).
\]

```lean
noncomputable def poissonBase (s t x : ℝ) : ℂ :=
  Complex.ofReal (Real.exp (-s * |x|)) *
  Complex.ofReal (CircleBessel.J0 (2 * Real.pi * t * |x|))

noncomputable def poissonF1 (s t x : ℝ) : ℂ :=
  Complex.ofReal |x| * poissonBase s t x

noncomputable def poissonF2 (s t x : ℝ) : ℂ :=
  Complex.ofReal (|x|^2) * poissonBase s t x
```

The left side after summing over `ℤ` is:

```lean
lemma zsum_poissonF1_eq_two_bessel_sum :
    (∑' n : ℤ, poissonF1 s t (n : ℝ))
      = 2 * (∑' n : ℕ, Complex.ofReal (((n+1 : ℕ) : ℝ) * Real.exp (-s*((n+1:ℕ):ℝ))
          * CircleBessel.J0 (2*Real.pi*t*((n+1:ℕ):ℝ)))) := by
  -- even function, zero at n=0
```

Similarly for `f2`.

### 5.2 Laplace-Bessel identity

The project needs the theorem:

```lean
theorem laplace_J0
    {λ : ℂ} {β : ℝ} (hλ : 0 < λ.re) :
    ∫ x in (0)..(∞), Complex.exp (-λ * Complex.ofReal x) *
        Complex.ofReal (CircleBessel.J0 (β * x))
      = (λ^2 + (β : ℂ)^2) ^ (- (1/2 : ℂ)) := by
```

Lean interval integrals over `[0,∞)` may be awkward.  Use `∫ x : ℝ in Set.Ioi 0, ...` or define as an improper integral via `∫ x, indicator (Set.Ioi 0) ...`.  The exact integration API should be chosen after checking mathlib.

The identity in the paper uses `β = 2πt` and principal complex square root.  In Lean, use `Complex.cpow`:

```lean
(λ^2 + (β : ℂ)^2) cpow (-(1/2 : ℂ))
```

or a helper:

```lean
noncomputable def invComplexSqrt (z : ℂ) : ℂ := z cpow (-(1/2 : ℂ))
```

#### Recommended proof route for `laplace_J0`

Because mathlib likely does not have Bessel transforms, formalise the classical integral from the circle-average definition.

1. Substitute the definition of `J0` as an average.
2. Use Fubini/dominated convergence to swap the `x` and `θ` integrals.  Domination: `‖exp(-λx) * exp(i β x cos θ)‖ = exp(-Re λ * x)`.
3. Compute the elementary Laplace integral

   \[
     \int_0^\infty e^{-(\lambda - i\beta\cos(2\pi\theta))x}\,dx
       = \frac{1}{\lambda - i\beta\cos(2\pi\theta)}
   \]

   since `Re(λ - iβ cos(...)) = Re λ > 0`.

4. Prove the remaining angular integral

   \[
   \int_0^1 \frac{d\theta}{\lambda - i\beta\cos(2\pi\theta)}
     = (\lambda^2+\beta^2)^{-1/2}.
   \]

This last angular integral is nontrivial.  Possible approaches:

- Use the tangent-half-angle substitution and integrate a rational function.
- Use complex contour integration on the unit circle.  Mathlib complex contour integration may be more overhead than the rational route.
- Prove both sides as holomorphic functions of `λ` on `{Re λ > 0}` and verify for real `λ>0`; probably too ambitious.

If this becomes the bottleneck, an alternative is to define a custom `J0` by the Laplace identity and separately prove the circle-average representation.  That merely moves the difficulty; the final project must prove both positivity and the Laplace transform with no axioms.

### 5.3 Fourier transforms of `f1` and `f2`

Let

\[
  \lambda_m = s + 2\pi i m,
  \qquad q_m(t)=\lambda_m^2 + (2\pi t)^2.
\]

Define:

```lean
noncomputable def lam (s : ℝ) (m : ℤ) : ℂ :=
  Complex.ofReal s + 2 * Complex.ofReal Real.pi * Complex.I * Complex.ofReal (m : ℝ)

noncomputable def q (s t : ℝ) (m : ℤ) : ℂ :=
  lam s m ^ 2 + Complex.ofReal ((2 * Real.pi * t)^2)

noncomputable def Tterm (s t : ℝ) (m : ℤ) : ℝ :=
  ((lam s m) * (q s t m) cpow (-(3/2 : ℂ))
    + 2 * Complex.ofReal s *
        (-(q s t m) cpow (-(3/2 : ℂ))
          + 3 * (lam s m)^2 * (q s t m) cpow (-(5/2 : ℂ)))).re
```

Check Lean parsing of rational complex exponents.  It may need:

```lean
((q s t m) cpow (Complex.ofReal (-(3/2 : ℝ))))
```

Fourier transform formulas:

```lean
lemma fourier_poissonF1 (s t : ℝ) (m : ℤ) (hs : 0 < s) :
    FourierTransform.fourier (poissonF1 s t) (m : ℝ)
      = 2 * Complex.ofReal ((lam s m * (q s t m) cpow (-(3/2 : ℂ))).re) := by
  -- derive by differentiating `laplace_J0` in s or directly integrate x*exp(-λx)
```

```lean
lemma fourier_poissonF2 (s t : ℝ) (m : ℤ) (hs : 0 < s) :
    FourierTransform.fourier (poissonF2 s t) (m : ℝ)
      = 2 * Complex.ofReal (((-(q s t m) cpow (-(3/2 : ℂ))
           + 3 * (lam s m)^2 * (q s t m) cpow (-(5/2 : ℂ))).re)) := by
```

The factors of `2` arise because the real-line Fourier transform of an even function is twice the half-line Laplace integral.  The sign of `2πim` depends on mathlib's Fourier convention; because the final expression takes real parts and `m ↦ -m` is symmetric, a sign error can usually be fixed by replacing `m` with `-m`.  Still, align this carefully using `#check Real.fourierChar` and small test lemmas.

### 5.4 Applying mathlib Poisson summation

Use mathlib's general theorem for continuous functions with polynomial decay.  The docs indicate available theorems of the following shape:

```lean
Real.tsum_eq_tsum_fourier_of_rpow_decay
Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
```

We need continuous `f1`, `f2`, exponential decay, and Fourier transforms decaying like `|m|^{-2}`.  Prove helper lemmas:

```lean
lemma poissonF1_continuous (s t : ℝ) : Continuous (poissonF1 s t) := by
  -- abs is continuous; J0 is continuous; exp is continuous

lemma poissonF1_decay {s : ℝ} (hs : 0 < s) (t : ℝ) :
    poissonF1 s t =O[Filter.cocompact ℝ] fun x : ℝ => |x|^(-2 : ℝ) := by
  -- exponential beats polynomial; use mathlib exp decay lemmas if available

lemma fourier_poissonF1_decay {s : ℝ} (hs : 0 < s) (t : ℝ) :
    FourierTransform.fourier (poissonF1 s t)
      =O[Filter.cocompact ℝ] fun ξ : ℝ => |ξ|^(-2 : ℝ) := by
  -- use explicit formula and q ~ ξ^2
```

Analogous for `poissonF2`.

Then prove the Poisson representation:

```lean
theorem K_bessel_eq_tsum_Tterm
    {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    K_bessel s t = ∑' m : ℤ, Tterm s t m := by
```

Proof sketch:

1. Apply Poisson summation to `poissonF1` and `poissonF2` at `x = 0`.
2. Convert the left side over `ℤ` to twice the positive-natural sums.
3. Combine:

   \[
   K_s(t)=\sum_{k\ge1} k e^{-sk}J_0(2\pi kt)
      + 2s\sum_{k\ge1} k^2e^{-sk}J_0(2\pi kt).
   \]

4. The right sides combine into `∑'_m Tterm s t m`.

5. Prove summability of `Tterm` from the explicit `O(|m|^{-2})` bound.

This identity is the bridge from the positive-definite Bessel kernel to the termwise-sign Poisson kernel.

---

## 6. Complex power and Taylor-bound infrastructure

The term-negativity proof is mostly elementary inequalities for the principal branch of complex powers near `1` and `-1`.

Create `ComplexPowBounds.lean` with all local analytic estimates.  Keep these independent of Bessel/Poisson.

### 6.1 Use helpers for powers

```lean
noncomputable def cpowR (z : ℂ) (a : ℝ) : ℂ := z cpow (a : ℂ)

notation z "^c" a => cpowR z a
```

Maybe avoid custom notation in final if it causes parser issues.

### 6.2 Exact principal-branch values

Needed values:

\[
  (-1)^{-3/2}=i,\qquad (-1)^{-5/2}=-i,
\]

and for `D>0`,

\[
  (-D)^{-3/2}=iD^{-3/2},\qquad (-D)^{-5/2}=-iD^{-5/2}.
\]

Lean statements:

```lean
lemma cpow_neg_one_neg_three_half :
    ((-1 : ℂ) cpow (Complex.ofReal (-(3/2 : ℝ)))) = Complex.I := by
  -- unfold cpow via exp(log); Complex.arg(-1)=π

lemma cpow_neg_one_neg_five_half :
    ((-1 : ℂ) cpow (Complex.ofReal (-(5/2 : ℝ)))) = -Complex.I := by
```

For positive real scaling:

```lean
lemma cpow_ofReal_pos_mul {D : ℝ} (hD : 0 < D) (z : ℂ) (a : ℝ) :
    (Complex.ofReal D * z) cpow (Complex.ofReal a)
      = Complex.ofReal (D^a) * (z cpow Complex.ofReal a) := by
```

This may require avoiding `z=0` and branch issues.  In the actual use, `z` is near `1` or `-1`, hence nonzero and its argument stays in a branch-compatible disk.  It may be simpler to prove the two needed scaled identities directly from `Complex.log_mul` under hypotheses.

### 6.3 Taylor bounds near `1`

Need:

\[
  (1+z)^{-3/2}=1-\frac32z+E_3(z),\quad |E_3(z)|\le C|z|^2
\]

and

\[
  (1+z)^{-5/2}=1+E_5(z),\quad |E_5(z)|\le C|z|.
\]

For Lean, prove existential constants on the closed disk `|z| ≤ r`, with e.g. `r = 1/4`.

```lean
theorem cpow_one_add_neg_three_half_taylor :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ (1/4 : ℝ) →
        ‖(1 + z) cpow (Complex.ofReal (-(3/2 : ℝ)))
          - (1 - (3/2 : ℂ) * z)‖ ≤ C * ‖z‖^2 := by
```

```lean
theorem cpow_one_add_neg_five_half_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ (1/4 : ℝ) →
        ‖(1 + z) cpow (Complex.ofReal (-(5/2 : ℝ))) - 1‖ ≤ C * ‖z‖ := by
```

Recommended proof strategy:

- The functions are holomorphic on a neighbourhood of the closed disk `‖z‖≤1/4`.
- Use Taylor's theorem if convenient, but an easier formal route may be compactness:
  define the quotient
  \[
    H_3(z)=\begin{cases}
      ((1+z)^{-3/2}-(1-3z/2))/z^2, & z\ne 0,\\
      \text{the second Taylor coefficient},& z=0.
    \end{cases}
  \]
  prove it is continuous on the compact disk, so bounded.
- Similarly for
  \[
    H_5(z)=((1+z)^{-5/2}-1)/z.
  \]

This is somewhat involved.  If mathlib has a good one-variable Taylor theorem for complex differentiable functions, use it.  Otherwise compactness of a removable singularity is robust.

### 6.4 Bounds near `-1`

Need only first-order/lipschitz bounds:

\[
  (-1+z)^{-3/2}=i+O(|z|),
  \qquad
  (-1+z)^{-5/2}=-i+O(|z|)
\]

for `|z|≤1/4`.

```lean
theorem cpow_minus_one_add_neg_three_half_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ (1/4 : ℝ) →
        ‖((-1 : ℂ) + z) cpow (Complex.ofReal (-(3/2 : ℝ))) - Complex.I‖
          ≤ C * ‖z‖ := by
```

```lean
theorem cpow_minus_one_add_neg_five_half_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ (1/4 : ℝ) →
        ‖((-1 : ℂ) + z) cpow (Complex.ofReal (-(5/2 : ℝ))) + Complex.I‖
          ≤ C * ‖z‖ := by
```

Same proof strategy: continuity of difference quotient on compact disk, avoiding the principal branch cut issue by working in a small disk centred at `-1` that does not cross `0` but is on the branch boundary.  Note: principal `log` has a branch cut on the negative real axis, so analyticity at `-1` is false for the principal branch in a full disk.  We only need estimates for perturbations `-D + ζ` where `ζ` has positive real part `s^2` and imaginary part `2as`, i.e. points approach the negative axis from the upper half-plane.  A full disk around `-1` crosses the branch cut and will be discontinuous.

Therefore do **not** state a full-disk Lipschitz theorem around `-1` for principal `cpow`.  Instead state it on the specific wedge/half-disk used in the proof:

```lean
def NearNegBranchDomain (z : ℂ) : Prop :=
  ‖z‖ ≤ (1/4 : ℝ) ∧ 0 ≤ z.im
```

Then prove

```lean
theorem cpow_minus_one_add_neg_three_half_upper_wedge :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, NearNegBranchDomain z →
        ‖((-1 : ℂ) + z) cpow (Complex.ofReal (-(3/2 : ℝ))) - Complex.I‖
          ≤ C * ‖z‖ := by
```

In our application, `z = ζ/D`, where `ζ = s^2 + 2ias`, so `z.im ≥ 0`.

If this branch-domain proof becomes painful, avoid local analyticity and prove the estimate directly from the explicit formula for principal square root/log on the upper half-plane.  Since `-1+z` remains in the upper half-plane or on the negative axis approached with positive real perturbation, its argument is close to `π`, and the power is close to `exp(-α iπ)`.

---

## 7. Term negativity

This file proves Proposition 4 in the short note.

### 7.1 Real auxiliary variables

For `m ≥ 1`, the paper sets

\[
  a=2\pi m,
  \quad b=2\pi t,
  \quad \zeta=s^2+2ias.
\]

In Lean, `m` is an integer in `Tterm`; for one-term estimates, use a natural positive index and then convert.

```lean
noncomputable def aNat (m : ℕ) : ℝ := 2 * Real.pi * (m : ℝ)
noncomputable def bOfT (t : ℝ) : ℝ := 2 * Real.pi * t
noncomputable def zeta (s a : ℝ) : ℂ :=
  Complex.ofReal (s^2) + 2 * Complex.I * Complex.ofReal (a * s)
```

For `m : ℕ` with `1 ≤ m`, connect `Tterm s t (m : ℤ)` to these variables.

### 7.2 Elementary bounds

Assume `0 < s`, `s ≤ 1`, `1 ≤ m`, `a = 2πm`, and `|a-b| ≥ Ls`.

Prove:

```lean
lemma zeta_norm_le {s a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : 2 * Real.pi ≤ a) :
    ‖zeta s a‖ ≤ 3 * a * s := by
  -- norm of s^2 + i 2as <= s^2 + 2as <= as + 2as
  -- because s≤1 and a≥1 (use 2π≥1)
```

For `D = |a^2-b^2|`:

```lean
lemma D_lower {a b L s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsep : L * s ≤ |a - b|) :
    a * L * s ≤ |a^2 - b^2| := by
  -- |a^2-b^2| = |a-b|*(a+b), and a≤a+b
```

Then:

```lean
lemma zeta_div_D_le {s a b L : ℝ} ... :
    ‖zeta s a / Complex.ofReal (|a^2 - b^2|)‖ ≤ 3 / L := by
```

This is the source of the `|z|≤3/L` smallness condition.

### 7.3 `m = 0` term

The paper computes

\[
T_0(s,t) = s\frac{5s^2-(2\pi t)^2}{(s^2+(2\pi t)^2)^{5/2}}.
\]

Prove exactly:

```lean
lemma Tterm_zero_formula {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    Tterm s t 0 =
      s * (5*s^2 - (2*Real.pi*t)^2) /
        (Real.sqrt (s^2 + (2*Real.pi*t)^2))^5 := by
```

The denominator can be represented in any convenient equivalent form.  Then:

```lean
lemma Tterm_zero_nonpos {L s t : ℝ}
    (hL : Real.sqrt 5 ≤ L) (hs : 0 < s) (ht : 0 ≤ t)
    (hsep0 : L * s ≤ 2 * Real.pi * t) :
    Tterm s t 0 ≤ 0 := by
  -- numerator <= 0, denominator positive
```

### 7.4 The `b < a` estimate

Desired theorem:

```lean
theorem Tterm_left_of_lt
    : ∃ L s0 : ℝ, 1 ≤ L ∧ 0 < s0 ∧ s0 ≤ 1 ∧
      ∀ (s t : ℝ) (m : ℕ),
        0 < s → s < s0 → 1 ≤ m →
        let a := 2 * Real.pi * (m : ℝ)
        let b := 2 * Real.pi * t
        b < a → L * s ≤ |a - b| →
        Tterm s t (m : ℤ) ≤
          - (1/4 : ℝ) * a * (a^2 - b^2)⁻¹ * (Real.sqrt (a^2 - b^2))⁻¹ := by
```

The right side is intended as `-(1/4) a D^{-3/2}`.  In Lean, define:

```lean
def powNegThreeHalves (D : ℝ) : ℝ := (D * Real.sqrt D)⁻¹
```

for `D>0`, and state:

```lean
Tterm s t (m : ℤ) ≤ -(1/4) * a * powNegThreeHalves (a^2 - b^2)
```

Proof details:

1. Put `D = a^2-b^2 > 0`.
2. Show `q = -D + ζ = D * (-1 + ζ/D)`.
3. Use the upper-branch estimates:
   \[
   q^{-3/2}=iD^{-3/2}+E_3,
   \quad |E_3|≤C L^{-1}D^{-3/2}
   \]
   and
   \[
   q^{-5/2}=-iD^{-5/2}+E_5,
   \quad |E_5|≤C L^{-1}D^{-5/2}.
   \]
4. Substitute into `Tterm`.
5. The main contribution is `Re((s+ia)*iD^{-3/2}) = -aD^{-3/2}`.
6. Bound all errors by
   \[
     C(L^{-1}+s0+s0^2)aD^{-3/2}.
   \]
7. Choose `s0` and `L` so that the error is at most `(3/4) * a * D^{-3/2}` or `(1/2)` if using the short version.

For implementation, do not mix constant choice with algebra.  First prove a parameterised lemma:

```lean
lemma Tterm_left_bound_with_constants
    (Cpow : ℝ) (hCpow : 0 < Cpow) ... :
    |Tterm s t (m : ℤ) + a * powNegThreeHalves D|
      ≤ Cpow * (L⁻¹ + s0 + s0^2) * a * powNegThreeHalves D := by
```

Then a separate lemma chooses `L,s0`.

### 7.5 The `b > a` estimate

Desired theorem:

```lean
theorem Tterm_right_of_lt
    : ∃ L s0 : ℝ, 1 ≤ L ∧ 0 < s0 ∧ s0 ≤ 1 ∧
      ∀ (s t : ℝ) (m : ℕ),
        0 < s → s < s0 → 1 ≤ m →
        let a := 2 * Real.pi * (m : ℝ)
        let b := 2 * Real.pi * t
        a < b → L * s ≤ |a - b| →
        Tterm s t (m : ℤ) ≤
          -(1/4) * s *
            (powNegThreeHalves (b^2-a^2) + a^2 * powNegFiveHalves (b^2-a^2)) := by
```

Define

```lean
def powNegFiveHalves (D : ℝ) : ℝ := (D^2 * Real.sqrt D)⁻¹
```

for `D>0`.

Proof details:

1. Put `D=b^2-a^2>0` and `z=ζ/D`.
2. Use

   \[
     (1+z)^{-3/2}=1-\frac32z+E_3,
     \quad |E_3|≤C|z|^2,
   \]

   and

   \[
     (1+z)^{-5/2}=1+E_5,
     \quad |E_5|≤C|z|.
   \]

3. Compute main contribution exactly.  This algebra should be isolated as a `ring_nf` lemma:

```lean
lemma Tterm_right_main_algebra (s a D : ℝ) :
  -- Re of the truncated expression equals
  -- -sD^{-3/2} - 3a^2sD^{-5/2} + 15/2 s^3D^{-5/2}
```

4. Show the positive term is small:

\[
  \frac{15}{2}s^3D^{-5/2} \le \frac12 a^2sD^{-5/2}
\]

provided `s0` is small enough, since `s ≤ s0 ≤ a / sqrt(15)` and `a≥2π`.

5. Bound the remainder:

\[
  |R| \le C L^{-2}sD^{-3/2} + C L^{-1}a^2sD^{-5/2}.
\]

6. Choose `L` large so the remainder is absorbed by

\[
  \frac34 sD^{-3/2}+\frac94 a^2sD^{-5/2}
\]

or any convenient margin.

### 7.6 All terms are non-positive away from singular radii

For `m ≥ 1`, if `|2πm - 2πt| ≥ Ls`, then either `b<a` or `a<b`, and the previous estimates give `Tterm≤0`.

For `m = 0`, use the zero estimate.

For negative `m`, prove symmetry:

```lean
lemma Tterm_neg_m (s t : ℝ) (m : ℤ) :
    Tterm s t (-m) = Tterm s t m := by
  -- lam(-m)=conj(lam m), q(-m)=conj(q m), real part invariant under conjugation
```

Then:

```lean
theorem Tterm_nonpos_away
    : ∃ L s0 : ℝ, 1 ≤ L ∧ 0 < s0 ∧ s0 ≤ 1 ∧
      ∀ (s t : ℝ) (m : ℤ),
        0 < s → s < s0 → 0 ≤ t →
        L * s ≤ |2 * Real.pi * (m : ℝ) - 2 * Real.pi * t| →
        Tterm s t m ≤ 0 := by
```

### 7.7 One quantitatively negative term

If `distToInt t ≥ A*s`, choose `n = ceil t`.  The note uses `n = ⌈t⌉`, so `n ≥ 1`, `0 < n-t ≤ 1`, and `n-t ≥ A*s`.

Using the logical predicate:

```lean
AwayFromIntegers (A*s) t
```

implies, for the integer `ceil t`,

```lean
A*s ≤ |t - (Int.ceil t : ℝ)|
```

If `t` is not an integer, `ceil t - t > 0`; the away condition ensures it is not zero.

Define `A = L / (2π)`.  Then

```lean
L*s ≤ |2π*n - 2π*t|.
```

Use the `b<a` estimate with `m=n` to get

\[
  T_n(s,t) \le -c(1+t)^{-1/2}.
\]

Lean theorem:

```lean
theorem exists_negative_ceiling_term
    : ∃ A c s0 : ℝ, 0 < A ∧ 0 < c ∧ 0 < s0 ∧
      ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A*s) t →
        ∃ m : ℤ, Tterm s t m ≤ - c * invSqrtOnePlus t := by
```

Proof details:

1. Let `n : ℤ := Int.ceil t`.
2. Show `1 ≤ n`, because `t≥0` and away from integer `0` gives `A*s ≤ |t|`, so `t>0`.
3. Show `0 < (n:ℝ)-t ≤ 1` using ceil properties.
4. Let `D=(2πn)^2-(2πt)^2`.
5. From `n-t≤1` and `n≤t+1`, prove

   \[
   D = (2π)^2(n-t)(n+t) \le C_D(1+t).
   \]

6. Also `2πn ≥ c_a(1+t)`.  Since `n>t` and `n≤t+1`, a simple lower bound is `n ≥ t`, so for `t≥1`, `n≥t`; for `t≤1`, `n≥1`.  Thus `n ≥ (1+t)/2`.

   ```lean
   lemma ceil_lower_one_plus (t : ℝ) (ht : 0 ≤ t) :
      (Int.ceil t : ℝ) ≥ (1 + t)/2 := by
      -- if t≤1, ceil t ≥ 1; if t≥1, ceil t ≥ t
   ```

7. Combine:

   \[
   aD^{-3/2} \ge c(1+t)^{-1/2}.
   \]

### 7.8 Kernel negativity from term negativity

Now combine `K_bessel_eq_tsum_Tterm` with termwise nonpositivity.

```lean
theorem K_bessel_offdiag_negativity :
    ∃ A c s0 : ℝ, 0 < A ∧ 0 < c ∧ 0 < s0 ∧
      ∀ (s t : ℝ), 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A*s) t →
        K_bessel s t ≤ - c * invSqrtOnePlus t := by
```

Proof:

1. Use Poisson formula `K_bessel s t = ∑' m, Tterm s t m`.
2. From `AwayFromIntegers (A*s) t`, every term is non-positive because every integer radius is separated:

   \[
     |2πm-2πt| = 2π|m-t| ≥ 2π A s = Ls.
   \]

3. Obtain a selected `m0` with `Tterm m0 ≤ -c invSqrtOnePlus t`.
4. Use an infinite-sum lemma:

```lean
lemma tsum_le_term_of_summable_nonpos
    {ι : Type*} [Countable ι] [DecidableEq ι]
    {a : ι → ℝ} (ha : Summable a) (hnonpos : ∀ i, a i ≤ 0) (i0 : ι) :
    (∑' i, a i) ≤ a i0 := by
  -- write tsum as a i0 + tsum over complement; complement tsum ≤ 0
```

For `ι=ℤ`, this should be straightforward.  If the generic version is awkward, prove a special version for `ℤ`.

5. Conclude.

---

## 8. Instantiate the Delsarte kernel package

After proving:

- `K_bessel_pos_def`
- `K_bessel_diag_bound`
- `K_bessel_offdiag_negativity`

construct a `DelsarteKernelPackage`.

```lean
noncomputable def poissonBesselPackage : DelsarteKernelPackage := by
  classical
  obtain ⟨Cdiag, hCdiag_pos, hdiag⟩ := K_bessel_diag_bound
  obtain ⟨A, c, s0neg, hApos, hcpos, hs0negpos, hneg⟩ := K_bessel_offdiag_negativity
  let s0 : ℝ := min 1 s0neg
  refine
    { K := K_bessel
      A := A
      cneg := c
      Cdiag := Cdiag
      s0 := s0
      A_pos := hApos
      cneg_pos := hcpos
      Cdiag_pos := hCdiag_pos
      s0_pos := ?_
      pos_def := ?_
      diag_bound := ?_
      offdiag_bound := ?_ }
  -- fill fields, using s<s0 -> s<1 and s<s0neg
```

Then:

```lean
theorem robust_finite_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X δ : ℝ) (P : Finset Plane),
        1 ≤ X → 0 < δ → δ < 1 / 10 → RobustFiniteSet X δ P →
        (P.card : ℝ) ≤ C * δ⁻² * Real.sqrt X :=
  robust_finite_bound_from_kernel poissonBesselPackage
```

---

## 9. Optional definition of `N(X,δ)`

The paper defines `N(X,δ)` as a maximum.  For the final upper bound, the finite-set theorem is enough.  But if desired, define it after proving that all robust finite sets have bounded cardinality.

```lean
noncomputable def N (X δ : ℝ) : ℕ :=
  Nat.findGreatest
    (fun n : ℕ => ∃ P : Finset Plane, RobustFiniteSet X δ P ∧ P.card = n)
    SOME_BOUND
```

This requires an explicit natural upper bound.  Easier:

```lean
noncomputable def Nreal (X δ : ℝ) : ℝ :=
  sSup {n : ℝ | ∃ P : Finset Plane, RobustFiniteSet X δ P ∧ n = P.card}
```

Then prove:

```lean
lemma Nreal_le_from_robust_bound ... :
    Nreal X δ ≤ C * δ⁻² * Real.sqrt X := by
  -- use csSup_le
```

But unless needed for a theorem statement, skip `N` and use the finite theorem directly in `MeasureReduction`.

---

## 10. Measurable reduction: upper bound

The upper bound in Lemma 2 says an admissible measurable set can be covered by `δ`-balls around a robust finite set, hence has measure `≤ πδ²N`.

The formal version should use the finite-point theorem directly.

### 10.1 Compact distance separation

For compact `K` with no positive integer distances, prove there exists `η>0` such that all positive distances in `K` are `η`-away from positive integers up to `⌊2R⌋`.

Formal statement:

```lean
lemma compact_distances_away_from_positive_integers
    {R : ℝ} {K : Set Plane}
    (hKcompact : IsCompact K)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hKno : NoPositiveIntegerDistances K)
    (hR : 0 ≤ R) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
        AwayFromPositiveIntegers η (dist x y) := by
```

Proof approach:

1. Let
   \[
     D = \{dist x y : x∈K, y∈K\}.
   \]
   This is compact as the image of compact `K × K` under continuous distance.
2. Let finite set `I = {n : ℕ | 1≤n ∧ n≤floor(2R)}`.
3. For each `n∈I`, `n∉D` by no positive integer distances.
4. Since `D` is compact and `{n}` closed disjoint, `dist(D,{n})>0`.
5. Take the minimum over finite `I`.
6. For positive integers `n` larger than `floor(2R)`, use `dist x y ≤ 2R < n` to get a crude positive separation.  Actually `|dist-n| ≥ n-2R`; if `n=floor(2R)+1`, this can be small but positive.  Include it in the finite set by using `n≤ceil(2R)+1`, or simpler use finite set `{1,..., Nat.ceil(2R)+1}`.

Simpler proof:

Let `I = {n : ℕ | 0 < n ∧ (n : ℝ) ≤ 2R + 1}`.  For `n` outside this set, since `dist x y ≤ 2R`, we get `|dist-n| ≥ 1`.  Inside, compact separation gives positive minimum.  Then take `η = min η_inside 1`.

### 10.2 Finite maximal separated subset / net

For compact `K` and `δ>0`, obtain a finite subset `P⊂K` that is `δ`-separated and whose `δ`-balls cover `K`.

```lean
lemma exists_finite_delta_net_separated
    {K : Set Plane} (hKcompact : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Finset Plane,
      (∀ p ∈ P, p ∈ K) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q) ∧
      (K ⊆ ⋃ p ∈ (P : Set Plane), Metric.closedBall p δ) := by
```

Mathlib may already have total-bounded finite nets.  Search for:

- `TotallyBounded.exists_finset_cover`
- `Metric.totallyBounded_iff`
- `IsCompact.totallyBounded`

If a maximal separated subset is hard, use a finite `δ/2`-net and then extract a separated representative set.  But the paper's proof needs both cover and separation.  In compact metric spaces, a maximal separated subset gives both.  A constructive route:

1. Use total boundedness to get a finite cover by balls of radius `δ/2`.
2. Choose one point of `K` in each nonempty ball.  This gives a cover by radius `δ`, but not separated.
3. The robust point theorem requires separation from `0` as integer.  Instead of requiring the selected `P` be `δ`-separated, we can use a maximal separated set.  Therefore it is worth proving the maximal-separated lemma.

Possible formal route using finite cardinal maximality:

- Total boundedness gives a finite upper bound on the size of any `δ`-separated subset of `K`.
- Let `S` be the set of cardinalities of finite `δ`-separated subsets.  It is nonempty and bounded in `ℕ`, so has a maximum.
- Choose a finite subset `P` of maximum cardinality.
- If some `x∈K` is not within distance `<δ` of `P`, then `insert x P` is still `δ`-separated, contradiction.

This is more work but robust.

### 10.3 Build a robust finite set from compact `K`

Given `η` from distance separation and a maximal `δ`-separated `P` with `δ<η`, prove `RobustFiniteSet R δ P`.

For `p≠q` in `P`:

- `δ ≤ dist p q` by Euclidean separation, so integer `0` is avoided.
- Positive integers are avoided because `δ≤η` and `AwayFromPositiveIntegers η (dist p q)`.
- Negative integers are automatically far because `dist p q ≥ δ ≥ 0`.

Lemma:

```lean
lemma robust_of_compact_net
    {R δ η : ℝ} {K : Set Plane} {P : Finset Plane}
    (hδpos : 0 < δ) (hδη : δ ≤ η)
    (hPsub : ∀ p ∈ P, p ∈ K)
    (hPsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q)
    (hKsub : K ⊆ Metric.closedBall (0 : Plane) R)
    (hKaway : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → AwayFromPositiveIntegers η (dist x y)) :
    RobustFiniteSet R δ P := by
```

### 10.4 Measure bound from cover

If `K` is covered by `P.card` balls of radius `δ`, then

\[
  area(K) \le |P|\,\pi\delta^2.
\]

Mathlib should have volume of balls in Euclidean spaces.  Use a crude constant if the exact `π` is hard:

\[
  volume(B(p,δ)) = C_2 δ^2
\]

for `C_2 = volume(B(0,1))`.  This is enough.

Define a constant:

```lean
noncomputable def unitBallArea : ℝ := area (Metric.closedBall (0 : Plane) 1)
```

Prove:

```lean
lemma area_closedBall_le_const_mul_sq (p : Plane) {r : ℝ} (hr : 0 ≤ r) :
    area (Metric.closedBall p r) ≤ unitBallArea * r^2 := by
  -- preferably equality by translation and scaling; inequality is enough
```

If volume scaling in mathlib is hard, use `MeasureTheory.volume_closedBall` from `VolumeOfBalls`.

Cover lemma:

```lean
lemma area_le_card_mul_ball_area
    {K : Set Plane} {P : Finset Plane} {δ : ℝ}
    (hKmeas : MeasurableSet K) (hδ : 0 ≤ δ)
    (hcover : K ⊆ ⋃ p ∈ (P : Set Plane), Metric.closedBall p δ) :
    area K ≤ (P.card : ℝ) * unitBallArea * δ^2 := by
  -- measure monotonicity + finite subadditivity + equal ball areas
```

### 10.5 Inner regularity and final measurable upper bound

For an admissible measurable `A`, choose compact `K⊂A` with area close to `area A`.  Mathlib regularity file should provide an inner-regular compact approximation for finite-measure measurable sets.

Desired lemma:

```lean
lemma exists_compact_subset_area_gt
    {A : Set Plane} (hAmeas : MeasurableSet A) (hAfin : volume A < ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set Plane, IsCompact K ∧ K ⊆ A ∧ area A - ε < area K := by
```

Use `Measure.InnerRegular` / `InnerRegularCompactLTTop` instances for Lebesgue measure.

Final bound for any admissible `A`:

```lean
lemma admissible_area_le_sqrt
    (Crob : ℝ) (hCrob : 0 < Crob)
    (hrob : ∀ X δ P, 1≤X → 0<δ → δ<1/10 → RobustFiniteSet X δ P →
      (P.card : ℝ) ≤ Crob * δ⁻² * Real.sqrt X) :
    ∃ C : ℝ, 0 < C ∧
      ∀ R A, 1 ≤ R → AdmissibleSet R A → area A ≤ C * Real.sqrt R := by
```

Proof for fixed `A,R`:

1. Let `ε>0`.
2. Choose compact `K⊂A` with `area A - ε < area K`.
3. Get `η>0` for compact positive-integer distance separation.
4. Choose `δ = min (η/2) (1/20)`, so `0<δ<1/10`.
5. Get maximal separated `P⊂K` covering `K`.
6. Show `RobustFiniteSet R δ P`.
7. Area bound:

   \[
   area(K) ≤ unitBallArea * δ^2 * |P|
          ≤ unitBallArea * Crob * \sqrt R.
   \]

8. Let `ε→0`.  In Lean, avoid limit language by showing for every `ε>0`, `area A ≤ C√R + ε`; then use `le_of_forall_pos_le_add`.

```lean
have hforall_eps : ∀ ε > 0, area A ≤ C * Real.sqrt R + ε := by ...
exact le_of_forall_pos_le_add hforall_eps
```

Then lift from every admissible `A` to `M R` using `sSup_le`:

```lean
lemma M_le_of_admissible_area_bound
    {R C : ℝ} (hbound : ∀ A, AdmissibleSet R A → area A ≤ C) :
    M R ≤ C := by
  unfold M
  apply csSup_le
  · -- set nonempty: empty set has area 0
  · intro a ha
    rcases ha with ⟨A, hA, rfl⟩
    exact hbound A hA
```

### 10.6 The final upper theorem

```lean
theorem erdos953_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → M R ≤ C * Real.sqrt R := by
  obtain ⟨Crob, hCrob_pos, hrob⟩ := robust_finite_bound
  obtain ⟨Cmeas, hCmeas_pos, hmeas⟩ := admissible_area_le_sqrt Crob hCrob_pos hrob
  exact ⟨Cmeas, hCmeas_pos, hmeas⟩
```

---

## 11. Optional lower bound and why it should be separated

The note's lower bound uses Sárközy's theorem on point sets whose mutual distances stay away from integers.  That theorem is not a simple mathlib import.  Therefore there are three honest options:

1. **Do not formalise the lower bound.**  State only `erdos953_upper`.
2. **Create a separate project formalising Sárközy's theorem.**  Then derive the lower bound by disk thickening.
3. **State a conditional theorem**, not as an axiom but as a theorem taking Sárközy's point-set result as an explicit hypothesis:

   ```lean
   theorem lower_bound_conditional
       (sarkozy : ∀ ε > 0, ∃ c > 0, ∀ᶠ R in atTop,
          ∃ δ > 0, ∃ P : Finset Plane, ... ) :
       ∀ ε > 0, ∃ c > 0, ∀ᶠ R in atTop, c * R^(1/2 - ε) ≤ M R := by
   ```

This is not an axiom because it is a conditional theorem.  But it does not prove the unconditional lower bound.

---

## 12. Lean engineering notes

### 12.1 Avoid fragile real powers where possible

For nonnegative real expressions, prefer explicit inverse square roots:

```lean
def invSqrt (x : ℝ) : ℝ := (Real.sqrt x)⁻¹
def powNegThreeHalves (x : ℝ) : ℝ := (x * Real.sqrt x)⁻¹
def powNegFiveHalves (x : ℝ) : ℝ := (x^2 * Real.sqrt x)⁻¹
```

Then prove algebraic identities under `0<x`.  This is usually easier than using `x ^ (-3/2 : ℝ)`.

For complex powers, use `Complex.cpow` because the principal branch matters.

### 12.2 Keep constant choices centralised

Create a section:

```lean
structure NegConstants where
  L : ℝ
  s0 : ℝ
  c : ℝ
  L_ge_one : 1 ≤ L
  s0_pos : 0 < s0
  s0_le_one : s0 ≤ 1
  c_pos : 0 < c
```

Let the term-negativity theorem return a `NegConstants` object.  Avoid scattering `choose L large` across files.

### 12.3 Prove algebra separately from inequalities

For example, in the `b>a` case, first prove a pure algebra identity:

```lean
lemma right_main_re_identity (s a D : ℝ) :
  let ζ : ℂ := Complex.ofReal (s^2) + 2 * Complex.I * Complex.ofReal (a*s)
  (((Complex.ofReal s + Complex.I * Complex.ofReal a) * Complex.ofReal (powNegThreeHalves D) *
      (1 - (3/2 : ℂ) * ζ / Complex.ofReal D)
    + 2 * Complex.ofReal s *
      ( - Complex.ofReal (powNegThreeHalves D) *
          (1 - (3/2 : ℂ) * ζ / Complex.ofReal D)
        + 3 * (Complex.ofReal s + Complex.I * Complex.ofReal a)^2 *
          Complex.ofReal (powNegFiveHalves D))).re)
  = -s * powNegThreeHalves D - 3*a^2*s*powNegFiveHalves D
      + (15/2)*s^3*powNegFiveHalves D := by
  -- `ring_nf` after unfolding helpers, maybe with field_simp for D powers
```

Once this compiles, the inequality proof is much easier.

### 12.4 Useful tactics

- `positivity` for positivity of `Real.exp`, `Real.sqrt`, powers.
- `nlinarith` for polynomial inequalities over reals.
- `linarith` for linear inequalities.
- `ring_nf` for algebraic normal forms.
- `field_simp` only after collecting nonzero denominator proofs.
- `norm_num` for rational constants.
- `gcongr` for monotonicity in inequalities.

### 12.5 Use `calc` blocks extensively

Long inequality proofs should be written as chains, not as tactic soup.  Codex repairs them more reliably.

Example:

```lean
calc
  K_bessel s (dist p q)
      ≤ -pkg.cneg * invSqrtOnePlus (dist p q) := by
        exact pkg.offdiag_bound s (dist p q) hs hss0 (dist_nonneg) haway
  _ ≤ -pkg.cneg * invSqrtOnePlus (2 * X) := by
        -- monotonicity with negative multiplier
  _ = Cpair := by rfl
```

### 12.6 Mark hard lemmas with docstrings

Every major lemma should include the paper equation it corresponds to.  Example:

```lean
/-- Equation (2.3)/(2.4) in the short note: Poisson expansion of `K_s`. -/
theorem K_bessel_eq_tsum_Tterm ...
```

This helps Codex preserve intent during refactors.

---

## 13. Suggested milestones for Codex

### Milestone 1: compile definitions and abstract Delsarte theorem

Files:

- `Basic.lean`
- `Delsarte.lean`

Goal:

```lean
#check robust_finite_bound_from_kernel
```

No Bessel or Poisson yet.

### Milestone 2: diagonal and positive definiteness of the Bessel kernel

Files:

- `CircleBessel.lean`

Goal:

```lean
#check K_bessel_pos_def
#check K_bessel_diag_bound
```

At this stage, do not prove Poisson negativity.

### Milestone 3: Poisson expansion

Files:

- `LaplaceBessel.lean`
- `PoissonKernel.lean`

Goal:

```lean
#check K_bessel_eq_tsum_Tterm
```

Use mathlib's general Poisson theorem, not Schwartz Poisson.

### Milestone 4: term negativity

Files:

- `ComplexPowBounds.lean`
- `TermNegativity.lean`

Goal:

```lean
#check K_bessel_offdiag_negativity
```

### Milestone 5: robust point theorem

Files:

- `RobustPointBound.lean`

Goal:

```lean
#check robust_finite_bound
```

### Milestone 6: measurable upper bound

Files:

- `MeasureReduction.lean`
- `Main.lean`

Goal:

```lean
#check erdos953_upper
```

---

## 14. Minimal theorem list to drive implementation

The following theorem list can be pasted into Lean as declarations with proof placeholders during development.  The final version must replace all placeholders with proofs.

```lean
namespace Erdos953

abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

def AwayFromIntegers (δ t : ℝ) : Prop :=
  ∀ n : ℤ, δ ≤ |t - (n : ℝ)|

def RobustFiniteSet (X δ : ℝ) (P : Finset Plane) : Prop :=
  (∀ p ∈ P, dist p 0 ≤ X) ∧
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q → AwayFromIntegers δ (dist p q))

def invSqrtOnePlus (t : ℝ) : ℝ := (Real.sqrt (1 + t))⁻¹

structure DelsarteKernelPackage where
  K : ℝ → ℝ → ℝ
  A cneg Cdiag s0 : ℝ
  A_pos : 0 < A
  cneg_pos : 0 < cneg
  Cdiag_pos : 0 < Cdiag
  s0_pos : 0 < s0
  pos_def : ∀ s, 0 < s → s < s0 → ∀ P : Finset Plane,
    0 ≤ ∑ p in P, ∑ q in P, K s (dist p q)
  diag_bound : ∀ s, 0 < s → s < s0 → K s 0 ≤ Cdiag * s⁻²
  offdiag_bound : ∀ s t, 0 < s → s < s0 → 0 ≤ t →
    AwayFromIntegers (A*s) t → K s t ≤ -cneg * invSqrtOnePlus t

theorem robust_finite_bound_from_kernel (pkg : DelsarteKernelPackage) :
  ∃ C : ℝ, 0 < C ∧ ∀ X δ P,
    1 ≤ X → 0 < δ → δ < 1/10 → RobustFiniteSet X δ P →
    (P.card : ℝ) ≤ C * δ⁻² * Real.sqrt X := by
  -- implement first

namespace CircleBessel
noncomputable def J0c (u : ℝ) : ℂ := by
  -- definition by circle average
noncomputable def J0 (u : ℝ) : ℝ := (J0c u).re
end CircleBessel

noncomputable def weight (s : ℝ) (n : ℕ) : ℝ :=
  let k : ℝ := (n + 1 : ℕ)
  (k + 2 * s * k^2) * Real.exp (-s*k)

noncomputable def K_bessel (s t : ℝ) : ℝ :=
  ∑' n : ℕ, weight s n * CircleBessel.J0 (2 * Real.pi * ((n+1:ℕ):ℝ) * t)

noncomputable def lam (s : ℝ) (m : ℤ) : ℂ :=
  Complex.ofReal s + 2 * Complex.ofReal Real.pi * Complex.I * Complex.ofReal (m : ℝ)

noncomputable def q (s t : ℝ) (m : ℤ) : ℂ :=
  lam s m ^ 2 + Complex.ofReal ((2 * Real.pi * t)^2)

noncomputable def Tterm (s t : ℝ) (m : ℤ) : ℝ :=
  ((lam s m) * ((q s t m) cpow (Complex.ofReal (-(3/2 : ℝ))))
    + 2 * Complex.ofReal s *
      (-((q s t m) cpow (Complex.ofReal (-(3/2 : ℝ))))
        + 3 * (lam s m)^2 * ((q s t m) cpow (Complex.ofReal (-(5/2 : ℝ)))))).re

theorem K_bessel_pos_def :
  ∀ s, 0 < s → ∀ P : Finset Plane,
    0 ≤ ∑ p in P, ∑ q in P, K_bessel s (dist p q) := by
  -- circle-average proof

theorem K_bessel_diag_bound :
  ∃ Cdiag : ℝ, 0 < Cdiag ∧
    ∀ s, 0 < s → s < 1 → K_bessel s 0 ≤ Cdiag * s⁻² := by
  -- geometric/exponential sum proof

theorem K_bessel_eq_tsum_Tterm :
  ∀ s t, 0 < s → 0 ≤ t → K_bessel s t = ∑' m : ℤ, Tterm s t m := by
  -- Poisson summation proof

theorem K_bessel_offdiag_negativity :
  ∃ A c s0 : ℝ, 0 < A ∧ 0 < c ∧ 0 < s0 ∧
    ∀ s t, 0 < s → s < s0 → 0 ≤ t → AwayFromIntegers (A*s) t →
      K_bessel s t ≤ -c * invSqrtOnePlus t := by
  -- term negativity + Poisson expansion

noncomputable def poissonBesselPackage : DelsarteKernelPackage := by
  -- assemble previous properties

theorem robust_finite_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ X δ P,
    1 ≤ X → 0 < δ → δ < 1/10 → RobustFiniteSet X δ P →
    (P.card : ℝ) ≤ C * δ⁻² * Real.sqrt X :=
  robust_finite_bound_from_kernel poissonBesselPackage

end Erdos953
```

---

## 15. Final quality gates

Before considering the formalisation complete:

1. Run `lake build` with no `sorry` and no declarations of type `axiom` or unproved `constant`.
2. Search the project for `sorry`, `admit`, `axiom`, `constant`, and `unsafe`.
3. Ensure the final theorem is stated only for the upper bound unless Sárközy is formalised.
4. Confirm that the Poisson summation proof uses a theorem whose hypotheses are actually proved for the nonsmooth-at-zero functions.
5. Confirm that all complex powers use the principal branch and that the estimates near the negative real axis are proved on the correct one-sided/upper-branch domain.
6. Confirm that the final constants are existential and positive, with no hidden dependence on `R`, `X`, `δ`, `P`, `s`, or `t`.

