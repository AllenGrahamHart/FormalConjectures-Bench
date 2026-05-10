# Top 10 Informal-Proof Formalisation Roadmaps

Date prepared: 2026-05-10

This note records ten candidate solved statements from `formal-conjectures` /
`FormalConjectures-Bench` which have supporting informal proofs in the
literature and, at least in principle, could be turned into future benchmark
tasks.  It follows the style of the existing planning notes for Erdős 1151,
Erdős 330, Erdős 953, and `OpenQuantum35.ame_4_3_exists`: each candidate has
source references, a precise Lean target, a proposed proof route, milestones,
and a viability assessment.

The goal here is not to begin any formalisation.  The goal is to make the
candidate list reviewable: which targets are realistically comparable to the
three Erdős tasks and the AME task, and which would be major new library
projects.

## Summary Table

| Rank | Candidate | FormalConjectures target | Main source proof | Viability |
| ---: | --- | --- | --- | --- |
| 1 | Sylvester-Schur prime divisor theorem | `Erdos699.sylvester_schur`; related `Erdos961.erdos_961.sylvester_schur` | Erdős 1934, following Sylvester/Schur | Low-medium |
| 2 | Erdős-Turán Sidon upper bound | `Erdos329.erdos_329.variants.turan_1941` | Erdős-Turán 1941 | High |
| 3 | Shakan large-gap dilate theorem | `Green32.green_32.variants.sh20_general` | Shakan 2020 | Medium |
| 4 | Finite-field Kakeya sharp bound | `Kakeya.kakeya_finite` | Bukh-Chao 2021, Dvir 2009 background | Low-medium |
| 5 | Finite-dimensional Banach-Mazur rotation theorem | `banach_mazur_rotation_problem.finite_dimensional` | standard compact-group averaging proof | Medium |
| 6 | Zariski cancellation in dimension one | `zariski_cancellation_problem.variants.dim_one` | Abhyankar-Eakin-Heinzer, surveyed by Gupta | Low |
| 7 | Triangle-free degree-sequence embedding theorem | `SimpleGraph.theorem2` in `DegreeSequencesTriangleFree` | Erdős-Fajtlowicz-Staton 1991 | Medium |
| 8 | Weak Freiman/Erdős 245 sumset lower bound | `Erdos245.erdos_245.variants.two` | Freiman 1973 / Erdős Problems note | Medium-low |
| 9 | Ramsey `R(5,5)` bounds | `ramsey_number_five_five_lower_bound`, `ramsey_number_five_five_upper_bound` | Exoo 1989; Angeltveit-McKay 2024/2026 | Lower: high; upper: low |
| 10 | Erdős sumset conjecture | `Erdos109.erdos_109` | Moreira-Richter-Robertson 2019; Host 2019 | Low |

## Global Notes

- The phrase "no claimed formalisation" here means that the benchmark manifest
  records no proof links and a lightweight search for exact theorem names did
  not find Lean proofs.  This is not a mathematical proof of absence.
- A good first task should have a proof whose hard parts are mathematical but
  still local: finite sums, finite sets, elementary graph constructions, or
  polynomial identities over finite fields.  A poor first task requires
  formalising a whole external theory before the stated theorem is even in
  reach.
- The most promising near-term candidates are now #2 and the lower-bound half
  of #9.  Candidate #1 has a compiled Lean bridge and two easy interval
  fragments, but the full interval Sylvester-Schur theorem is essentially the
  unsolved `Erdos961` target and would require a substantial number-theory
  development rather than a direct Mathlib application.  Candidate #3 is
  attractive but more sensitive to polynomial-method API quality.  Candidate #5
  is mathematically short but depends on compact groups/Haar integration or an
  equivalent convex-geometry formalisation.

## 1. Sylvester-Schur Prime Divisor Theorem

### Local Target

Primary target:

```lean
theorem Erdos699.sylvester_schur
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

Related target:

```lean
theorem Erdos961.erdos_961.sylvester_schur
    (k : ℕ) (hk : 0 < k) : Erdos961Prop k k
```

The `Erdos961` theorem states the equivalent interval form: every block of `k`
consecutive integers above `k` contains a number with a prime factor greater
than `k`.

### Informal Proof Sources

- J. J. Sylvester, "On arithmetical series", Messenger of Mathematics 21
  (1892), 1-19 and 87-120.
- I. Schur, "Einige Sätze über Primzahlen mit Anwendung auf
  Irreduzibilitätsfragen", Sitzungsberichte der Preussischen Akademie der
  Wissenschaften, Phys.-Math. Klasse 23 (1929), 1-24.
- P. Erdős, "A theorem of Sylvester and Schur", Journal of the London
  Mathematical Society 9 (1934), 282-288.
  - Oxford page: https://academic.oup.com/jlms/article/s1-9/4/282/891032
  - Public scan: https://combinatorica.hu/~p_erdos/1934-01.pdf
- D. Hanson, "On a theorem of Sylvester and Schur", Canadian Mathematical
  Bulletin 16 (1973), 195-199.  This is useful for bibliographic orientation:
  https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/on-a-theorem-of-sylvester-and-schur/7A13C0E854FA6A796BC3130C05497E18

### Mathematical Route

The clean route is to formalise the interval form first:

```lean
theorem sylvester_schur_interval
    {m k : ℕ} (hk : 0 < k) (hm : k < m) :
    ∃ t p, t ∈ Finset.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ t
```

Then derive the binomial-coefficient form by taking the interval
`n - i + 1, ..., n`.

If `i ≤ n / 2`, then `i < n - i + 1`, so the interval theorem gives a prime
`p > i` dividing one factor of

```text
(n - i + 1) * ... * n.
```

The factorial identity

```text
Nat.choose n i * i! = (n - i + 1) * ... * n
```

then shows that `p ∣ Nat.choose n i`, because `p > i` implies `p ∤ i!`.

### Lean Implementation Plan

1. Add an internal namespace, probably near the eventual task oracle, with
   helper lemmas about products of consecutive naturals:

```lean
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ t in Finset.Ico m (m + k), t
```

2. Prove the product/binomial bridge:

```lean
lemma choose_mul_factorial_eq_consecutiveProduct
    (h : i ≤ n) :
    Nat.choose n i * i.factorial =
      ∏ t in Finset.Icc (n - i + 1) n, t
```

Expected APIs:

- `Nat.choose_mul_factorial_mul_factorial`
- `Finset.prod_Icc_eq_prod_range`
- factorial/product lemmas in `Mathlib/Data/Nat/Choose/Dvd.lean`

3. Prove that a prime above `i` cannot divide `i!`:

```lean
lemma prime_not_dvd_factorial_of_lt
    (hp : p.Prime) (hpi : i < p) : ¬ p ∣ i.factorial
```

Expected APIs:

- `Nat.Prime.dvd_factorial`
- `Nat.Prime.two_le`
- divisibility lemmas for factorial.

4. Prove `Erdos699.sylvester_schur` from `sylvester_schur_interval`.

5. Prove `Erdos961.erdos_961.sylvester_schur` from the same interval theorem by
   unfolding `Nat.smoothNumbers`:

```lean
rw [Nat.mem_smoothNumbers]
```

and using the prime `p > k`.

6. Formalise the interval theorem itself.  This is the only substantial
   mathematical component.  The proof should be transcribed from Erdős 1934,
   but it should be staged as independent lemmas:

- reduction from "no large prime factor in the interval" to "all interval
  terms are `k+1`-smooth";
- squarefree-kernel decomposition of a smooth number, using the existing
  `Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers`;
- the core inequality from Erdős's proof, isolated from the final contradiction;
- small cases, separated so that the main proof does not carry case noise.

### Existing Lean Support

Useful existing files:

- `Mathlib/NumberTheory/SmoothNumbers.lean`
- `Mathlib/Data/Nat/Choose/Factorization.lean`
- `Mathlib/Data/Nat/Choose/Dvd.lean`
- `Mathlib/NumberTheory/Bertrand.lean`

The smooth-number file already has squarefree-kernel and counting lemmas, but
it does not by itself prove Sylvester-Schur.

### Milestones

- M1: prove the binomial/interval bridge without using the hard theorem.
- M2: prove `Erdos699.sylvester_schur` assuming a local
  `sylvester_schur_interval`.
- M3: prove `Erdos961.erdos_961.sylvester_schur` from the same interval theorem.
- M4: formalise the interval theorem from Erdős 1934.
- M5: remove any temporary assumptions and package one or two benchmark tasks.

### Risks

- The short historical proof uses several number-theoretic estimates that need
  to be identified precisely before coding.
- The final theorem statement is elementary, but the interval theorem may still
  be longer than the four already-completed tasks.

### Viability

Low-medium.  The target is elementary and the binomial/interval bridge is
short, but the full interval theorem is not available in Mathlib or as a
proved FormalConjectures theorem.  A compiled local bridge now lives in
`formalizations/erdos699`; it proves the binomial target from an interval
Sylvester-Schur theorem, proves the bridge from `Erdos961Prop`, and covers the
`k = 1` and boundary-Bertrand cases without `sorryAx`.  Completing the problem
requires formalising the full Erdős 1934 interval proof itself, which would
also essentially solve the `erdosproblems-961-sylvester-schur` benchmark.

## 2. Erdős-Turán Sidon Upper Bound

### Local Target

```lean
theorem Erdos329.erdos_329.variants.turan_1941 :
    ∀ (A : Set ℕ), IsSidon A → sidonUpperDensity A ≤ 1
```

Here

```lean
sidonUpperDensity A =
  limsup (fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt N) atTop
```

### Informal Proof Sources

- P. Erdős and P. Turán, "On a problem of Sidon in additive number theory, and
  on some related problems", Journal of the London Mathematical Society 16
  (1941), 212-215.
  - Oxford page: https://academic.oup.com/jlms/article/s1-16/4/212/877908
  - Public scan: https://combinatorica.hu/~p_erdos/1941-01.pdf
- The standard modern statement is that a Sidon set has
  `|A ∩ [1,N]| ≤ sqrt N + O(N^(1/4))`.

### Mathematical Route

Let `A_N = A ∩ Icc 1 N` and `m = |A_N|`.

A Sidon set has unique positive differences: if `a > b`, `c > d`, all four
terms are in `A`, and `a - b = c - d`, then the Sidon property applied to
`a + d = c + b` gives `(a,b) = (c,d)`.

The Erdős-Turán argument improves the naive `sqrt (2N)` bound by averaging
short intervals.

For an integer window length `h`, define

```text
B_u = A ∩ Icc u (u + h - 1).
```

Then:

1. The sum of the cardinalities `|B_u|` over shifts `u` is approximately
   `h * m`, up to boundary terms.
2. The sum of `|B_u| choose 2` is bounded above by
   `h * (h - 1) / 2`, because each positive difference `< h` occurs at most
   once, and a pair at distance `d` appears in exactly `h - d` windows.
3. Cauchy or Jensen gives a lower bound on
   `∑ |B_u| (|B_u| - 1)` in terms of `(∑ |B_u|)^2`.
4. Choosing `h ≈ N^(3/4)` or the standard optimized parameter gives

```text
|A ∩ [1,N]| ≤ sqrt N + O(N^(1/4)).
```

For the benchmark theorem it is enough to prove the weaker asymptotic form:

```lean
∀ ε > 0, ∀ᶠ N in atTop,
  ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt N ≤ 1 + ε
```

and then pass to `limsup`.

### Lean Implementation Plan

1. Prove finite Sidon difference uniqueness:

```lean
lemma IsSidon.eq_of_pos_diff_eq_pos_diff
    (hA : IsSidon A)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A)
    (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (hb₁a₁ : b₁ < a₁) (hb₂a₂ : b₂ < a₂)
    (hdiff : a₁ - b₁ = a₂ - b₂) :
    a₁ = a₂ ∧ b₁ = b₂
```

This will likely need an integer coercion version to avoid natural subtraction
case splits.

2. Define interval-count helper:

```lean
noncomputable def windowCount (A : Set ℕ) (h u : ℕ) : ℕ :=
  (A ∩ Set.Icc u (u + h - 1)).ncard
```

3. Prove the upper bound on pair counts:

```lean
lemma sum_choose_two_windowCount_le
    (hA : IsSidon A) :
    ∑ u in Finset.Icc 1 N, Nat.choose (windowCount A h u) 2 ≤ h * (h - 1) / 2 + boundary
```

It may be cleaner to count triples `(u,a,b)` with `a,b ∈ A`, `u ≤ b < a ≤ u+h-1`,
then map them injectively to a positive difference `a-b`.

4. Prove the lower bound on the same pair count using
`∑ x^2 ≥ (∑ x)^2 / number_of_windows`.  This is over `ℝ`, so cast early.

5. Establish a finite theorem:

```lean
theorem sidon_count_le_sqrt_add_error
    (hA : IsSidon A) :
    ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ Real.sqrt N + C * N ^ (1/4)
```

The exact error term need not match the paper.  Any `o(sqrt N)` error is enough.

6. Convert to `sidonUpperDensity A ≤ 1` using limsup APIs:

- show the normalized finite bound is eventually `≤ 1 + ε`;
- apply `Filter.limsup_le_of_le`;
- discharge positivity and `Real.sqrt` growth lemmas.

### Existing Lean Support

- `FormalConjecturesForMathlib/Combinatorics/Basic.lean` defines `IsSidon`.
- Finset sums, Cauchy-type inequalities, and real square-root asymptotics are
  all standard mathlib material.

### Milestones

- M1: finite positive-difference uniqueness.
- M2: interval/window counting lemma.
- M3: finite Erdős-Turán inequality with explicit error.
- M4: limsup wrapper proving the exact target.

### Risks

- Boundary handling in interval sums can be noisy.
- Natural-number subtraction should be avoided where possible by moving
  differences to `ℤ`.

### Viability

High.  This looks comparable to the completed Erdős formalizations: finite
combinatorics plus an asymptotic wrapper.

## 3. Shakan Large-Gap Dilate Theorem

### Local Target

```lean
theorem Green32.green_32.variants.sh20_general :
    ∀ (p : ℕ), p.Prime →
      ∀ A : Finset (ZMod p), 1 < A.card →
      ∃ c : (ZMod p)ˣ,
        HasGap (c • A) ⌊2 * (p : ℝ) / A.card - 2⌋₊
```

`HasGap A L` means that a translate of `{0,1,...,L-1}` is disjoint from `A`
inside `ZMod p`.

### Informal Proof Sources

- G. Shakan, "A large gap in a dilate of a set", SIAM Journal on Discrete
  Mathematics 34 (2020), 2553-2555.
  - arXiv: https://arxiv.org/abs/2004.14828
  - PDF: https://arxiv.org/pdf/2004.14828
- The proof uses Alon's Combinatorial Nullstellensatz:
  N. Alon, "Combinatorial Nullstellensatz", Combinatorics, Probability and
  Computing 8 (1999), 7-29.

### Mathematical Route

Shakan proves the following.  For `A ⊂ F_p`, `|A| > 1`, there is a nonzero
scalar `d` such that `d*A` has a gap of size at least `2p/|A| - 2`.

The proof is a compact polynomial-method argument:

1. Let `m` be one more than the largest gap among all nonzero dilates.
2. Set `B = {1, ..., m}` and `P = A × B`.
3. By the definition of `m`, every non-horizontal line `y = d*x + t` meets `P`.
4. Define a polynomial

```text
w(d,t) = d * ∏_{a∈A, b∈B} (b + d*a + t).
```

5. This polynomial vanishes on all of `F_p^2`.
6. Apply Combinatorial Nullstellensatz to write `w` modulo
   `(t^p - t, d^p - d)`.
7. Extract the top homogeneous component and set `d = 1`, obtaining a
   one-variable identity

```text
f(t) = ∏_{a∈A} (t+a)^|B| = t^p g(t) + h(t),
```

   with controlled degrees.
8. Differentiate and compare common factors.  Either the degree inequality
   gives the desired bound immediately, or a Wronskian identity forces
   `h = c*g`, contradicting the multiplicities in `f`.
9. Convert the rational bound into the floored natural-number bound in the
   Lean statement.

### Lean Implementation Plan

1. First prove a rational/natural version avoiding floors:

```lean
theorem exists_gap_gt_rational_bound
    (hp : p.Prime) (hA : 1 < A.card) :
    ∃ c : (ZMod p)ˣ, (2 * (p : ℚ) / A.card - 2) ≤ gapLength (c • A)
```

Then derive the exact `⌊...⌋₊` statement.

2. Define a finite-field interval `B m : Finset (ZMod p)` as the image of
`Finset.Icc 1 m`.  Keep a hypothesis `m < p` until the final contradiction.

3. Formalise the line-intersection consequence of "no large gap":

```lean
lemma line_meets_product_of_max_gap
    (hm : m = sup_gap + 1) :
    ∀ d : (ZMod p)ˣ, ∀ t : ZMod p,
      ∃ a ∈ A, ∃ b ∈ B m, b = d * a + t
```

This is the combinatorial heart before polynomial algebra.

4. Build the bivariate polynomial `w` using `MvPolynomial (Fin 2) (ZMod p)`.
Use variables `D = X 0`, `T = X 1`.

5. Use `Mathlib/Combinatorics/Nullstellensatz.lean`.  The available theorem is
close to the needed "vanishes on all field points implies reducible modulo
`X^q-X`" step, but the exact output shape may need a wrapper lemma:

```lean
lemma polynomial_eq_mod_frobenius_vanishing
    (hw : ∀ x : Fin 2 → ZMod p, MvPolynomial.eval x w = 0) :
    ∃ u v, w = (T^p - T) * u + (D^p - D) * v
```

6. Extract homogeneous degree.  If mathlib's homogeneous-component API is too
heavy, define the particular coefficient comparison needed by the paper.

7. Convert to the one-variable polynomial identity.  This may be easier through
`Polynomial` after evaluating `D = 1`.

8. Prove the derivative/multiplicity lemma:

```lean
lemma same_roots_of_wronskian_eq_zero
    {g h : F[X]} (hg : g.natDegree < p) (hh : h.natDegree < p)
    (hW : derivative h * g = h * derivative g) :
    ∃ c, h = C c * g
```

For this task, it is enough to prove the special version used by Shakan,
tracking multiplicities of linear factors.

9. Finish the degree inequality and floor conversion.

### Existing Lean Support

- `ZMod p` field instances under `p.Prime`.
- `Mathlib/Combinatorics/Nullstellensatz.lean`.
- `Polynomial.derivative`, `Polynomial.natDegree`, and divisibility APIs.
- Finset product APIs over finite fields.

### Milestones

- M1: all finite-field combinatorial definitions and gap/dilate lemmas.
- M2: polynomial `w` and proof it vanishes on `F_p^2`.
- M3: Nullstellensatz wrapper.
- M4: one-variable identity and Wronskian/multiplicity contradiction.
- M5: exact floor/cast wrapper matching the GDM target.

### Risks

- Polynomial homogeneous-component manipulation can become longer than the
  paper suggests.
- The floor target mixes `ℝ`, `ℕ`, `ZMod p`, and units.  It should be kept out
  of the hard polynomial proof until the final wrapper.

### Viability

Medium.  The paper proof is only three pages and very structured, but this is
the first candidate in the list that depends seriously on polynomial-method
infrastructure.

## 4. Finite-Field Kakeya Sharp Bound

### Local Target

```lean
theorem Kakeya.kakeya_finite
    {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (K : Finset (Fin n → F)) (hK : IsKakeyaFinite K) :
    card F ^ n / (2 - 1 / card F : ℚ) ^ (n - 1) ≤ K.card
```

### Informal Proof Sources

- Z. Dvir, "On the size of Kakeya sets in finite fields", Journal of the
  American Mathematical Society 22 (2009), 1093-1097.
  - AMS page: https://www.ams.org/journals/jams/2009-22-04/S0894-0347-08-00607-3/
  - arXiv: https://arxiv.org/abs/0803.2336
- B. Bukh and T.-W. Chao, "Sharp density bounds on the finite field Kakeya
  problem", Discrete Analysis 2021:26.
  - journal page: https://discreteanalysisjournal.com/article/30707-sharp-density-bounds-on-the-finite-field-kakeya-problem
  - arXiv: https://arxiv.org/abs/2108.00074

The GDM target is the sharp Bukh-Chao bound, not merely Dvir's earlier
constant-factor Kakeya theorem.

### Mathematical Route

Bukh-Chao prove that every Kakeya set in `F_q^n` has size at least

```text
q^n / (2 - 1/q)^(n-1).
```

The proof refines Dvir's polynomial method:

1. Build a finite-dimensional space of multivariate polynomials whose monomial
   support is a carefully chosen set.
2. If `K` is too small, dimension counting gives a nonzero polynomial in this
   space which vanishes on `K` with prescribed multiplicities.
3. Restrict this polynomial to each line contained in `K`.
4. A univariate polynomial with sufficiently high multiplicity vanishing on all
   field points must vanish identically.
5. This forces the top part or a selected coefficient structure to vanish in
   all directions.
6. A final nonzero-polynomial contradiction proves the lower bound.

### Lean Implementation Plan

This should be split into two possible tasks.

#### Task A: Dvir-Strength Warm-Up

Prove a weaker but still scientifically meaningful theorem:

```lean
theorem kakeya_finite_dvir_bound
    {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (K : Finset (Fin n → F)) (hK : IsKakeyaFinite K) :
    ∃ c : ℚ, 0 < c ∧ c * (Fintype.card F : ℚ) ^ n ≤ K.card
```

or a concrete bound such as `q^n / n!`.

This establishes the polynomial-method infrastructure without Hasse derivative
multiplicities.

#### Task B: Exact Bukh-Chao Target

1. Define monomial index sets as `Fin n →₀ ℕ` with total-degree constraints.
2. Define the polynomial space as a submodule of `MvPolynomial (Fin n) F`.
3. Formalise dimension counts by constructing explicit bases indexed by the
   monomial finsets.
4. Add Hasse derivatives for multivariate polynomials:

```lean
def hasseDeriv (α : Fin n →₀ ℕ) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F
```

5. Define multiplicity vanishing at a point by vanishing of all Hasse
   derivatives below a given order.
6. Prove the univariate restriction lemma:

```lean
lemma polynomial_zero_of_many_multiplicity_roots
    (f : F[X]) :
    (sum_of_multiplicities_over_univ > f.natDegree) → f = 0
```

7. Prove that restriction to a Kakeya line transfers multiplicity vanishing from
   `K` to the line polynomial.
8. Complete Bukh-Chao's dimension inequality and translate it to the rational
   inequality in the theorem statement.

### Existing Lean Support

- `MvPolynomial` and `Finsupp` monomial APIs.
- `Mathlib/Combinatorics/Nullstellensatz.lean`.
- Polynomial degree and root-count lemmas.

Missing or likely incomplete:

- multivariate Hasse derivative infrastructure;
- multiplicity-vanishing API for finite-field polynomial method;
- dimension counts for custom monomial spaces.

### Milestones

- M1: Dvir-style polynomial vanishing lemma over finite fields.
- M2: weak finite-field Kakeya theorem.
- M3: Hasse derivative and multiplicity API.
- M4: Bukh-Chao dimension count.
- M5: exact theorem statement.

### Risks

- The exact target is likely much harder than the four completed benchmark
  tasks.
- Proving the sharp bound first is not advisable.  A Dvir-bound task would make
  a better benchmark contribution.

### Viability

Low-medium for the exact GDM theorem.  Medium for a weaker Dvir theorem if the
benchmark accepts a nearby solved statement.

## 5. Finite-Dimensional Banach-Mazur Rotation Theorem

### Local Target

```lean
theorem Arxiv.«math.0110202».banach_mazur_rotation_problem.finite_dimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [IsPretransitive (E ≃ₗᵢ[ℝ] E) (sphere (0 : E) 1)] :
    InnerProductSpaceable E
```

`InnerProductSpaceable E` is the parallelogram-law predicate from mathlib.

### Informal Proof Sources

- B. Randrianantoanina, "A note on Banach-Mazur problem", Glasgow Mathematical
  Journal 45 (2003), 193-197.
  - arXiv: https://arxiv.org/abs/math/0110202
- Survey/background:
  - A. Avilés et al., "On Mazur rotations problem and its multidimensional
    versions", arXiv:2012.08344, https://arxiv.org/abs/2012.08344
  - Ferenczi lecture notes, which include the compact-group averaging proof:
    https://banach24.unizar.es/talks/ferenczi1.pdf
- A standard alternative is the John ellipsoid proof: a transitive norm has an
  invariant maximal ellipsoid, hence the norm ball must be Euclidean.

### Mathematical Route

The compact-group averaging proof is probably better for Lean than John
ellipsoids.

1. In finite dimension, choose some auxiliary inner product on `E`.
2. The linear isometry group `G = E ≃ₗᵢ[ℝ] E` is compact.
3. Average the auxiliary inner product over `G` using Haar probability measure:

```text
[x,y] = ∫ T : G, <T x, T y> dT.
```

4. This averaged form is an inner product and is invariant under every
   `T : G`.
5. Choose `x₀` on the unit sphere and normalise the auxiliary inner product so
   that the averaged Hilbert norm agrees with the original norm at `x₀`.
6. By transitivity of `G` on the original unit sphere, agreement at `x₀` implies
   agreement on every original unit vector.
7. By homogeneity, the original norm equals the Hilbert norm everywhere.
8. Therefore the parallelogram identity holds.

### Lean Implementation Plan

1. Handle the zero-dimensional/subsingleton case separately.  The unit sphere
   may be empty, and `IsPretransitive` can be vacuous.

2. Produce an auxiliary inner product on a finite-dimensional real vector
   space.  Possible route:

```lean
noncomputable def auxiliaryInner
    [FiniteDimensional ℝ E] : InnerProductSpace ℝ E := ...
```

This may already be available via `FiniteDimensional` and a chosen basis.  If
not, construct a linear equivalence to `Fin m → ℝ` and pull back the Euclidean
inner product.

3. Establish topology/compactness for the isometry group.  Needed pieces:

- `E ≃ₗᵢ[ℝ] E` as a topological group;
- compactness in finite dimension;
- Haar probability measure on compact groups.

4. Define the averaged bilinear form.  Instead of constructing an
`InnerProductSpace` structure immediately, prove the parallelogram identity by
using the averaged squared norm:

```lean
def avgSqNorm (x : E) : ℝ := ∫ T, ‖T x‖₂^2
```

where `‖·‖₂` is the auxiliary Hilbert norm.

5. Prove invariance:

```lean
lemma avgSqNorm_apply_isometry (T : E ≃ₗᵢ[ℝ] E) :
    avgSqNorm (T x) = avgSqNorm x
```

6. Use transitivity on `sphere 0 1` to prove that `avgSqNorm` is constant on
the original unit sphere.

7. Scale the auxiliary inner product so that this constant is `1`.  Then prove
`avgSqNorm x = ‖x‖^2` for all `x`, using `x = ‖x‖ • u` for `u` on the sphere.

8. Conclude the parallelogram law by applying the parallelogram law for the
averaged Hilbert norm and rewriting it as the original norm.

### Existing Lean Support

- `Mathlib/Analysis/InnerProductSpace/OfNorm.lean` defines
  `InnerProductSpaceable`.
- Finite-dimensional normed-space compactness APIs exist broadly in mathlib.
- Haar measure APIs exist in mathlib, but their exact fit for `E ≃ₗᵢ[ℝ] E`
  must be checked early.

### Milestones

- M1: auxiliary inner product on arbitrary finite-dimensional real normed
  spaces.
- M2: compact/topological-group/Haar setup for linear isometries.
- M3: averaged norm invariance.
- M4: transitivity implies original norm equals averaged Hilbert norm.
- M5: produce `InnerProductSpaceable`.

### Risks

- If `E ≃ₗᵢ[ℝ] E` lacks convenient Haar/compact-group instances, this becomes a
  library project.
- John ellipsoid would avoid Haar measure but requires convex-body volume and
  maximal ellipsoid APIs, which are likely worse.

### Viability

Medium.  The proof is conceptually short, but the library dependencies are
substantial.

## 6. Zariski Cancellation in Dimension One

### Local Target

```lean
theorem Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_one
    {k : Type*} [Field k] : IsCancellative k k[X]
```

Here `IsCancellative k A` means that for every finitely generated `k`-algebra
`B`, if `A[X] ≃ₐ[k] B[X]`, then `A ≃ₐ[k] B`.

### Informal Proof Sources

- S. S. Abhyankar, P. Eakin, and W. J. Heinzer, cancellation for one-dimensional
  affine domains; cited in Gupta's ICM survey.
- N. Gupta, "The Zariski Cancellation Problem and related problems in Affine
  Algebraic Geometry", Proceedings ICM 2022.
  - arXiv: https://arxiv.org/abs/2208.14736
  - PDF: https://arxiv.org/pdf/2208.14736

Gupta's survey states the one-dimensional result in the form that a domain of
transcendence degree one over a field is cancellative, and also mentions the
stronger Abhyankar-Eakin-Heinzer theorem for `R[X]` over a UFD `R`.

### Mathematical Route

The Lean statement is algebraic:

```text
k[X][T] ≃ₐ[k] B[T]  implies  k[X] ≃ₐ[k] B.
```

A proof route following the literature would likely be:

1. Show `B[T]` is a domain because it is isomorphic to `k[X][T]`.
2. Deduce `B` is a domain.
3. Deduce `B` is an affine `k`-domain of transcendence degree one.
4. Use the Abhyankar-Eakin-Heinzer theorem:

```text
If A is a one-dimensional affine k-domain and A[T] ≃ k[X,Y],
then A ≃ k[X].
```

5. Convert this theorem into the GDM `IsCancellative` statement.

### Lean Implementation Plan

This target should not be attempted directly unless we are willing to formalise
or import a substantial algebraic-geometry theorem.

Possible staged plan:

1. Prove easy algebraic consequences of an isomorphism:

```lean
lemma domain_of_polynomial_algEquiv_polynomial
    (e : k[X][T] ≃ₐ[k] B[T]) : IsDomain B
```

2. Prove finite-type and algebraic-independence transfer lemmas.

3. Define or reuse transcendence degree for finitely generated domains.

4. State an internal theorem matching AEH as a temporary milestone:

```lean
theorem abhyankar_eakin_heinzer_dim_one
    {B : Type*} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    [IsDomain B]
    (e : k[X][T] ≃ₐ[k] B[T]) :
    Nonempty (k[X] ≃ₐ[k] B)
```

5. Investigate whether a proof can be built from existing mathlib APIs:

- UFD transfer from polynomial rings;
- units of polynomial rings;
- Krull dimension;
- normal affine curves;
- characterisation of `A¹`.

6. If not, treat AEH as the actual theorem to formalise, not this cancellation
wrapper.

### Existing Lean Support

Mathlib has strong polynomial and finite-type algebra APIs, but the exact
one-dimensional affine-domain cancellation theorem is not expected to be
available.

### Milestones

- M1: sanity-check the exact GDM statement: no domain assumption on `B`, so
  domain must be derived.
- M2: prove the wrapper from a locally stated AEH theorem.
- M3: decide whether formalising AEH is feasible.
- M4: only then attempt the full proof.

### Risks

- This is not a short commutative-algebra exercise.  The load-bearing theorem is
  much larger than the benchmark target suggests.
- The formal statement may need supporting definitions not already developed in
  mathlib, especially transcendence degree and curve characterisations.

### Viability

Low for a near-term gold task.  Good as a long-term algebraic-geometry library
project.

## 7. Triangle-Free Degree-Sequence Embedding Theorem

### Local Target

```lean
theorem SimpleGraph.theorem2
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected)
    (h : G.CliqueFree 3) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β)
      (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧ degreeSequenceMultiplicity H = 3
```

This lives in
`FormalConjectures/Paper/DegreeSequencesTriangleFree.lean`.

### Informal Proof Sources

- P. Erdős, S. Fajtlowicz, and W. Staton, "Degree sequences in triangle-free
  graphs", Discrete Mathematics 92 (1991), 85-88.
  - ScienceDirect page:
    https://www.sciencedirect.com/science/article/pii/0012365X91902698
  - DBLP:
    https://dblp.org/rec/journals/dm/ErdosFS91

The FormalConjectures file already mirrors the paper structure: Lemmas 1-4,
Theorem 1, and Theorem 2.

### Mathematical Route

The paper studies `f(G)`, the maximum multiplicity of a degree in the degree
sequence of `G`.  The target says every connected triangle-free graph embeds as
an induced subgraph of a triangle-free graph with `f = 3`.

The local Lean file suggests the proof pipeline:

1. Lemma 1: monotone sequences with no three equal terms grow by at least one
   every two steps.  Parts (a) and (b) are already proved.
2. Lemma 2: block-sum inequalities for such degree sequences.  These are
   currently `sorry`.
3. Theorem 1: a connected triangle-free graph with `f = 2` is bipartite, has
   minimum degree `1`, and has a compact degree sequence.
4. Lemma 3: construct, for every `n > 0`, a bipartite graph on `8n` vertices
   with minimum degree `n+1` and `f = 3`.
5. Lemma 4: given a connected triangle-free graph `G` and a vertex `v`, build a
   triangle-free supergraph `H` that raises the degree of `v` by one, leaves the
   other old degrees unchanged, and whose new part has `f = 3` and large
   minimum degree.
6. Theorem 2 follows by iterating Lemma 4 enough times to adjust repeated old
   degrees while preserving triangle-freeness.

### Lean Implementation Plan

1. Complete Lemma 2 first.  This is pure `ℕ`/Finset arithmetic over monotone
   sequences:

```lean
lemma lemma2_a ... :
  2 * n * n ≤
    ∑ i ∈ .Icc (2*n+1) (4*n), d i -
      ∑ i ∈ .Icc 1 (2*n), d i
```

Expected tactics: `nlinarith`, `omega`, `Finset.sum_le_sum`,
`Finset.sum_Icc_eq_sum_range`, and the already-proved `lemma1_b`.

2. Audit definitions:

- `degreeSequence G` is a sorted list of degrees.
- `degreeSequenceMultiplicity G` is the maximum list count.
- `HasCompactdegreeSequence G` is stated over `List.getD`.

It may be worth proving list lemmas about sorted degree sequences separately.

3. Prove Theorem 1.  This is the first graph-theoretic hard point:

- `f = 2` means no degree occurs three times.
- Triangle-free plus connected constrains neighborhoods.
- Lemma 2 likely gives a contradiction unless the graph is bipartite/min-degree
  one/compact.

4. Formalise Lemma 3 by an explicit construction.  The paper's construction
should be translated into a type such as

```lean
β := Fin 8 × Fin n
```

or a sum of eight parts each of size `n`.  Define adjacency by part indices and
cyclic shifts.  Prove:

- bipartite;
- triangle-free follows from bipartite;
- minimum degree is `n+1`;
- the degree sequence has maximum multiplicity `3`.

5. Formalise Lemma 4 as a graph attachment gadget:

- take disjoint union of `G` and a Lemma 3 graph `J`;
- connect the distinguished old vertex `v` to a carefully chosen independent
  subset of `J`;
- preserve triangle-freeness by ensuring the new neighbor set is independent;
- compute old degrees and bound new-part minimum degree.

6. Prove Theorem 2 by finite induction over vertices and degree deficits.  A
   good measure is the sum over degree classes of the excess multiplicity above
   `3`, or a target list of vertices whose degrees need to be raised.

### Existing Lean Support

- `SimpleGraph.CliqueFree`, `SimpleGraph.IsBipartite`, `SimpleGraph.minDegree`,
  graph embeddings, induced graphs, and graph maps are available.
- `degreeSequenceMultiplicity` is already defined in
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/GraphConjectures/Definitions.lean`.

### Milestones

- M1: finish Lemma 2 arithmetic.
- M2: prove Lemma 3 explicit gadget.
- M3: prove Lemma 4 attachment gadget.
- M4: prove Theorem 2 by iteration.
- M5: decide whether Theorem 1 is needed for Theorem 2 or only for surrounding
  results.  If Theorem 2 can be proved from Lemmas 3 and 4 alone, skip Theorem 1.

### Risks

- The graph construction may be concise on paper but verbose in Lean.
- Degree-sequence multiplicity via sorted lists can be awkward.  It may be
  useful to prove an equivalent finset/fiber-count characterisation first.

### Viability

Medium.  This is a plausible benchmark if the paper's constructions are simple
enough, but it may be longer than the completed Erdős tasks.

## 8. Weak Freiman/Erdős 245 Sumset Lower Bound

### Local Target

```lean
theorem Erdos245.erdos_245.variants.two
    (A : Set ℕ) (h_inf : A.Infinite)
    (hf : atTop.Tendsto
      (fun N ↦ ((A ∩ Icc 1 ⌊N⌋₊).ncard : ℝ) / N) (𝓝 0)) :
    2 ≤ atTop.limsup
      fun N : ℝ ↦
        (((A + A) ∩ Icc 1 ⌊N⌋₊).ncard : EReal)
          / (A ∩ Icc 1 ⌊N⌋₊).ncard
```

The full Erdős 245 target asks for `3`, proved by Freiman.  This variant asks
only for `2`.

### Informal Proof Sources

- G. A. Freiman, "Foundations of a Structural Theory of Set Addition",
  Translations of Mathematical Monographs 37, AMS, 1973.
  - AMS book page: https://bookstore.ams.org/MMONO/37
  - Open Library page:
    https://openlibrary.org/works/OL6320649W/Foundations_of_a_structural_theory_of_set_addition
- Erdős Problems #245:
  https://www.erdosproblems.com/245

### Mathematical Route

The full theorem is a sparse-set sumset lower bound:

```text
limsup |(A+A)∩[1,N]| / |A∩[1,N]| ≥ 3.
```

The weak `2` target should be substantially easier, but still needs care
because the denominator counts `A` up to `N`, while the obvious finite estimate
`|X+X| ≥ 2|X|-1` only controls sums of a finite truncation `X`.

Possible proof route:

1. Let `A(N) = |A ∩ [1,N]|`.
2. For finite nonempty `X ⊂ ℕ`, prove

```text
|X + X| ≥ 2|X| - 1.
```

This follows by taking the ordered enumeration
`x₁ < ... < x_m`; the sums

```text
x₁+x₁, x₁+x₂, ..., x₁+x_m, x₂+x_m, ..., x_m+x_m
```

are strictly increasing.

3. Apply this to carefully chosen finite truncations of `A`, while using the
zero-density hypothesis to choose scales where the truncation denominator does
not jump too much.
4. Convert the finite estimates into the `EReal` limsup statement.

If the scale-selection lemma becomes difficult, an alternative is to formalise
the relevant weak part of Freiman's proof and then specialise to the constant
`2`.

### Lean Implementation Plan

1. Prove finite ordered-sumset lower bound:

```lean
lemma two_mul_card_sub_one_le_card_sumset
    (X : Finset ℕ) (hX : X.Nonempty) :
    2 * X.card - 1 ≤ (X + X).card
```

A direct injection from `Fin (2*m-1)` into `X+X` using sorted elements may be
cleaner than invoking additive-combinatorics library theorems.

2. Develop truncation notation:

```lean
def countA (A : Set ℕ) (N : ℕ) : ℕ := (A ∩ Set.Icc 1 N).ncard
def countAA (A : Set ℕ) (N : ℕ) : ℕ := ((A + A) ∩ Set.Icc 1 N).ncard
```

3. Prove an infinite-set enumeration lemma:

```lean
lemma exists_strictMono_enumeration (hA : A.Infinite) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Set.range a = A
```

or use existing `Set.Infinite` APIs to avoid constructing a full enumeration.

4. Prove the scale-selection lemma from `A(N) = o(N)`.  A useful target:

```lean
lemma exists_good_scales_of_zero_density
    (h_inf : A.Infinite)
    (hf : Tendsto (fun N => (countA A N : ℝ) / N) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ᶠ N in atTop,
      (countA A N : ℝ) ≤ (1 + ε) * countA A (N / 2)
```

This exact statement may need adjustment.  The proof should be worked out
informally before coding.

5. Combine with the finite lower bound on
`X = A ∩ [1, N/2]`, whose double sum lies inside `[1,N]`.

6. Convert from `ℝ` inequalities to `EReal` limsup.  Keep this as a final
wrapper:

```lean
have h_eventual : ∀ ε > 0, ∃ᶠ N in atTop, (2 - ε : EReal) ≤ ratio N
exact le_limsup_of_frequently_le ...
```

### Existing Lean Support

- Pointwise set addition via `open scoped Pointwise`.
- EReal and limsup APIs are available but can be syntactically heavy.
- Additive-combinatorics APIs may already contain a finite `|A+B|` lower bound
  in linearly ordered cancellative settings; this should be checked before
  hand-proving.

### Milestones

- M1: finite `|X+X| ≥ 2|X|-1`.
- M2: scale-selection lemma from zero density.
- M3: real-valued limsup statement.
- M4: exact `EReal` theorem.

### Risks

- The weak-looking scale-selection step is the actual mathematical issue.
- The target uses `N : ℝ` with `⌊N⌋₊`, which adds floor/cast noise.

### Viability

Medium-low until the scale-selection proof is written cleanly.  If that lemma
is simple, the rest is routine.

## 9. Ramsey `R(5,5)` Bounds

### Local Targets

Lower bound:

```lean
theorem RamseyNumbers.ramsey_number_five_five_lower_bound :
    ∃ G : SimpleGraph (Fin 42), G.CliqueFree 5 ∧ (Gᶜ).CliqueFree 5
```

Upper bound:

```lean
theorem RamseyNumbers.ramsey_number_five_five_upper_bound :
    IsGraphRamsey 46 5 5
```

### Informal Proof Sources

- G. Exoo, "A lower bound for R(5,5)", Journal of Graph Theory 13 (1989),
  97-98.  This gives a graph on 42 vertices with no clique or independent set
  of size 5.
  - DOI metadata summary:
    https://researchr.org/publication/Exoo89-0
- V. Angeltveit and B. D. McKay, "`R(5,5) ≤ 46`", arXiv:2409.15709.  The
  theorem was later published in Journal of Graph Theory in 2026.
  - arXiv: https://arxiv.org/abs/2409.15709
- S. P. Radziszowski, "Small Ramsey Numbers", Electronic Journal of
  Combinatorics, Dynamic Survey DS1:
  https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1

### Mathematical Route

These two targets are very different.

#### Lower Bound

The lower bound is a finite certificate:

1. Define Exoo's 42-vertex graph explicitly.
2. Check every 5-subset is not a clique.
3. Check every 5-subset is not an independent set.

This is a good Lean benchmark because the proof is small in mathematics but
requires careful finite-data representation.

#### Upper Bound

The upper bound is a large computer-assisted proof.  Angeltveit-McKay combine
linear programming with a large case analysis.  A Lean proof would need either:

- a formally verified checker for their certificates; or
- a complete reimplementation of the exhaustive search with a proof that the
  search is complete.

That is a much larger project.

### Lean Implementation Plan

#### Lower Bound Plan

1. Encode Exoo's graph.  Possible representations:

```lean
def exooAdj : Fin 42 → Fin 42 → Bool := ...
def exooGraph : SimpleGraph (Fin 42) := SimpleGraph.fromRel ...
```

Use a compact adjacency bitset or cyclic construction if Exoo's graph has one.

2. Prove symmetry and irreflexivity by `decide`.

3. Prove clique-free by exhaustive checking of 5-subsets:

```lean
lemma exooGraph_cliqueFree_five : exooGraph.CliqueFree 5 := by
  native_decide
```

This may be too slow if stated naively.  If so, create a verified certificate:

- enumerate all 5-subsets;
- for each subset provide one missing edge;
- check the certificate by `decide`.

4. Prove complement clique-free similarly.

5. Package the theorem.

#### Upper Bound Plan

1. Do not attempt first.
2. If attempted, define a generic Ramsey-certificate checker:

```lean
structure RamseyUpperCertificate (n k l : ℕ) where
  cases : ...
  lpCertificates : ...
  completenessProof : ...
```

3. Translate Angeltveit-McKay's computational artifacts into this format.
4. Verify the checker in Lean.

### Existing Lean Support

- `SimpleGraph.CliqueFree`.
- `SimpleGraph.compl`.
- `Finset.powersetCard`.
- `native_decide` for finite propositions.

### Milestones

- M1: lower-bound graph encoded.
- M2: certificate checker for clique-free/complement-clique-free.
- M3: lower-bound theorem.
- M4: only separately, investigate upper-bound certificate availability.

### Risks

- A raw `native_decide` over all 5-subsets might compile slowly but is still
  plausible for 42 vertices.
- The upper bound is not comparable to the completed gold tasks.

### Viability

Lower bound: high.  Upper bound: low.  As a benchmark, the lower-bound target is
the right one.

## 10. Erdős Sumset Conjecture

### Local Target

```lean
theorem Erdos109.erdos_109
    (A : Set ℕ) (h : A.upperDensity > 0) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A
```

### Informal Proof Sources

- J. Moreira, F. K. Richter, and D. Robertson, "A proof of a sumset conjecture
  of Erdős", Annals of Mathematics 189 (2019), 605-652.
  - arXiv: https://arxiv.org/abs/1803.00498
  - Warwick repository:
    https://wrap.warwick.ac.uk/id/eprint/127282/
- B. Host, "A short proof of a conjecture of Erdős proved by Moreira, Richter
  and Robertson", Discrete Analysis 2019:19.
  - journal page:
    https://discreteanalysisjournal.com/article/11129-a-short-proof-of-a-conjecture-of-erdos-proved-by-moreira-richter-and-robertson
  - arXiv/html conversion:
    https://ar5iv.org/abs/1904.09952v3

Host's proof is shorter and likely the better formalisation blueprint, but it
uses classical ergodic theory.

### Mathematical Route

The GDM theorem uses natural upper density.  Host's paper uses upper uniform
density / Følner intervals.  The first bridge is:

```text
positive natural upper density ⇒ positive upper Banach density.
```

Then the Host proof proceeds roughly as follows:

1. Encode `A` as a point in the shift space `{0,1}^ℤ` or `{0,1}^ℕ`.
2. Take an orbit closure and an invariant measure generated by intervals where
   `A` has positive density.
3. Use ergodic decomposition to obtain an ergodic component where the cylinder
   corresponding to membership in `A` has positive measure.
4. Use the Kronecker factor of this ergodic system.
5. Construct a joining with enough recurrence.
6. Apply a combinatorial selection lemma to build infinite sets `B` and `C`
   with `B+C ⊆ A`.

### Lean Implementation Plan

This is a long-term plan, not a near-term benchmark plan.

1. Define upper Banach density for subsets of `ℕ`:

```lean
noncomputable def upperBanachDensity (A : Set ℕ) : ℝ := ...
```

2. Prove:

```lean
lemma upperDensity_pos_imp_upperBanachDensity_pos
    (h : A.upperDensity > 0) :
    upperBanachDensity A > 0
```

3. Build the symbolic dynamical system:

- alphabet `Bool` or `Fin 2`;
- product topology on sequences;
- shift map;
- point `x_A`;
- cylinder set `U = {x | x 0 = true}`.

4. Formalise orbit-closure compactness and Krylov-Bogolyubov-style invariant
   measure extraction from empirical measures along intervals.

5. Add ergodic decomposition or avoid it by using an existing ergodic component
   theorem if mathlib has one.

6. Formalise the Kronecker factor step.  This is the largest missing block:

- measure-preserving systems;
- compact abelian group rotations;
- factor maps;
- generic points along Følner sequences.

7. Prove Host's Theorem 3, the combinatorial selection lemma, separately.  This
   part is set-theoretic and may be independently feasible:

```lean
lemma host_selection
    (h_recurrence : ...)
    : ∃ B C, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A
```

8. Assemble the dynamical proof.

### Existing Lean Support

Mathlib has topology, measure theory, compact spaces, and some ergodic-theory
infrastructure, but the exact Host proof would need significant new
development around symbolic systems, Følner genericity, joinings, and
Kronecker factors.

### Milestones

- M1: density bridge and symbolic shift definitions.
- M2: invariant measure from positive density.
- M3: Host's combinatorial selection lemma.
- M4: ergodic/Kronecker/joining machinery.
- M5: final theorem.

### Risks

- This is likely much larger than the four completed tasks.
- The density notion in the GDM theorem is weaker-looking than Host's working
  definition, so the density bridge must be checked carefully.

### Viability

Low for a near-term gold task.  Scientifically important and load-bearing, but
not a first-pass candidate.

## Recommended Review Order

For the next discussion, I would review the top candidates in this order:

1. `Erdos329.erdos_329.variants.turan_1941`
2. `Erdos699.sylvester_schur`
3. `RamseyNumbers.ramsey_number_five_five_lower_bound`
4. `Green32.green_32.variants.sh20_general`
5. `SimpleGraph.theorem2`
6. `banach_mazur_rotation_problem.finite_dimensional`

The remaining four are valuable but appear less suitable as immediate
benchmarks:

- exact finite-field Kakeya is probably too much, though a Dvir-bound variant
  may be excellent;
- Zariski cancellation dimension one hides a large theorem;
- Erdős 245 needs a clean scale-selection/Freiman plan before committing;
- Erdős 109 is a serious ergodic-theory project.
