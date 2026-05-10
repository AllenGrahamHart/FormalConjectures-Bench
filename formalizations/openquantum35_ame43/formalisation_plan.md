# Open Quantum Problem 35, AME(4,3) - Lean formalisation plan

This is a Codex-oriented plan for formalising the benchmark theorem

```lean
theorem OpenQuantumProblem35.ame_4_3_exists : ExistsAME 4 3
```

from `FormalConjectures/OpenQuantumProblems/35.lean`.

The theorem states that there exists an absolutely maximally entangled state of
four qutrits.  In the benchmark source, this theorem is currently marked as a
source-backed solved statement but has no Lean proof:

```lean
/-- Source-backed benchmark statement: an `AME(4,3)` state exists;
    see Helwig et al. (2012) and Goyeneche et al. (2015). -/
@[category research solved, AMS 5 15 81 94]
theorem ame_4_3_exists : ExistsAME 4 3 := by
  sorry
```

The generated v2 task already exists at
`tasks-v2/openquantumproblems-35-ame-4-3-exists`, with
`benchmark_bucket = "informal_proof"` and `oracle_status = "none"`.

Current local implementation status:

- `formalizations/openquantum35_ame43` contains a standalone Lake project.
- The proved theorem is
  `OpenQuantumProblem35.ame_4_3_exists_formal : ExistsAME 4 3`.
- The project builds with `lake build`.
- The formalization file contains no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, or `native_decide`.
- `#print axioms OpenQuantumProblem35.ame_4_3_exists_formal` reports only
  `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`.

## 0. Sources and status

Primary informal sources:

- Open Quantum Problems, Problem 35:
  `https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states`
- W. Helwig, W. Cui, A. Riera, J. I. Latorre, and H.-K. Lo,
  "Absolute Maximal Entanglement and Quantum Secret Sharing",
  Phys. Rev. A 86, 052335 (2012), arXiv:1204.2289.
- D. Goyeneche, D. Alsina, J. I. Latorre, A. Riera, and K. Zyczkowski,
  "Absolutely Maximally Entangled states, combinatorial designs and
  multi-unitary matrices", Phys. Rev. A 92, 032316 (2015),
  arXiv:1506.08857.

The concrete construction used by Goyeneche et al. is

```text
|Omega_4,3> = (1/3) * sum_{i,j in {0,1,2}}
  |i> |j> |i+j> |i+2j>,
```

where the additions are modulo 3.  The paper states that every two-qutrit
reduction is the maximally mixed matrix `I_9 / 9`.

Local proof search status:

- The local `manifest/v2_candidates.json` entry has `formal_proofs: []`.
- The current upstream Formal Conjectures source still has
  `ame_4_3_exists := by sorry`.
- GitHub code search for exact Lean names such as `ame_4_3_exists`,
  `OpenQuantumProblem35.ame_4_3_exists`, and `ExistsAME 4 3` did not reveal an
  external formal proof beyond the source theorem itself.

This does not prove that no private Lean proof exists, but it is enough evidence
to treat this as an unsolved local formalisation task.

## 1. Target theorem and non-goals

The target theorem is exactly the existing benchmark theorem:

```lean
namespace OpenQuantumProblem35

theorem ame_4_3_exists : ExistsAME 4 3 := by
  ...

end OpenQuantumProblem35
```

Use the source definitions already present in `OpenQuantumProblems/35.lean`:

```lean
abbrev Config (n d : Nat) := Fin n -> Fin d
abbrev StateVector (n d : Nat) := EuclideanSpace Complex (Config n d)

def IsNormalized {n d : Nat} (psi : StateVector n d) : Prop :=
  norm psi = 1

noncomputable def reducedDensityFirst
    {n d : Nat} (m : Nat) (hm : m <= n) (psi : StateVector n d) :
    Matrix (Config m d) (Config m d) Complex := ...

def HasMaximallyMixedFirstReduction {n d : Nat} (m : Nat) (hm : m <= n)
    (psi : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm psi = maximallyMixed m d

def IsAME {n d : Nat} (psi : StateVector n d) : Prop :=
  IsNormalized psi /\
    forall pi : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState pi psi)

def ExistsAME (n d : Nat) : Prop :=
  exists psi : StateVector n d, IsAME (n := n) (d := d) psi
```

Non-goals:

1. Do not formalise the full classification of `AME(n,d)` states.
2. Do not prove that the benchmark definition is equivalent to every standard
   physics definition using von Neumann entropy.  The source has already chosen
   a reduced-density-matrix definition.
3. Do not formalise uniqueness or local-unitary equivalence of `AME(4,3)`.
4. Do not formalise `AME(4,d)` for all prime `d > 2`.
5. Do not prove the harder adjacent statements such as `ame_4_2_not_exists`,
   `ame_5_2_exists`, or `ame_6_2_exists`.

The proof should contain no `axiom`, no `constant` standing for an unproved
theorem, and no remaining `sorry`.

## 2. Mathematical proof

Let `F_3 = {0,1,2}` with arithmetic modulo 3.  Define the support code

```text
C = { (i, j, i+j, i+2j) : i,j in F_3 } subset F_3^4.
```

Define the state

```text
Omega(x) = 1/3   if x in C,
           0     otherwise.
```

There are exactly 9 support words.  Hence

```text
sum_x |Omega(x)|^2 = 9 * |1/3|^2 = 1.
```

So `Omega` is normalized.

The key AME property is that the projection of `C` onto any two coordinates is
a bijection `C -> F_3^2`.  Indeed the four coordinate functions are the linear
forms

```text
i,   j,   i+j,   i+2j.
```

Any two of these linear forms are linearly independent over `F_3`, so the
chosen two coordinates determine the two hidden parameters `i,j`, and hence
determine the remaining two coordinates.

It follows that, for any bipartition into two parties and two parties, the state
is a uniform superposition over the graph of a bijection

```text
completion : Config 2 3 -> Config 2 3.
```

The benchmark file already has exactly the reusable lemma needed for this:

```lean
lemma hasMaximallyMixedFirstReduction_of_completion
    {n d m : Nat} (hm : m <= n)
    (psi : StateVector n d)
    (completion : Config m d -> Config (n - m) d)
    (coeff : Complex)
    (hpsi : forall x z,
      psi (combineFirst (n := n) (d := d) m hm x z) =
        if z = completion x then coeff else 0)
    (hinj : Function.Injective completion)
    (hnorm : coeff * star coeff =
      ((Fintype.card (Config m d) : Complex)^-1)) :
    HasMaximallyMixedFirstReduction (n := n) (d := d) m hm psi
```

The formal task is therefore mostly finite combinatorics and indexing:

1. Define the `AME(4,3)` state.
2. Prove it is normalized.
3. Prove every two-coordinate projection of the support code is bijective.
4. Use the existing completion lemma for each permutation of the four parties.
5. Package the witness into `ExistsAME 4 3`.

## 3. Recommended Lean structure

The theorem can be proved directly inside the target file.  If developing in a
separate project first, a small file layout would be:

```text
OpenQuantum35AME43/
  Basic.lean          -- finite qutrit helpers and the support code
  Normalization.lean  -- norm of the uniform 9-word state
  Projections.lean    -- every two-coordinate projection is bijective
  Reductions.lean     -- completion functions and reduced-density proof
  Main.lean           -- final theorem
```

For the generated tb task, this would later be compressed back into
`FormalConjecturesBench/Target.lean`, because the task expects the proof in the
single target file.

## 4. Concrete Lean definitions

### 4.1 Support words

Use `Fin 3` for qutrit values.  `Fin` has modular arithmetic, but if the API is
awkward, define small explicit helpers and prove by finite case analysis.

Suggested definitions:

```lean
namespace OpenQuantumProblem35

noncomputable section

def qadd (a b : Fin 3) : Fin 3 :=
  a + b

def qdouble (a : Fin 3) : Fin 3 :=
  a + a

def qutritPairToConfig (p : Prod (Fin 3) (Fin 3)) : Config 2 3 :=
  fun k =>
    if h : k = 0 then p.1 else p.2

def configToQutritPair (x : Config 2 3) : Prod (Fin 3) (Fin 3) :=
  (x 0, x 1)

def omega43Word (i j : Fin 3) : Config 4 3 :=
  fun k =>
    if k = 0 then i
    else if k = 1 then j
    else if k = 2 then i + j
    else i + j + j

def IsOmega43Word (w : Config 4 3) : Prop :=
  exists i j : Fin 3, w = omega43Word i j
```

The snippets use `Prod (Fin 3) (Fin 3)` rather than the Unicode product
notation so that the plan stays mostly ASCII.  In actual Lean code,
`Fin 3 × Fin 3` is also fine.

Useful simp lemmas:

```lean
@[simp] lemma omega43Word_zero (i j : Fin 3) :
    omega43Word i j 0 = i := ...

@[simp] lemma omega43Word_one (i j : Fin 3) :
    omega43Word i j 1 = j := ...

@[simp] lemma omega43Word_two (i j : Fin 3) :
    omega43Word i j 2 = i + j := ...

@[simp] lemma omega43Word_three (i j : Fin 3) :
    omega43Word i j 3 = i + j + j := ...
```

The word map is injective because the first two coordinates recover `i` and
`j`:

```lean
lemma omega43Word_injective :
    Function.Injective
      (fun p : Prod (Fin 3) (Fin 3) => omega43Word p.1 p.2) := by
  intro p q h
  have h0 := congrArg (fun w : Config 4 3 => w 0) h
  have h1 := congrArg (fun w : Config 4 3 => w 1) h
  cases p
  cases q
  simp [omega43Word] at h0 h1
  ext <;> assumption
```

### 4.2 The state

The coefficient is `1/3`, not `1/sqrt 9`.

```lean
noncomputable def omega43Coeff : Complex :=
  (3 : Complex)^-1

noncomputable def omega43State : StateVector 4 3 :=
  mkStateVector fun w =>
    if IsOmega43Word w then omega43Coeff else 0
```

The coefficient norm lemma should be elementary:

```lean
lemma omega43Coeff_mul_star :
    omega43Coeff * star omega43Coeff =
      ((Fintype.card (Config 2 3) : Complex)^-1) := by
  -- card_config gives 3^2 = 9.
  -- omega43Coeff is real, so star omega43Coeff = omega43Coeff.
  -- Finish with norm_num/simp.
```

The exact simp route may need small helper facts:

```lean
lemma card_config_two_three :
    Fintype.card (Config 2 3) = 9 := by
  simpa [card_config]

lemma omega43Coeff_star :
    star omega43Coeff = omega43Coeff := by
  simp [omega43Coeff]
```

## 5. Normalization plan

Prove:

```lean
lemma omega43State_isNormalized :
    IsNormalized omega43State := by
  ...
```

Use the existing equivalence:

```lean
isNormalized_iff_norm_sq_eq_one
```

and mathlib's finite-dimensional norm formula:

```lean
EuclideanSpace.norm_sq_eq
```

The proof skeleton:

```lean
have hnorm_sq : norm omega43State ^ 2 = 1 := by
  calc
    norm omega43State ^ 2
        = sum w : Config 4 3, norm (omega43State w) ^ 2 := by
            simpa using EuclideanSpace.norm_sq_eq omega43State
    _ = sum w : Config 4 3,
          if IsOmega43Word w then norm omega43Coeff ^ 2 else 0 := by
            -- pointwise by cases on support membership
    _ = 9 * norm omega43Coeff ^ 2 := by
            -- support has cardinality 9
    _ = 1 := by
            -- norm (1/3) squared is 1/9
```

For the support cardinality, use a finite image:

```lean
let S : Finset (Config 4 3) :=
  Finset.image
    (fun p : Prod (Fin 3) (Fin 3) => omega43Word p.1 p.2) Finset.univ

have hS_card : S.card = 9 := by
  rw [Finset.card_image_of_injective]
  · simp
  · exact omega43Word_injective

have hS_support :
    forall w, w in S <-> IsOmega43Word w := by
  ...
```

Expected difficulty: moderate.  This is mostly finite-set rewriting and
`Complex` arithmetic.  It should be much easier than any analytic part of the
Erdos 953 proof.

## 6. Projection and completion lemmas

### 6.1 Core orthogonal-array lemma

The central finite lemma should say that every ordered pair of distinct
coordinates gives a bijection from the two parameters `(i,j)` to the observed
coordinate pair.

```lean
def projectWordPair (a b : Fin 4) (w : Config 4 3) :
    Prod (Fin 3) (Fin 3) :=
  (w a, w b)

lemma omega43_projection_bijective
    {a b : Fin 4} (hab : a ≠ b) :
    Function.Bijective
      (fun p : Prod (Fin 3) (Fin 3) =>
        projectWordPair a b (omega43Word p.1 p.2)) := by
  ...
```

There are two viable proof styles.

### 6.2 Preferred proof style: finite computation

Because the domain is tiny, this lemma can probably be proved by computation:

```lean
lemma omega43_projection_bijective
    {a b : Fin 4} (hab : a ≠ b) :
    Function.Bijective
      (fun p : Prod (Fin 3) (Fin 3) =>
        projectWordPair a b (omega43Word p.1 p.2)) := by
  -- possible route:
  --   fin_cases a <;> fin_cases b <;> simp at hab <;>
  --   constructor <;> intro ... <;> fin_cases ... <;> decide
```

or, if accepted cleanly:

```lean
lemma omega43_projection_bijective_all :
    forall a b : Fin 4, a ≠ b ->
      Function.Bijective
        (fun p : Prod (Fin 3) (Fin 3) =>
          projectWordPair a b (omega43Word p.1 p.2)) := by
  native_decide
```

`native_decide` is not a mathematical escape hatch here; it is a finite
verification of a decidable statement over a domain of size at most
`4 * 4 * 3 * 3`.  If the benchmark verifier or review standard dislikes
`native_decide`, replace it with explicit `fin_cases` proof scripts.

### 6.3 Structured algebra proof style

A more explanatory proof identifies the coordinate functions with the four
vectors

```text
(1,0), (0,1), (1,1), (1,2) in F_3^2.
```

The determinant of any two distinct vectors is nonzero in `F_3`, so the two
linear forms determine `(i,j)`.  This is conceptually cleaner but probably more
work in Lean unless we already have convenient `ZMod 3` matrix infrastructure
in the target file.

For this particular benchmark, the finite-computation proof is likely the
better engineering choice.

## 7. Reductions after arbitrary party permutations

The source definition of `IsAME` quantifies over every

```lean
pi : Equiv.Perm (Fin 4)
```

and asks for the first two parties of `permuteState pi omega43State` to have a
maximally mixed reduction.

For a fixed permutation `pi`, define which original coordinates are observed in
the first block and which original coordinates are traced out:

```lean
def sourceLeftIndex (pi : Equiv.Perm (Fin 4)) (i : Fin 2) : Fin 4 :=
  pi.symm (leftIndex (m := 2) (n := 4) (by decide) i)

def sourceRightIndex (pi : Equiv.Perm (Fin 4)) (i : Fin 2) : Fin 4 :=
  pi.symm (rightIndex (m := 2) (n := 4) (by decide) i)
```

If

```lean
q = combineFirst (n := 4) (d := 3) 2 (by decide) x z
w = permuteConfig pi q
```

then

```lean
w (sourceLeftIndex pi i) = x i
w (sourceRightIndex pi i) = z i
```

Prove these as simp lemmas:

```lean
@[simp] lemma permuted_combine_left
    (pi : Equiv.Perm (Fin 4)) (x z : Config 2 3) (i : Fin 2) :
    permuteConfig pi
      (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
      (sourceLeftIndex pi i) = x i := by
  simp [sourceLeftIndex, permuteConfig]

@[simp] lemma permuted_combine_right
    (pi : Equiv.Perm (Fin 4)) (x z : Config 2 3) (i : Fin 2) :
    permuteConfig pi
      (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
      (sourceRightIndex pi i) = z i := by
  simp [sourceRightIndex, permuteConfig]
```

For each `pi` and observed left configuration `x`, use
`omega43_projection_bijective` on the two source-left coordinates to recover the
unique parameters `(i,j)`.  Then define the completion as the two source-right
coordinates of the corresponding support word:

```lean
noncomputable def omega43ParamForLeft
    (pi : Equiv.Perm (Fin 4)) (x : Config 2 3) :
    Prod (Fin 3) (Fin 3) :=
  Classical.choose
    ((omega43_projection_bijective
      (a := sourceLeftIndex pi 0)
      (b := sourceLeftIndex pi 1)
      (by
        -- sourceLeftIndex pi 0 ≠ sourceLeftIndex pi 1
        ...)).2 (x 0, x 1))

noncomputable def omega43Completion
    (pi : Equiv.Perm (Fin 4)) (x : Config 2 3) : Config 2 3 :=
  fun r =>
    omega43Word
      (omega43ParamForLeft pi x).1
      (omega43ParamForLeft pi x).2
      (sourceRightIndex pi r)
```

The exact proof term around `Classical.choose` can be adjusted.  The important
mathematical invariant is:

```lean
lemma omega43_support_after_permute_iff
    (pi : Equiv.Perm (Fin 4)) (x z : Config 2 3) :
    IsOmega43Word
      (permuteConfig pi
        (combineFirst (n := 4) (d := 3) 2 (by decide) x z))
      <->
    z = omega43Completion pi x := by
  ...
```

The reverse direction says that if the right block is the computed completion,
then the full word is exactly `omega43Word i j`.  The forward direction uses
the uniqueness/injectivity of the source-left projection.

Prove injectivity of the completion from the corresponding source-right
projection:

```lean
lemma omega43Completion_injective (pi : Equiv.Perm (Fin 4)) :
    Function.Injective (omega43Completion pi) := by
  intro x y hxy
  -- The right coordinates of the two corresponding words agree by hxy.
  -- Since the source-right projection is bijective on support words,
  -- the parameters agree; then the source-left coordinates agree; hence x = y.
```

Again, this can be replaced by a finite computational lemma if the symbolic
proof becomes disproportionately long:

```lean
lemma omega43Completion_injective_all :
    forall pi : Equiv.Perm (Fin 4),
      Function.Injective (omega43Completion pi) := by
  native_decide
```

provided `omega43Completion` is computationally transparent enough.  If not,
prove a decidable support uniqueness lemma first and define the completion from
that lemma.

## 8. Applying the existing completion criterion

For a fixed permutation, the key amplitude lemma should be:

```lean
lemma omega43State_permuted_graph
    (pi : Equiv.Perm (Fin 4)) :
    forall x z,
      permuteState pi omega43State
        (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
        =
      if z = omega43Completion pi x then omega43Coeff else 0 := by
  intro x z
  rw [permuteState_apply, omega43State, mkStateVector_apply]
  by_cases h : z = omega43Completion pi x
  · have hsupp : IsOmega43Word
        (permuteConfig pi
          (combineFirst (n := 4) (d := 3) 2 (by decide) x z)) := by
        exact (omega43_support_after_permute_iff pi x z).2 h
    simp [hsupp, h]
  · have hsupp_not : not IsOmega43Word
        (permuteConfig pi
          (combineFirst (n := 4) (d := 3) 2 (by decide) x z)) := by
        intro hsupp
        exact h ((omega43_support_after_permute_iff pi x z).1 hsupp)
    simp [hsupp_not, h]
```

Then the maximally mixed reduction is immediate:

```lean
lemma omega43_hasMaximallyMixedFirstReduction
    (pi : Equiv.Perm (Fin 4)) :
    HasMaximallyMixedFirstReduction (n := 4) (d := 3)
      2 (by decide) (permuteState pi omega43State) := by
  apply hasMaximallyMixedFirstReduction_of_completion
    (n := 4) (d := 3) (m := 2) (hm := by decide)
    (psi := permuteState pi omega43State)
    (completion := omega43Completion pi)
    (coeff := omega43Coeff)
  · exact omega43State_permuted_graph pi
  · exact omega43Completion_injective pi
  · exact omega43Coeff_mul_star
```

The final theorem is then short:

```lean
theorem ame_4_3_exists : ExistsAME 4 3 := by
  refine ⟨omega43State, ?_⟩
  refine ⟨omega43State_isNormalized, ?_⟩
  intro pi
  simpa using omega43_hasMaximallyMixedFirstReduction pi
```

## 9. Alternative direct finite-reduction proof

If the completion construction with `Classical.choose` becomes fiddly, there is
a direct finite route:

1. Define `omega43State`.
2. Prove normalization as above.
3. Prove, by finite computation, that for every permutation `pi` and every
   `x y : Config 2 3`,

```lean
reducedDensityFirst (n := 4) (d := 3) 2 (by decide)
  (permuteState pi omega43State) x y =
maximallyMixed 2 3 x y
```

The proposition is finite: there are 24 permutations, 9 choices of `x`, 9
choices of `y`, and each reduced-density entry is a sum over 9 tails.  This is
conceptually less elegant but likely robust if expressed as a decidable equality
of complex rationals.

The risk is that `Complex` equalities involving `star` and casts may not reduce
as cleanly as the combinatorial completion proof.  For this reason, the
completion route is preferred: it reduces the matrix computation to an already
proved source lemma.

## 10. Implementation risks

### 10.1 `Fin 3` arithmetic

The biggest source of friction is likely modular arithmetic on `Fin 3`.  If
`simp` does not reduce expressions like `i + j + j`, use `fin_cases` aggressively
or define explicit arithmetic:

```lean
def qadd (a b : Fin 3) : Fin 3 :=
  ⟨(a.val + b.val) % 3, by omega⟩
```

Then prove all arithmetic facts by `fin_cases`.

### 10.2 Function extensionality for `Config 2 3` and `Config 4 3`

Many equalities are between functions.  Use:

```lean
ext k
fin_cases k <;> simp [omega43Word, ...]
```

It may be worth adding helper lemmas:

```lean
lemma config2_ext {x y : Config 2 3}
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext k
  fin_cases k <;> simp [h0, h1]

lemma config4_ext {x y : Config 4 3}
    (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) (h3 : x 3 = y 3) : x = y := by
  ext k
  fin_cases k <;> simp [h0, h1, h2, h3]
```

### 10.3 Decidability of `IsOmega43Word`

Inside proofs, `classical` should usually give a decidable predicate.  If `simp`
does not unfold the support predicate well, define a finite support set `S`
first and use membership in `S` as the state predicate:

```lean
def omega43Support : Finset (Config 4 3) :=
  Finset.image
    (fun p : Prod (Fin 3) (Fin 3) => omega43Word p.1 p.2) Finset.univ

noncomputable def omega43State : StateVector 4 3 :=
  mkStateVector fun w =>
    if w in omega43Support then omega43Coeff else 0
```

This often makes cardinality and finite computation easier.  The source theorem
does not care how the witness is defined.

### 10.4 `Complex` arithmetic

Keep the coefficient rational:

```lean
omega43Coeff = (3 : Complex)^-1
```

Avoid square roots.  The proof only needs

```text
(1/3) * conj(1/3) = 1/9.
```

This should be `norm_num` or `simp [omega43Coeff, card_config]`.

### 10.5 Review acceptability of finite computation

A finite `native_decide` proof of the projection property is mathematically
reasonable here, because the scientific content is exactly an explicit finite
qutrit construction.  Still, for a polished tb-science submission, it may be
better to expose the support-code/projection lemmas with clear names and use
finite computation only inside those lemmas.

## 11. Expected scale

With the existing `hasMaximallyMixedFirstReduction_of_completion` lemma, this
should be much smaller than the three Erdős projects.

Rough estimate:

- Definitions and simp lemmas: 50-100 lines.
- Normalization: 80-180 lines.
- Projection/bijection lemmas: 80-250 lines if finite computation works,
  perhaps 400-700 lines if done manually.
- Completion and reduction wrapper: 150-350 lines.
- Final theorem: less than 10 lines.

Total expected proof size: about 350-900 lines, depending on how much finite
case analysis Lean requires.

Main difficulty is not mathematics; it is indexing through

```lean
Fin 4
Equiv.Perm (Fin 4)
combineFirst
permuteConfig
Config n d
```

Compared with the Erdős formalizations:

- Much less analytic or number-theoretic depth than Erdős 953.
- Much less constructional machinery than Erdős 330.
- More finite linear-algebra/index bookkeeping than Erdős 1151's early
  abstract scaffold, but likely smaller than the completed Erdős projects.

The task looks viable as a `tb-3-science` candidate if the goal is a compact
formalisation of a real quantum-information construction.

## 12. Suggested first implementation milestone

Before attempting the full theorem, create a temporary Lean scratch file and
try to prove just this:

```lean
lemma omega43_projection_bijective_all :
    forall a b : Fin 4, a ≠ b ->
      Function.Bijective
        (fun p : Prod (Fin 3) (Fin 3) =>
          projectWordPair a b (omega43Word p.1 p.2)) := by
  ...
```

If this compiles cleanly, the rest of the proof is likely routine.

If this lemma is painful, fall back to an explicit enumeration of the six
unordered coordinate pairs:

```text
(0,1), (0,2), (0,3), (1,2), (1,3), (2,3).
```

For each pair, write the inverse map by hand:

```text
(0,1): (a,b) -> (a,b)
(0,2): (a,c) -> (a,c-a)
(0,3): (a,d) -> (a,2*(d-a))
(1,2): (b,c) -> (c-b,b)
(1,3): (b,d) -> (d-2b,b)
(2,3): (c,d) -> (2c-d,d-c)
```

All arithmetic is modulo 3.  These explicit inverses would make the final proof
more verbose but more transparent to Lean.

## 13. Submission path if formalisation succeeds

If the proof is completed:

1. Add an oracle solution directory for
   `openquantumproblems-35-ame-4-3-exists`.
2. Regenerate the task metadata if this repository is treating it as a promoted
   gold task.
3. Run the local task verifier.
4. Run Harbor with the oracle agent against the generated task.
5. If contributing to tb-science rather than this repository's gold set, package
   the theorem statement, source references, and completed Lean proof as the
   science task artifact.

For a polished task statement, cite the OQP page and Goyeneche et al. Eq. (11),
and describe the proof objective as:

> Formalise that the explicit four-qutrit state
> `(1/3) sum_{i,j} |i,j,i+j,i+2j>` is absolutely maximally entangled under the
> benchmark's reduced-density-matrix definition.
