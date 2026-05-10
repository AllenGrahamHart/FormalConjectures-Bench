# Erdős Problem #330 formalisation brief — revised using the supplied Overleaf proof

This is a Codex-facing formalisation brief for Erdős Problem #330, based on the supplied proof

> **A Minimal Asymptotic Basis of Positive Upper Density with Every Element Density-Essential**
> by David Turturean, April 2026.

The previous brief was a reconstruction from the forum discussion.  This revised brief should supersede it.  The supplied proof is much more useful: it gives a complete finite gadget, a local activation lemma, one-stage extension, and a global priority construction.

The recommended Lean target is the exact theorem proved in the note:

```lean
-- Schematic only.
theorem erdos330 :
  ∃ A : Set ℕ,
    IsAsymptoticBasisOfOrderTwo A ∧
    0 < upperDensity A ∧
    ∀ a ∈ A, 0 < upperDensity (privateSet A a)
```

where

```lean
exactTwoFold A = {n : ℕ | ∃ x ∈ A, ∃ y ∈ A, x + y = n}
privateSet A a = exactTwoFold A \ exactTwoFold (A \ {a})
```

The theorem is about **upper asymptotic density**, not lower density and not existence of a natural density.

The proof uses exact two-fold sums.  It allows the same summand twice, as usual for additive bases.  The final remark in the proof says the same protected blocks also handle the “at most two summands” convention, but this should be a non-goal for the first formalisation.

---

## 0. Important audit notes from the supplied proof

The proof is very formalisation-friendly overall, but a few details should be made explicit before Lean work begins.

### 0.1 Avoid infinite products in Lean

The proof defines

\[
\delta = \prod_{a\in A}\left(1-\frac1{m_a}\right)>0.
\]

For Lean, it is better not to use an infinite product.  Instead choose the personal primes so that

\[
\sum_a \frac1{m_a} \le \eta
\]

for a fixed explicit \(0<\eta<1\), for example \(\eta=1/4\).  Then every finite active set \(P\) satisfies

\[
\prod_{b\in P}\left(1-\frac1{m_b}\right)
\ge
1-\sum_{b\in P}\frac1{m_b}
\ge 1-\eta.
\]

Use a constant

\[
\delta_0 := 1-\eta,
\]

for example \(\delta_0=3/4\), or use a more conservative \(\delta_0=1/2\).  This replaces every use of the infinite product.

Lean lemma to prove:

```lean
lemma one_sub_sum_le_prod_one_sub
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) :
  1 - (∑ i in s, x i) ≤ ∏ i in s, (1 - x i)
```

Then use it with `x i = 1 / (m i : ℝ)`.

This is much easier than proving positivity of an infinite product.

### 0.2 Avoid Dirichlet’s theorem

The proof says to choose primes \(p\equiv 3\pmod 4\) using Dirichlet’s theorem.  For Lean, do **not** use Dirichlet.  It suffices to prove the elementary Euclid-style fact:

```lean
lemma exists_prime_three_mod_four_ge (N : ℕ) :
  ∃ p ≥ N, Nat.Prime p ∧ p % 4 = 3
```

A standard proof: given a finite list of primes \(3\bmod 4\), form something like

\[
4M^2-1 = (2M-1)(2M+1).
\]

A prime divisor of this number is odd and at least one prime divisor is \(3\bmod 4\), because a product of numbers all \(1\bmod4\) is \(1\bmod4\), while \(4M^2-1\equiv3\bmod4\).  Arrange \(M\) to be divisible by all previously considered primes and large enough.  This proves unboundedly many primes \(3\bmod4\).

This gives primes satisfying all stage requirements:

```lean
p > X,
p ≥ 23,
p % 4 = 3,
(1 : ℝ) / p ≤ ε_j.
```

### 0.3 Track a fixed lower endpoint for coverage

The proof says that `2S` contains all integers “in a fixed interval up to `R₀`”.  In Lean, include a fixed lower endpoint `coverStart` in the stage state:

```lean
coverage : ∀ n, coverStart ≤ n → n ≤ R → n ∈ exactTwoFold S
```

The lower endpoint is established in the initial reservoir by the middle-interval lemma.  Each stage only extends the upper endpoint.

### 0.4 Add one harmless inequality for the new height

In the stage construction, after defining

\[
K=R-X+1,
\qquad
Z=[K,K+L_Z]_{D^+}^{(M^+)},
\qquad
X'=K+L_Z,
\]

make sure all newly added elements are at most \(X'\).  The lower block `B` is below `K`, but the private-partner block

\[
P_{\rm blk}=[2N+M^+-a, R-a]_{P_a^*}^{(M^+)}
\]

can extend beyond `K` if `a` is small.  Add the stage choice condition

\[
L_Z \ge X
\]

or more directly

\[
R-a \le K+L_Z.
\]

This is easy because `L_Z` is chosen “very large”.  It should be part of the formal stage hypotheses/construction.

### 0.5 Do not use Big-O in the formal statement

The proof uses an estimate of the form

\[
\#((a+P_{\rm priv})\cap[1,R-X])
\ge
\frac{|P_a^*|}{M^+}(N+L-M^+-2X)-O(M^+).
\]

In Lean, replace this with an explicit floor/counting bound.  For a residue set `Ω : Finset (ZMod M)` and an interval of length `len`, prove for example

```lean
lemma count_residue_block_lower
    (M : ℕ) (hM : 0 < M) (Ω : Finset (ZMod M))
    (lo len : ℕ) :
  ((Icc lo (lo + len)).filter (fun n => (n % M) ∈ Ω)).card
    ≥ Ω.card * (len / M)
```

or a stronger variant with `len + 1`.  This is enough.  Choose `L` so large that the floor error is negligible with the desired explicit constants.

### 0.6 Store the “base part” of the CRT gadget

The local activation reservoir lemma uses not only the fact that

\[
D^+ + T_a = \mathbb Z/M^+\mathbb Z,
\]

but specifically the base part of `T_a`, whose old-coordinate projection has full coverage with the old allowed set.  In the formalisation, the CRT gadget structure should expose this base subset.

Suggested structure:

```lean
structure CRTGadget (P : Finset ℕ) (m : ℕ → ℕ) (a : ℕ) where
  M : ℕ
  D : Finset (ZMod M)
  T : Finset (ZMod M)
  Pstar : Finset (ZMod M)
  Tbase : Finset (ZMod M)
  Tbase_subset_T : Tbase ⊆ T
  T_subset_D : T ⊆ D
  Pstar_subset_D : Pstar ⊆ D
  T_add_T_compl_private : ...
  D_add_T_full : ...
  base_projection_full_for_activation : ...
  selected_coord_T_avoids : ...
  selected_coord_Pstar_fixed : ...
  Pstar_card_formula : ...
```

The exact fields will depend on whether residues are represented as `ZMod M` or as a coordinate product.

---

## 1. Mathematical theorem and definitions

### 1.1 Exact two-fold sumset

Use exact two-fold sums first.

```lean
def twoFold (A : Set ℕ) : Set ℕ :=
  {n | ∃ x ∈ A, ∃ y ∈ A, x + y = n}

def IsAsymptoticBasisTwo (A : Set ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → n ∈ twoFold A

def privateSet (A : Set ℕ) (a : ℕ) : Set ℕ :=
  twoFold A \ twoFold (A \ {a})
```

For finite stage sets, it may be convenient to use `Finset ℕ` and coerce to `Set ℕ`:

```lean
def twoFoldFinset (S : Finset ℕ) : Set ℕ :=
  {n | ∃ x ∈ S, ∃ y ∈ S, x + y = n}
```

Prove bridge lemmas between `twoFoldFinset S` and `twoFold (fun n => n ∈ S)`.

### 1.2 Upper density

If using the density API from Formal Conjectures, target its existing `Set.upperDensity`.  Otherwise define a lightweight notion sufficient for the proof:

```lean
def HasPositiveUpperDensity (S : Set ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ x ≥ N,
    ε * x ≤ ((Finset.Icc 1 x).filter (fun n => n ∈ S)).card
```

This avoids `limsup` at first.  Later one can prove equivalence with the library upper-density definition.

The construction proves this subsequence-witness version directly for `A` and for every `privateSet A a`.

### 1.3 Residue blocks

For modulus `M`, residue set `Ω`, and interval `[lo, hi]`:

```lean
def residueBlock (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter (fun n => (ZMod.ofNat M n) ∈ Ω)
```

Depending on the actual `ZMod` API, the cast may be written differently.

For proofs involving interval lengths, it may be cleaner to parameterise by `lo` and `L`:

```lean
def residueBlockLen (M : ℕ) (Ω : Finset (ZMod M)) (lo L : ℕ) : Finset ℕ :=
  residueBlock M Ω lo (lo + L)
```

---

## 2. Finite residue lemmas

The finite section is the hardest purely finite part of the proof.  It consists of three pieces:

1. quadratic residue sum lemma;
2. two-safe-pairs lemma over a product of finite fields;
3. bounded-resource CRT gadget.

A sensible implementation strategy is to state the CRT gadget as an interface first, complete the stage/global proof using that interface, and later prove the interface from the finite lemmas.

---

### 2.1 Quadratic-residue sums

Mathematical statement:

Let `p` be a prime with `p % 4 = 3` and `23 ≤ p`.  Let `Q` be the set of nonzero quadratic residues in `F_p`.  If `U ⊆ Q` and `|U| ≤ 2`, then

\[
(Q\setminus U)+(Q\setminus U)=F_p^\times.
\]

Also

\[
Q\cap(-Q)=\varnothing.
\]

Lean-ish statement:

```lean
lemma qr_neg_disjoint
    (p : ℕ) [Fact (Nat.Prime p)]
    (hp3 : p % 4 = 3) :
  ∀ x : ZMod p, x ∈ Q p → -x ∉ Q p

lemma qr_sum_after_delete_two
    (p : ℕ) [Fact (Nat.Prime p)]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p)
    (U : Finset (ZMod p))
    (hUQ : U ⊆ Q p) (hUcard : U.card ≤ 2) :
  ∀ t : ZMod p, t ≠ 0 →
    ∃ x ∈ Q p, x ∉ U,
    ∃ y ∈ Q p, y ∉ U,
      x + y = t
```

The proof in the note counts ordered pairs.  For `t ≠ 0`, define

\[
N(t)=\#\{(x,y)\in Q^2:x+y=t\}.
\]

The character calculation gives

\[
N(t)=\frac{p-1-2\chi(t)}4.
\]

Therefore `N(t) ≥ (p-3)/4 ≥ 5`.  Deleting two residues removes at most four ordered representations, so at least one remains.

Implementation notes:

* This lemma is the most likely finite-field bottleneck.
* If the quadratic-character API is awkward, isolate this as a standalone file.
* Avoid depending on this lemma in the stage/global construction until late; use a `CRTSelectedCoordinateGadget` assumption first.

---

### 2.2 Two safe pairs lemma

Mathematical statement:

Let

\[
G=\prod_{i=1}^k \mathbb F_{p_i}, \qquad p_i\ge7,
\]

and

\[
D=\prod_i \mathbb F_{p_i}^{\times}.
\]

For arbitrary targets `e_i`, define

\[
C=\{z\in G:\exists i, z_i=e_i\}.
\]

Then there are sets

\[
L_1,R_1,L_2,R_2\subset D
\]

such that

\[
L_\nu+R_\nu\subset C
\]

for `ν=1,2`, and

\[
C=(L_1+R_1)\cup(L_2+R_2).
\]

The proof chooses two disjoint nonzero ordered pairs

\[
(c_i^{(1)},d_i^{(1)}),\quad(c_i^{(2)},d_i^{(2)})
\]

with sum `e_i` in every coordinate.  For `p_i ≥ 7`, explicit choices are:

* if `e_i ≠ 0`: scale `(2,-1)` and `(3,-2)` by `e_i`;
* if `e_i = 0`: use `(1,-1)` and `(2,-2)`.

Then set `s = ceil(k/2)` and define

\[
L_\nu=\{x\in D:\#\{i:x_i=c_i^{(\nu)}\}\ge s\},
\]

\[
R_\nu=\{y\in D:\#\{i:y_i=d_i^{(\nu)}\}\ge k-s+1\}.
\]

Containment is by pigeonhole: the coordinate sets have total size at least `k+1`.

Coverage proof detail:

For `z ∈ C`, let

\[
Z=\{i:z_i=e_i\},\quad t=|Z|≥1,
\quad U=I\setminus Z.
\]

A coordinate `i ∈ U` is bad for `ν` if

\[
z_i\in\{c_i^{(\nu)},d_i^{(\nu)}\}.
\]

Because the two chosen pairs are disjoint in each coordinate, each `i ∈ U` is bad for at most one value of `ν`.  Choose `ν` with at most `|U|/2` bad coordinates.

Then define

\[
a_0=\max(0,s-t),\qquad b_0=\max(0,k-s+1-t).
\]

Choose disjoint coordinate sets

\[
S_0\subset U\setminus C_0,
\qquad
T_0\subset U\setminus D_0,
\]

with sizes `a₀` and `b₀`, where

\[
C_0=\{i\in U:z_i=c_i\},\qquad D_0=\{i\in U:z_i=d_i\}.
\]

The note says the necessary inequalities are elementary.  In Lean, make this a separate finite-choice lemma:

```lean
lemma choose_disjoint_avoiding_two_forbidden_sets
    (U C0 D0 : Finset ι)
    (hC : C0 ⊆ U) (hD : D0 ⊆ U) (hdisj : Disjoint C0 D0)
    (a b : ℕ)
    (ha : a ≤ (U \ C0).card)
    (hb : b ≤ (U \ D0).card)
    (hab : a + b ≤ U.card) :
  ∃ S T : Finset ι,
    S ⊆ U \ C0 ∧ T ⊆ U \ D0 ∧ Disjoint S T ∧
    S.card = a ∧ T.card = b
```

Then fill coordinates:

* On `Z`: set `x_i=c_i`, `y_i=d_i`.
* On `S_0`: set `x_i=c_i`, `y_i=z_i-c_i`; nonzero because `i∉C_0`.
* On `T_0`: set `y_i=d_i`, `x_i=z_i-d_i`; nonzero because `i∉D_0`.
* Else choose any nonzero `x_i ≠ z_i`, and put `y_i=z_i-x_i`.  This is possible because `p_i≥7`, so there are enough nonzero choices.

The edge case `k=0` has `C=∅` and all four sets empty.

---

### 2.3 Bounded-resource CRT gadget

This is the key finite lemma used by the stage construction.

#### Data

`P` is a finite active set.  Each `b ∈ P` has a personal modulus `m_b`, a distinct prime satisfying

```lean
Nat.Prime (m b)
23 ≤ m b
m b % 4 = 3
```

Define

\[
M_P=\prod_{b\in P} m_b.
\]

Define the allowed residue set

\[
D_P=\{x\bmod M_P: \forall b\in P,
      x\not\equiv b\pmod {m_b}\}.
\]

The CRT identifies `ZMod M_P` with

\[
\prod_{b\in P} \mathbb F_{m_b}.
\]

#### Statement

For every selected active element `a ∈ P`, there exist residue sets

\[
T_a\subset D_P,
\qquad
P_a^*\subset D_P,
\]

such that:

1. `T_a + T_a` is the complement of the private slice:

   \[
   T_a+T_a=(\mathbb Z/M_P\mathbb Z)\setminus(a+P_a^*).
   \]

2. `D_P + T_a` is full:

   \[
   D_P+T_a=\mathbb Z/M_P\mathbb Z.
   \]

3. In the `m_a` coordinate, all elements of `P_a^*` have one fixed residue

   \[
   r_a\not\equiv a\pmod {m_a},
   \]

   while all elements of `T_a` avoid the residue `a mod m_a`.

4. Cardinality formula:

   \[
   \frac{|P_a^*|}{M_P}
   =
   \frac1{m_a}\prod_{b\in P,b\ne a}\left(1-\frac1{m_b}\right).
   \]

#### Construction details

Split the CRT product into the selected coordinate and the remaining coordinates:

\[
G_0=\mathbb F_{m_a},
\qquad
\alpha\equiv a\pmod {m_a},
\qquad
G'=\prod_{b\in P\setminus\{a\}}\mathbb F_{m_b}.
\]

Then

\[
D_P=(G_0\setminus\{\alpha\})\times D'.
\]

Choose `h ∈ G₀` so that

\[
v=\alpha-h
\]

is a nonzero quadratic nonresidue.  Put

\[
\tau=2h,
\qquad
r_a=\tau-\alpha.
\]

Then `r_a ≠ α`.

Let `Q₀` be the nonzero quadratic residues.  Choose distinct

\[
u_1,u_2\in Q_0,
\qquad
u_i\ne -v.
\]

The QR lemma implies

\[
(Q_0\setminus\{u_1,u_2\})+(Q_0\setminus\{u_1,u_2\})=G_0^\times.
\]

Define

\[
Q=h+(Q_0\setminus\{u_1,u_2\}).
\]

Then

\[
Q\subset G_0\setminus\{\alpha\},
\qquad
Q+Q=G_0\setminus\{\tau\}.
\]

For the nonselected coordinates define

\[
H'=a'+D'.
\]

Then

\[
C'=G'\setminus H'
\]

is the union of coordinate hyperplanes saying that a coordinate equals `a_b+b_b`.  Apply the two-safe-pairs lemma after affine normalisation to obtain

\[
L_1,R_1,L_2,R_2\subset D'
\]

with

\[
L_\nu+R_\nu\subset C',
\qquad
C'=(L_1+R_1)\cup(L_2+R_2).
\]

Define

\[
P_a^*=\{r_a\}\times D'.
\]

Then

\[
a+P_a^*=\{\tau\}\times H'.
\]

Define

\[
T_a=
(Q\times D')
\cup((h+u_1)\times L_1)
\cup((h-u_1)\times R_1)
\cup((h+u_2)\times L_2)
\cup((h-u_2)\times R_2).
\]

The base part is

\[
T_{a,0}=Q\times D'.
\]

This base part should be stored in the Lean object because it is used later in the activation lemma.

Key selected-coordinate fact:

No unmatched selected-coordinate sum equals `τ`.  Offsets are either in `Q₀ \ {u₁,u₂}` or among `±u₁, ±u₂`.  Since `Q₀ ∩ -Q₀ = ∅`, the only offset pairs summing to zero are the matched correction pairs `uν,-uν`.

Therefore:

* base-base covers all selected coordinates except `τ`;
* matched correction pairs cover the `τ` slice over `C'`;
* the remaining `τ` slice is exactly `{τ} × H' = a + P_a^*`.

---

## 3. Local activation reservoir

This is the most important bridge between the finite CRT gadget and the global priority construction.

### 3.1 Setup

At a stage, we have active set `P`, modulus `M`, allowed residues `D`, and a finite set `S ⊆ [1,X]`.  The current reservoir is the full allowed block

\[
U=[H,X]_D^{(M)}\subset S.
\]

Let

\[
C=3M.
\]

Every interval of length `C` inside `[H,X]` contains at least two integers from each residue class `ρ∈D` modulo `M`.

Now activate a dormant element `b∈S\P`.  Choose a new personal prime

\[
p_b>X.
\]

Define

\[
P^+=P\cup\{b\},
\qquad
M^+=Mp_b,
\qquad
D^+=D_{P^+}.
\]

The old reservoir is not complete modulo `M⁺`, but the fact `p_b>X` means that any new forbidden congruence excludes at most one old helper in `[1,X]`.

### 3.2 Local reservoir lemma

For any interval `J⊆[H,X]` of length `C`:

1. for every residue `γ mod M⁺`, there exists `u∈J∩U` such that

   \[
   \gamma-u\in D^+;
   \]

2. if `a∈P` and `T_a` is the CRT gadget for the enlarged active set `P⁺`, then for every residue `γ mod M⁺`, there exists `u∈J∩U` such that

   \[
   \gamma-u\in T_a.
   \]

Proof of (1):

* Project `γ` modulo old `M`.
* Since `D+D=Z/MZ`, choose old residues `ρ,d∈D` with `ρ+d=γ mod M`.
* In `J`, there are at least two old helpers `u∈U` with old residue `ρ`.
* The new coordinate forbids only

  \[
  \gamma-u\equiv b\pmod {p_b},
  \]

  equivalently

  \[
  u\equiv \gamma-b\pmod {p_b}.
  \]

* Because `p_b>X` and `u∈[1,X]`, this excludes at most one actual helper.
* The other helper works.

Proof of (2):

Use the base part `Tbase` of the CRT gadget.  Its projection to the old modulus has the property

\[
D + \overline{T}_{a,0}=\mathbb Z/M\mathbb Z.
\]

Choose old residues `ρ∈D` and `θ∈projection(Tbase)` with `ρ+θ=γ mod M`.  Again there are two helpers of residue `ρ`, and the new prime excludes at most one.  The survivor gives `γ-u∈Tbase⊆T_a`.

### 3.3 Helper block coverage

If

\[
Y=[N,N+L]_{\Omega}^{(M^+)},
\]

where `Ω` is either `D⁺` or `T_a`, then

\[
U+Y\supset[H+N+C,\;X+N+L-C].
\]

Proof: for a target `n`, choose a length-`C` interval

\[
J\subset [H,X]\cap[n-N-L,n-N].
\]

Apply the local reservoir lemma to `γ=n mod M⁺` and this `J`.  The resulting `u` has `n-u∈Ω`, and the interval condition ensures `n-u∈[N,N+L]`.

In Lean, isolate the interval arithmetic as a separate lemma.  The key condition is:

```lean
n ∈ Icc (H + N + C) (X + N + L - C)
```

implies

```lean
∃ Jlo, H ≤ Jlo ∧ Jlo + C ≤ X ∧
       n - (N + L) ≤ Jlo ∧ Jlo + C ≤ n - N
```

or an equivalent formulation.

### 3.4 Middle interval lemma

If `L ≥ M` and `C₁+C₂` contains residue `σ mod M`, then

\[
[N,N+L]_{C_1}^{(M)}+[N,N+L]_{C_2}^{(M)}
\]

contains every integer

\[
n\in[2N+M,2N+2L-M]
\]

with

\[
n\equiv\sigma\pmod M.
\]

Proof: possible first summands in residue class `c₁` form an interval long enough to hit the required range.

Make this a general lemma for residue blocks.

---

## 4. Stage state

Use a structure like this.  The precise fields can be adjusted.

```lean
structure StageState where
  S : Finset ℕ
  P : Finset ℕ
  m : ℕ → ℕ
  H X R : ℕ
  coverStart : ℕ

  P_subset_S : P ⊆ S
  S_le_X : ∀ s ∈ S, s ≤ X

  -- Active moduli.
  m_prime : ∀ a ∈ P, Nat.Prime (m a)
  m_ge23 : ∀ a ∈ P, 23 ≤ m a
  m_mod4 : ∀ a ∈ P, m a % 4 = 3
  m_pairwise_coprime_or_distinct : ...

  -- Active modulus.
  M : ℕ
  M_def : M = ∏ a in P, m a

  -- Allowed residue set D_P.
  D : Finset (ZMod M)
  D_def : ...

  -- Isolation.
  isolated : ∀ a ∈ P, ∀ s ∈ S,
    s ≡ a [MOD m a] → s = a

  -- Reservoir.
  reservoir_subset :
    residueBlock M D H X ⊆ S

  -- Local multiplicity, usually follows from being a full residue block
  -- and X-H ≥ 3M, but store it as an invariant if convenient.
  reservoir_multiplicity :
    ∀ Jlo, H ≤ Jlo → Jlo + 3*M ≤ X →
      ∀ ρ ∈ D,
        ∃ u ∈ residueBlock M {ρ} Jlo (Jlo + 3*M),
        ∃ v ∈ residueBlock M {ρ} Jlo (Jlo + 3*M),
          u ≠ v ∧ u ∈ S ∧ v ∈ S

  -- Headroom.
  reservoir_long : H + 3*M ≤ X
  headroom : H + X + 3*M ≤ R

  -- Coverage.
  coverage : ∀ n, coverStart ≤ n → n ≤ R → n ∈ twoFoldFinset S

  -- Dormancy available.
  exists_dormant : ∃ b ∈ S, b ∉ P
```

Potential simplification: derive `reservoir_multiplicity` from `reservoir_subset`, `D_def`, and interval length.  But storing it as an invariant makes the stage proof cleaner.

---

## 5. One service-and-tail stage

### 5.1 Inputs

At the beginning of a stage:

* finite `S⊆[1,X]`;
* finite active `P⊆S`;
* personal primes for active elements;
* isolation for each active element;
* active modulus `M` and allowed residues `D`;
* covered endpoint `R₀` with fixed lower endpoint `coverStart`;
* reservoir

  \[
  U=[H,X]_D^{(M)}\subset S;
  \]

* `C=3M`;
* every length-`C` subinterval of `[H,X]` has two helpers in each allowed residue;
* strengthened headroom:

  \[
  X-H\ge C,
  \qquad
  H+X+C\le R_0.
  \]

Choose:

* a dormant `b∈S\P` to activate;
* a fresh prime

  \[
  p_b>X,
  \quad p_b≥23,
  \quad p_b≡3\pmod4;
  \]

* enlarged active set `P⁺=P∪{b}`;
* enlarged modulus `M⁺=M p_b`;
* an old active `a∈P` to serve;
* CRT gadget `T_a,P_a^*` for `a` in the enlarged system.

### 5.2 Parameter choices

Choose `N>X` satisfying

\[
H+N+C\le R_0+1.
\]

This is possible by headroom; `N=X+1` works.

Choose `L` so large that:

\[
L\ge \max(C,M^+),
\]

\[
X+N+L-C\ge 2N+M^+-1,
\]

\[
N+L-M^+-2X>0.
\]

For the density proof, impose a stronger explicit condition too:

\[
\#\bigl([X+N+L+1,R-X]_{a+P_a^*}^{(M^+)}\bigr)
\ge c_a (R-X)
\]

for a chosen constant such as

\[
c_a = \frac{\delta_0}{8m_a}.
\]

Rather than proving this inside the stage proposition with asymptotics, use a separate `exists_large_L_for_private_density` lemma from residue-block counting.

Define

\[
B=[N,N+L]_{T_a}^{(M^+)},
\]

\[
R=2N+2L-M^+,
\]

\[
P_{\rm blk}=[2N+M^+-a, R-a]_{P_a^*}^{(M^+)},
\]

\[
K=R-X+1.
\]

Choose `L_Z` very large and define

\[
Z=[K,K+L_Z]_{D^+}^{(M^+)}.
\]

Require:

\[
X+K+L_Z-C\ge 2K+M^+-1,
\]

\[
L_Z\ge 3M^+,
\]

\[
K+(K+L_Z)+3M^+\le 2K+2L_Z-M^+,
\]

and add:

\[
L_Z\ge X
\]

to ensure the new height `X'=K+L_Z` bounds all of `S'`.

For the positive upper density of `A`, also impose a direct density condition on `Z`, for instance:

\[
\#Z \ge \frac{\delta_0}{4}(K+L_Z).
\]

This follows for large `L_Z` because the residue density of `D⁺` is at least `δ₀`.

Define

\[
S'=S\cup B\cup P_{\rm blk}\cup Z.
\]

Set next-stage data:

\[
P'=P^+,
\quad
M'=M^+,
\quad
H'=K,
\quad
X'=K+L_Z,
\quad
R'=2K+2L_Z-M^+.
\]

### 5.3 Stage theorem

Formal target:

```lean
theorem stage_extension
    (st : StageState)
    (b : ℕ) (hbS : b ∈ st.S) (hbDormant : b ∉ st.P)
    (a : ℕ) (haP : a ∈ st.P)
    (p_b : ℕ) (hp_b : FreshPrimeData st b p_b)
    (params : StageParams st a b p_b) :
  ∃ st' : StageState,
    st'.S = st.S ∪ B ∪ Pblk ∪ Z ∧
    st'.P = insert b st.P ∧
    st.coverStart = st'.coverStart ∧
    st.R < st'.R ∧
    ProtectedBlockPermanentCertificate st st' a
```

The `ProtectedBlockPermanentCertificate` should record the finite protected interval produced at this service stage:

```lean
structure ProtectedBlockCertificate where
  a : ℕ
  endpoint : ℕ       -- endpoint = R - X
  block : Finset ℕ   -- subset of privateSet after this stage
  block_subset_private_stage :
    ∀ n ∈ block, n ∈ privateSetFinset st'.S a
  block_le_endpoint : ∀ n ∈ block, n ≤ endpoint
  block_density_lower :
    c_a * endpoint ≤ block.card
```

Later, permanence follows because all future elements are larger than this endpoint.

---

## 6. Proof of the stage theorem

### 6.1 Coverage through the lower block

By helper block coverage with `Ω=T_a`,

\[
U+B\supset[H+N+C,\;X+N+L-C].
\]

Because

\[
H+N+C\le R_0+1,
\]

this continues the old covered interval.

By

\[
X+N+L-C\ge 2N+M^+-1,
\]

it reaches up to just before the middle interval for `B+B`.

On

\[
[2N+M^+,R],
\qquad R=2N+2L-M^+,
\]

use the middle-interval lemma and CRT gadget:

* `B+B` covers every residue except `a+P_a^*`;
* `a+Pblk` covers exactly the missing private residues.

Therefore coverage continues through `R`.

### 6.2 Coverage through the tail

By helper block coverage with `Ω=D⁺`,

\[
U+Z\supset[H+K+C,\;X+K+L_Z-C].
\]

Since

\[
K=R-X+1
\]

and `X-H≥C`, the left endpoint is at most `R+1`.  Hence `U+Z` begins no later than the first integer after the already-covered range.

By the imposed inequality

\[
X+K+L_Z-C\ge 2K+M^+-1,
\]

this overlaps the middle interval covered by `Z+Z`:

\[
[2K+M^+,2K+2L_Z-M^+].
\]

Since `D⁺+D⁺` is the full residue group, `Z+Z` covers every integer in that middle interval.

This proves the next coverage endpoint

\[
R'=2K+2L_Z-M^+.
\]

### 6.3 New reservoir

The next reservoir is exactly

\[
Z=[K,K+L_Z]_{D^+}^{(M^+)}.
\]

Because `L_Z≥3M⁺`, every subinterval of length `3M⁺` has two representatives from each allowed residue.  Because

\[
K+(K+L_Z)+3M^+\le 2K+2L_Z-M^+,
\]

the strengthened headroom condition holds for the next stage.

### 6.4 Isolation

For the newly activated `b`, the new prime satisfies `p_b>X`.  Since all old elements are at most `X`, congruence modulo `p_b` among old elements is equality.  Thus only `b` is congruent to `b mod p_b` in the old set.  All new elements lie in `D⁺`, so they avoid `b mod p_b`.

For old active `c∈P`, isolation was true in `S`, and all new elements lie in `D⁺`, so they avoid `c mod m_c`.  Thus old isolation persists.

### 6.5 Privacy of the protected core

Define

\[
P_{\rm priv}=
\{p\in P_{\rm blk}: X+N+L<a+p\le R-X\}.
\]

For every

\[
n=a+p,
\qquad p\in P_{\rm priv},
\]

prove

\[
n\in E_{S'}(a).
\]

Representation using `a` exists by construction, since `p∈Pblk⊆S'`.

Now exclude representations without `a`:

1. **Old-old sums:** impossible because `n>2X`.
2. **Old + B:** impossible because every such sum is at most `X+N+L<n`.
3. **B+B:** impossible because `B+B` avoids the residue slice `a+P_a^*`, while `n` lies in that slice.
4. **Old element other than `a` + Pblk:** if

   \[
   s+p'=a+p
   \]

   with `s∈S\{a}` and `p,p'∈Pblk`, then reducing modulo `m_a` gives

   \[
   s\equiv a\pmod {m_a},
   \]

   contradicting isolation of `a`.
5. **B+Pblk:** in the selected coordinate, elements of `B` have residues in `T_a`, which avoid `a mod m_a`; elements of `Pblk` have selected coordinate `r_a`; hence their sum cannot have selected coordinate `a+r_a`.
6. **Pblk+Pblk:** selected coordinate is `2r_a`, not `a+r_a`, because `r_a≠a`.
7. **Any sum using Z:** every element of `Z` is at least

   \[
   K=R-X+1>n,
   \]

   so no natural-number sum using `Z` can equal `n`.

This proves the stage-private certificate.

### 6.6 Counting the protected core

The set `a+P_priv` is a translate of the residue set `P_a^*` inside the interval

\[
(X+N+L,
\quad R-X].
\]

The interval length is

\[
(R-X)-(X+N+L)=N+L-M^+-2X.
\]

Use residue-block counting to prove a lower bound.  Since

\[
\frac{|P_a^*|}{M^+}
=
\frac1{m_a}\prod_{b\in P^+,b\ne a}\left(1-rac1{m_b}\right)
\ge
\frac{\delta_0}{m_a},
\]

and since `L` is chosen large, arrange directly that

\[
\#(a+P_{\rm priv})
\ge
\frac{\delta_0}{8m_a}(R-X).
\]

Do this with explicit constants to avoid limit arguments inside the stage proof.

---

## 7. Global priority construction

### 7.1 Initial state

Choose a seed element `a₀`, for example `a₀=1`.

Choose a prime

\[
m_{a_0}>a_0,
\quad m_{a_0}≥23,
\quad m_{a_0}≡3\pmod4,
\]

also satisfying the reciprocal budget.

Let

\[
D_0=\mathbb Z/m_{a_0}\mathbb Z\setminus\{a_0\bmod m_{a_0}\}.
\]

Choose `H₀<X₀`, with `H₀>a₀`, so large that

\[
U_0=[H_0,X_0]_{D_0}^{(m_{a_0})}
\]

has the local multiplicity property with `C₀=3m_{a₀}` and

\[
H_0+X_0+C_0\le R_0,
\qquad
R_0=2X_0-m_{a_0}.
\]

The initial finite set is

\[
S_0=\{a_0\}\cup U_0,
\qquad
P_0=\{a_0\}.
\]

The middle-interval lemma gives

\[
U_0+U_0\supset[2H_0+m_{a_0},2X_0-m_{a_0}].
\]

Set

\[
coverStart=2H_0+m_{a_0}.
\]

Then the initial `StageState` satisfies coverage from `coverStart` to `R₀`.

### 7.2 Activation schedule

At every stage, activate the least dormant element of the current finite set:

\[
b=\min(S\setminus P).
\]

This ensures every element of the eventual set `A` is eventually activated.  Formal proof:

* each stage adds only finitely many elements;
* all new elements are larger than the previous height `X`;
* therefore, for any fixed element `x` added at some stage, no future stage adds smaller elements;
* only finitely many dormant elements below `x` can be activated before `x`;
* hence `x` is eventually the least dormant element.

### 7.3 Service schedule

Use a fair schedule that serves every activated element infinitely often after activation.

A Lean-friendly schedule is triangular:

\[
0;
\quad 0,1;
\quad 0,1,2;
\quad 0,1,2,3;
\quad\ldots
\]

At each stage, interpret the scheduled number as an activation index.  If it is less than the number of old active elements, serve that active element; otherwise serve `a₀`.  With the triangular schedule and activation count increasing by one each stage, every fixed activation index is valid and served infinitely often after it exists.

It may be easiest to prove a standalone lemma:

```lean
lemma exists_fair_service_schedule :
  ∃ serve : ℕ → ℕ,
    (∀ j, serve j ≤ j) ∧
    ∀ i, ∃ᶠ j in Filter.atTop, serve j = i
```

Then active elements are stored in activation order, and at stage `j` serve the element with index `serve j`.

### 7.4 Prime choice and reciprocal budget

At activation step `j`, choose the personal prime `m_b` satisfying:

```lean
m_b > currentX
23 ≤ m_b
m_b % 4 = 3
(1 : ℝ) / m_b ≤ ε_j
```

where `∑ ε_j ≤ η`, e.g. `ε_j = 2^(-(j+4))`.

Then every finite active product has density at least `δ₀=1-η`.

### 7.5 Definition of the final set

Let `st j` be the recursive sequence of stage states.  Define

```lean
def A : Set ℕ := {n | ∃ j, n ∈ (st j).S}
```

Because `S_j⊆S_{j+1}`, this is an increasing union.

---

## 8. Verification of the final theorem

### 8.1 `A` is an asymptotic basis of order 2

Each stage extends coverage from the fixed lower endpoint `coverStart` to a larger endpoint.  The endpoints go to infinity because `L_Z` can be chosen arbitrarily large at every stage.

Therefore:

\[
\forall n\ge coverStart,
\quad n\in 2A.
\]

Lean proof shape:

```lean
have hR_unbounded : ∀ n, ∃ j, n ≤ (st j).R := ...
intro n hn
obtain ⟨j, hj⟩ := hR_unbounded n
have : n ∈ twoFoldFinset (st j).S := (st j).coverage n hn hj
exact twoFold_mono (stage_subset_A j) this
```

### 8.2 `A` has positive upper density

At the end of infinitely many stages, the tail

\[
Z_j=[K_j,K_j+L_{Z,j}]_{D_j}^{(M_j)}
\]

is contained in `A` and was chosen to satisfy

\[
\#Z_j\ge \frac{\delta_0}{4}(K_j+L_{Z,j}).
\]

At endpoint

\[
x_j=K_j+L_{Z,j},
\]

we have

\[
\#(A\cap[1,x_j])\ge \#Z_j
\ge \frac{\delta_0}{4}x_j.
\]

Since `x_j→∞`, this proves positive upper density.  Use `ε=δ₀/4`.

### 8.3 Every element has a positive-density private set

Fix `a∈A`.

1. By least-dormant activation, `a` is eventually activated.
2. By the fair service schedule, `a` is served infinitely many times after activation.
3. Each service stage for `a` produces a protected finite block

   \[
   B_{a,j}\subset E_A(a)
   \]

   below an endpoint `Y_j=R_j-X_j`.
4. The block is permanent because all later elements are larger than `Y_j`.
5. The stage chooses parameters so that

   \[
   \#B_{a,j}\ge \frac{\delta_0}{8m_a}Y_j.
   \]

6. The endpoints `Y_j` for service stages of `a` go to infinity.

Therefore `privateSet A a` has positive upper density, with witness

\[
\varepsilon_a=\frac{\delta_0}{8m_a}>0.
\]

Lean proof shape:

```lean
have hserved_inf : ∃ᶠ j in atTop, servedAt j a := ...
let eps := δ0 / (8 * m a)
have eps_pos : 0 < eps := ...
refine ⟨eps, eps_pos, ?_⟩
intro N
obtain ⟨j, hj_ge, hserved⟩ := frequently_atTop.mp hserved_inf N
let Y := protectedEndpoint j a
have hY_ge : N ≤ Y := ... -- choose j late enough
have hcount : eps * Y ≤ #(privateSet A a ∩ [1,Y]) := ...
exact ⟨Y, hY_ge, hcount⟩
```

### 8.4 Minimality follows

If `a∈A`, then `privateSet A a` has positive upper density, hence is nonempty and in fact infinite.  Therefore `A\{a}` fails to represent infinitely many sufficiently large integers.  So `A\{a}` is not an asymptotic basis of order 2.

This proves minimality if desired as a corollary:

```lean
theorem erdos330_minimal_corollary :
  ∃ A : Set ℕ,
    IsAsymptoticBasisOfOrderTwo A ∧
    MinimalAsymptoticBasisTwo A ∧
    0 < upperDensity A ∧
    ∀ a ∈ A, 0 < upperDensity (privateSet A a)
```

---

## 9. Suggested implementation order

### Milestone 1 — Definitions and density-free finite-stage theorem

Implement:

* `twoFold`, `privateSet`;
* residue blocks;
* finite interval and residue counting utilities;
* `StageState` without density conclusions;
* abstract `CRTGadget` interface;
* stage coverage and isolation using the abstract gadget.

Do not prove the QR/safe-pair/CRT construction yet.

### Milestone 2 — Global construction with abstract stage certificates

Assume a stage extension theorem producing:

* next stage state;
* coverage extension;
* a protected private block for the served element;
* a dense tail.

Formalise the priority argument:

* least-dormant activation activates every eventual element;
* fair service serves every activated element infinitely often;
* final `A` is an asymptotic basis;
* final `A` has positive upper density;
* every element has positive-private upper density.

This proves the theorem from abstract stage certificates.

### Milestone 3 — Local activation and stage extension

Prove the local reservoir lemma, helper block coverage, middle interval lemma, and the concrete stage extension theorem from the CRT gadget.

This is mostly modular arithmetic and interval arithmetic.

### Milestone 4 — CRT gadget construction

Formalise the selected-coordinate construction and the nonselected two-safe-pairs construction.

This includes:

* coordinate-product representation;
* CRT equivalence to `ZMod M`;
* cardinality of allowed residue products;
* selected-coordinate sum analysis;
* `T_a+T_a` complement identity;
* `D_P+T_a=full`;
* selected-coordinate privacy facts;
* base projection fact for activation.

### Milestone 5 — Quadratic-residue lemma

Prove the QR lemma.  This is the most independent finite-field subproject and can be delayed.

---

## 10. Risk register

### Risk 1: quadratic-character API

The QR lemma may be the most API-sensitive finite algebra step.  The proof is elementary, but formalising the character sum may require locating or building Legendre-symbol/quadratic-character lemmas.

Mitigation: isolate it in a small file and keep the rest of the proof parameterised by the selected-coordinate lemma.

### Risk 2: CRT representation overhead

The finite gadget is easiest on the product

\[
\prod_{b\in P}\mathbb F_{m_b},
\]

whereas interval residue blocks are easiest in `ZMod M`.  Bridging these via CRT can be tedious.

Mitigation: define a `ResidueModel P` structure containing both the product representation and an equivalence to `ZMod M`.  Push all coordinate reasoning through this structure.

### Risk 3: interval arithmetic

The proof has many inequalities involving `N,L,K,R,X,H,M`.  Natural-number subtraction can be annoying.

Mitigation: either use integer intervals in `ℤ`, or phrase all interval endpoints with additive inequalities and avoid truncated subtraction.  The proof itself already uses integer intervals; Lean may be smoother if residue blocks are sets of `ℤ` and are later intersected with `ℕ` when defining `A`.

If staying in `ℕ`, impose strict inequalities before using expressions like `R-X` and prove positivity early.

### Risk 4: upper-density API

If the existing upper-density API is heavy, first prove the theorem using the subsequence-witness definition `HasPositiveUpperDensity`.  Then bridge to the official definition later.

### Risk 5: scheduling proof

The least-dormant and fair-service arguments are conceptually simple but can be bookkeeping-heavy.

Mitigation: prove abstract lemmas about monotone finite stage sets whose new elements are above the previous height.  Then instantiate them with the construction.

---

## 11. A compact dependency graph

```text
QR lemma
   ↓
selected-coordinate gadget
   ↓
CRT gadget ← two-safe-pairs lemma
   ↓
local activation reservoir
   ↓
helper block coverage + middle interval coverage
   ↓
one-stage extension
   ↓
priority construction
   ↓
final A is an asymptotic basis, has positive upper density,
and every a∈A has positive-upper-density private set
```

For development, reverse the dependency graph by using interfaces:

```text
abstract stage certificate
   ↓
global theorem
   ↓
concrete stage from abstract CRT gadget
   ↓
CRT gadget from finite lemmas
   ↓
QR lemma and safe-pairs lemma
```

---

## 12. Recommended theorem scoping

First formalise exactly this:

```lean
theorem erdos330_upper_density_exact_two_sums :
  ∃ A : Set ℕ,
    IsAsymptoticBasisTwo A ∧
    HasPositiveUpperDensity A ∧
    ∀ a ∈ A, HasPositiveUpperDensity (privateSet A a)
```

Then prove as corollaries:

```lean
theorem erdos330_minimal :
  ∃ A : Set ℕ,
    IsMinimalAsymptoticBasisTwo A ∧
    HasPositiveUpperDensity A ∧
    ∀ a ∈ A, HasPositiveUpperDensity (privateSet A a)
```

and, if needed later, bridge `HasPositiveUpperDensity` to the library `upperDensity` formulation.

Do not initially target:

* positive lower density;
* existence of natural density;
* exact compatibility with a formal-conjectures statement using `Set.HasPosDensity`, if that means actual density rather than upper density;
* the “at most two summands” convention.

---

## 13. Bottom-line formalisation assessment

The supplied proof makes #330 a stronger target than before.  The construction is self-contained and does not require analytic number theory.  The only genuinely nontrivial external-looking ingredient in the written proof, Dirichlet’s theorem for primes in arithmetic progressions, is unnecessary and can be replaced by the elementary infinitude of primes congruent to `3 mod 4`.

The largest Lean tasks are:

1. the finite quadratic-residue sum lemma;
2. the CRT/product-residue bookkeeping;
3. the stage inequality bookkeeping;
4. the global priority/scheduling argument.

None of these should require unproved axioms.  The proof is long, but it decomposes very cleanly into finite lemmas, a one-stage extension theorem, and a final priority construction.
