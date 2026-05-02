/-
Solving Erdős Problem #355 (https://www.erdosproblems.com/355), Vjekoslav Kovač and I proved that there exists a lacunary sequence of positive integers whose reciprocal sums represent all rational numbers in an interval.

W. van Doorn and V. Kovač, Lacunary sequences whose reciprocal sums represent all rationals in an interval. arXiv:2509.24971 (2025).

Below you can find a formalization of the main results of our paper, obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

More precisely, for a parameter $λ > 1$, let us say that a sequence $A = \{a_1 < a_2 < \cdots\}$ of positive integers is $λ$-lacunary if $a_{i+1} \ge λ a_i$ for all $i$. Let's further define $P(A^{-1})}$ to be the set of all rationals that can be written as a finite sum of reciprocals of elements in $A$, and define $R(λ)$ to be the least upper bound on the length $\beta - \alpha$ of an interval $(\alpha, \beta)$ for which there exists a $λ$-lacunary sequence of positive integers $A$ such that $P(A^{-1})$ contains all rational numbers from $(\alpha, \beta)$. Then at the end of the Lean-file below the following four theorems are proven.

Theorem 1. For all $λ \in (1, 2)$ there exists a $λ$-lacunary sequence $A = \{a_1 < a_2 < \cdots\}$ of positive integers with $\frac{a_{i+1}}{a_i} \to 2$ such that $P(A^{-1})$ contains every rational in the interval $[0, 2]$.

Theorem 2. For all $λ \in (1, 2)$ we have $R(λ) = \sum_{i=1}^{\infty} \frac{1}{b_i}$.

Theorem 3. For all $Λ \ge 2$ and all $λ$ with $1 < λ < Λ/(Λ-1)$, there exists a $λ$-lacunary sequence $A = \{a_1 < a_2 < \cdots\}$ of positive integers for which infinitely many indices $i$ exist with $a_{i+1} > Λ a_i$, and such that $P(A^{-1})$ contains every positive rational smaller than $\frac{1}{a_i}$.

Theorem 4. If $A$ is a set of positive integers with $2A ⊆ A$ and such that $A$ contains a multiple of each odd integer, then $P(A^{-1})$ contains every positive rational smaller than $\sum_{a \in A} \frac{1}{a}$.

At the very end of the file you can find the statement of Erdős Problem #355 taken from the Formal Conjectures project by Google DeepMind, which we also prove.

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/355.lean

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace Erdos355Oracle

/-
Basic definitions of e.g. lacunarity, the function $R(λ)$, and the assumption on $S$ for Theorem 4. These definitions are sufficient in order to understand the statements of our results at the end.
-/

/-
For a parameter $λ  > 1$, we say that a sequence $n_1, n_2, \ldots$ is $λ$-lacunary if $n_{i+1} \ge λ n_i$ for all $i ≥ 1$. It is simply said to be lacunary if it is $λ$-lacunary for some $λ > 1$.
-/
def IsLambdaLacunary (lambda : ℝ) (seq : ℕ → ℝ) : Prop :=
  ∀ i, seq (i + 1) / seq i ≥ lambda

def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lambda_val > 1, ∀ i ≥ 1, (a (i + 1) : ℝ) / a i ≥ lambda_val

/-
Given a sequence, SubsetSums is the set of finite sums of elements of the sequence.
-/
def SubsetSums (seq : ℕ → ℝ) : Set ℝ :=
  { s | ∃ t : Finset ℕ, s = ∑ i ∈ t, seq i }

/-
$R(λ)$ is the supremum of lengths of intervals filled by $λ$-lacunary sequences.
-/
def FillsInterval (lambda : ℝ) (alpha beta : ℝ) : Prop :=
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Set.Ioo alpha beta ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i)

noncomputable def R_lambda (lambda : ℝ) : ℝ :=
  sSup {len | ∃ alpha beta, beta - alpha = len ∧ FillsInterval lambda alpha beta}

/-
The property S_cond requires a set $S$ to contain $2S$, as well as a multiple of every odd integer.
-/
def S_cond (S : Set ℕ) : Prop :=
  (∀ s ∈ S, s > 0) ∧ (∀ s ∈ S, 2 * s ∈ S) ∧ (∀ k, Odd k → ∃ s ∈ S, k ∣ s)

/-
Definition of the target interval $[0, \sum f_i)$ which is $[0, \infty)$ if the sum diverges.
-/
noncomputable def TargetInterval (f : ℕ → ℝ) : Set ℝ :=
  if Summable f then Set.Ico 0 (∑' i, f i) else Set.Ici 0

/-
The set $S$ $x_m$-densely fills in the segment $[a, b]$, i.e., it divides this segment into sub-intervals of length at most $x_m$.
-/
def DenselyFills (S : Set ℝ) (a b δ : ℝ) : Prop :=
  S ⊆ Icc a b ∧ a ∈ S ∧ b ∈ S ∧
  ∀ x ∈ Icc a b, ∃ s1 ∈ S, ∃ s2 ∈ S, s1 ≤ x ∧ x ≤ s2 ∧ s2 - s1 ≤ δ

/-
If a set $S$ $\delta$-densely fills $[0, U]$ and $x \le U + \delta$, then the union of $S$ and $S+x$ $\delta$-densely fills $[0, U+x]$.
-/
lemma densely_fills_union (S : Set ℝ) (U x δ : ℝ)
  (hS : DenselyFills S 0 U δ)
  (hx : 0 < x)
  (h_gap : x ≤ U + δ) :
  DenselyFills (S ∪ {s + x | s ∈ S}) 0 (U + x) δ := by
  obtain ⟨ hS_sub, hS0, hSU, hS_dense ⟩ := hS;
  refine' ⟨ _, _, _, _ ⟩;
  · exact Set.union_subset ( hS_sub.trans ( Set.Icc_subset_Icc_right ( by linarith ) ) ) ( Set.image_subset_iff.mpr fun s hs => ⟨ by linarith [ Set.mem_Icc.mp ( hS_sub hs ) ], by linarith [ Set.mem_Icc.mp ( hS_sub hs ) ] ⟩ );
  · exact Or.inl hS0;
  · exact Or.inr ⟨ U, hSU, rfl ⟩;
  · intro y hy
    by_cases hy_case : y ≤ U ∨ y ≥ x;
    · cases hy_case <;> simp_all +decide [ Set.subset_def ];
      · rcases hS_dense y hy.1 ‹_› with ⟨ s1, hs1, s2, hs2, h1, h2, h3 ⟩ ; exact ⟨ s1, Or.inl hs1, s2, Or.inl hs2, h1, h2, h3 ⟩;
      · obtain ⟨ s1, hs1, s2, hs2, hs1_le, hs2_le, hs2_le' ⟩ := hS_dense ( y - x ) ( by linarith ) ( by linarith ) ; exact ⟨ s1 + x, Or.inr ⟨ s1, hs1, rfl ⟩, s2 + x, Or.inr ⟨ s2, hs2, rfl ⟩, by linarith, by linarith, by linarith ⟩ ;
    · exact ⟨ U, Or.inl hSU, x, Or.inr ⟨ 0, hS0, by ring ⟩, by push_neg at hy_case; linarith, by push_neg at hy_case; linarith, by push_neg at hy_case; linarith ⟩

/-
Suppose that $x_1>x_2>\cdots>x_m>0$ are real numbers satisfying
\[ x_i \leqslant \sum_{j=i+1}^{m}x_j + x_m \]
for all $i$ with $1 \le i \le m-1$. Then the set
\[ \Big\{ \sum_{i\in T}x_i : T\subseteq\{1,2,\ldots,m\} \Big\} \]
$x_m$-densely fills in the segment
$[0,\sum_{i=1}^{m}x_i]$,
i.e., it divides this segment into sub-intervals of length at most $x_m$.
-/
lemma lm_reals (m : ℕ) (hm : m ≥ 1) (x : ℕ → ℝ)
  (h_pos : ∀ i ∈ Finset.Icc 1 m, 0 < x i)
  (h_dec : ∀ i ∈ Finset.Icc 1 (m - 1), x (i + 1) < x i)
  (h_cond : ∀ i ∈ Finset.Icc 1 (m - 1), x i ≤ (∑ j ∈ Finset.Icc (i + 1) m, x j) + x m) :
  DenselyFills { s | ∃ t ⊆ Finset.Icc 1 m, s = ∑ i ∈ t, x i } 0 (∑ i ∈ Finset.Icc 1 m, x i) (x m) := by
  induction' m with m ih generalizing x;
  · contradiction;
  · have h_ind : DenselyFills {s | ∃ t ⊆ Finset.Icc 2 (m + 1), s = ∑ i ∈ t, x i} 0 (∑ i ∈ Finset.Icc 2 (m + 1), x i) (x (m + 1)) := by
      by_cases hm : m ≥ 1;
      · convert ih hm ( fun i => x ( i + 1 ) ) _ _ _ using 1;
        · ext s
          constructor
          intro hs
          obtain ⟨t, ht_sub, ht_sum⟩ := hs
          use Finset.image (fun i => i - 1) t
          simp [ht_sum];
          · exact ⟨ Finset.image_subset_iff.mpr fun i hi => Finset.mem_Icc.mpr ⟨ Nat.le_sub_one_of_lt <| Finset.mem_Icc.mp ( ht_sub hi ) |>.1, Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Icc.mp ( ht_sub hi ) |>.2 ] ⟩, by rw [ Finset.sum_image <| by intros i hi j hj hij; linarith [ Nat.sub_add_cancel <| show 1 ≤ i from by linarith [ Finset.mem_Icc.mp ( ht_sub hi ) |>.1 ], Nat.sub_add_cancel <| show 1 ≤ j from by linarith [ Finset.mem_Icc.mp ( ht_sub hj ) |>.1 ] ] ] ; exact Finset.sum_congr rfl fun i hi => by rw [ Nat.sub_add_cancel <| show 1 ≤ i from by linarith [ Finset.mem_Icc.mp ( ht_sub hi ) |>.1 ] ] ⟩;
          · rintro ⟨ t, ht, rfl ⟩ ; use Finset.image ( fun i => i + 1 ) t; simp_all +decide [ Finset.subset_iff ] ;
        · erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ];
        · exact fun i hi => h_pos _ <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩;
        · exact fun i hi => h_dec _ <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt ( Finset.mem_Icc.mp hi |>.2 ) <| Nat.pred_lt <| ne_bot_of_gt hm ⟩;
        · intro i hi
          specialize h_cond ( i + 1 )
          have icc_succ : ∀ a b : ℕ, Finset.Icc (a + 1) b = Finset.Ioc a b := fun a b => by
            ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
          rcases m with ( _ | m ) <;> simp_all +decide [Finset.sum_Ioc_succ_top] ;
          convert h_cond using 2 ; rw [ show Finset.Ioc ( i + 1 ) ( m + 1 ) = Finset.image ( fun k => k + 1 ) ( Finset.Ioc i m ) from ?_, Finset.sum_image <| by intros a ha b hb hab; linarith ] ; aesop;
      · interval_cases m ; norm_num [ DenselyFills ];
        linarith [ h_pos 1 ( by norm_num ) ];
    have h_union : DenselyFills ({s | ∃ t ⊆ Finset.Icc 2 (m + 1), s = ∑ i ∈ t, x i} ∪ {s + x 1 | s ∈ {s | ∃ t ⊆ Finset.Icc 2 (m + 1), s = ∑ i ∈ t, x i}}) 0 (∑ i ∈ Finset.Icc 1 (m + 1), x i) (x (m + 1)) := by
      convert densely_fills_union _ _ _ _ h_ind _ _ using 1;
      · erw [ Finset.Icc_eq_cons_Ioc, Finset.sum_cons, add_comm ] <;> norm_num [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      · exact h_pos 1 <| by norm_num;
      · rcases m with ( _ | m ) <;> aesop;
    convert h_union using 1;
    ext s;
    constructor;
    · rintro ⟨ t, ht, rfl ⟩;
      by_cases h1 : 1 ∈ t;
      · exact Or.inr ⟨ ∑ i ∈ t.erase 1, x i, ⟨ t.erase 1, fun i hi => Finset.mem_Icc.mpr ⟨ Nat.lt_of_le_of_ne ( Finset.mem_Icc.mp ( ht ( Finset.mem_of_mem_erase hi ) ) |>.1 ) ( Ne.symm <| by aesop ), Finset.mem_Icc.mp ( ht ( Finset.mem_of_mem_erase hi ) ) |>.2 ⟩, rfl ⟩, by rw [ Finset.sum_erase_add _ _ h1 ] ⟩;
      · exact Or.inl ⟨ t, fun i hi => Finset.mem_Icc.mpr ⟨ Nat.lt_of_le_of_ne ( Finset.mem_Icc.mp ( ht hi ) |>.1 ) ( Ne.symm <| by rintro rfl; exact h1 hi ), Finset.mem_Icc.mp ( ht hi ) |>.2 ⟩, rfl ⟩;
    · rintro ( ⟨ t, ht, rfl ⟩ | ⟨ s, ⟨ t, ht, rfl ⟩, rfl ⟩ );
      · exact ⟨ t, Finset.Subset.trans ht ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ), rfl ⟩;
      · use Insert.insert 1 t;
        simp_all +decide [ Finset.subset_iff ];
        exact ⟨ fun a ha => by linarith [ ht ha ], by rw [ Finset.sum_insert ( show 1∉t from fun h => by linarith [ ht h ] ) ] ; ring ⟩

/-
The finite sequence $1/n_0, \dots, 1/n_{m_K}$ satisfies the condition of `lm_reals`.
-/
lemma finite_seq_satisfies_condition (n : ℕ → ℕ) (m : ℕ → ℕ) (K : ℕ)
  (h_m_mono : StrictMono m)
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  ∀ i < m K, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m K), (1 : ℝ) / n j) + (1 : ℝ) / n (m K) := by
  induction' K with K ih;
  · assumption;
  · intro i hi;
    by_cases hi' : i < m K;
    · refine le_trans ( ih i hi' ) ?_;
      rw [ show ( Finset.Ioc i ( m ( K + 1 ) ) ) = Finset.Ioc i ( m K ) ∪ Finset.Ioc ( m K ) ( m ( K + 1 ) ) from ?_, Finset.sum_union ] <;> norm_num [ h_m_mono.le_iff_le ];
      · have := h_ineq_k K ( m K ) le_rfl ( h_m_mono K.lt_succ_self ) ; norm_num at * ; linarith;
      · rw [ Finset.Ioc_union_Ioc_eq_Ioc ] <;> linarith [ h_m_mono K.lt_succ_self ];
    · exact h_ineq_k K i ( le_of_not_gt hi' ) hi

/-
If a set $S$ of multiples of $\delta$ densely fills $[0, U]$, then it contains all multiples of $\delta$ in $[0, U]$.
-/
lemma dense_and_divisible_implies_all_multiples (S : Set ℝ) (U δ : ℝ)
  (h_dense : DenselyFills S 0 U δ)
  (h_div : ∀ s ∈ S, ∃ k : ℤ, s = k * δ)
  (h_delta_pos : 0 < δ) :
  {x ∈ Set.Icc 0 U | ∃ k : ℤ, x = k * δ} ⊆ S := by
  intro x hx
  obtain ⟨hx_bounds, k, hk⟩ := hx
  obtain ⟨s1, hs1, s2, hs2, hs1_le_x, hx_le_s2, hs2_s1_le_delta⟩ := h_dense.2.2.2 x hx_bounds
  obtain ⟨k₁, rfl⟩ := h_div s1 hs1
  obtain ⟨k₂, rfl⟩ := h_div s2 hs2
  have h_eq : k₁ * δ = x ∨ k₂ * δ = x := by
    rcases lt_trichotomy k₁ k with hk₁ | rfl | hk₁
    · right
      have hcast : (k₁ : ℝ) + 1 ≤ k := by exact_mod_cast hk₁
      nlinarith
    · left
      linarith
    · exfalso
      have hcast : (k : ℝ) + 1 ≤ k₁ := by exact_mod_cast hk₁
      nlinarith
  rcases h_eq with h | h
  · rw [← h]; exact hs1
  · rw [← h]; exact hs2

/-
The finite subset sums contain all multiples of $1/n_{m_K}$ in the range.
-/
lemma finite_subset_sums_contain_multiples (n : ℕ → ℕ) (m : ℕ → ℕ) (K : ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_mono : StrictMono n)
  (h_m_mono : StrictMono m)
  (h_div_m : ∀ k : ℕ, ∀ j < m k, n j ∣ n (m k))
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  let M := m K
  let S := { s | ∃ t ⊆ Finset.range (M + 1), s = ∑ i ∈ t, (1 : ℝ) / n i }
  let U := ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / n i
  let δ := (1 : ℝ) / n M
  {x ∈ Set.Icc 0 U | ∃ k : ℤ, x = k * δ} ⊆ S := by
  intros M S U δ hS
  have h_dense : DenselyFills S 0 U δ := by
    have h_apply_lm_reals : DenselyFills { s | ∃ t ⊆ Finset.Icc 1 (M + 1), s = ∑ i ∈ t, (1 : ℝ) / n (i - 1) } 0 (∑ i ∈ Finset.Icc 1 (M + 1), (1 : ℝ) / n (i - 1)) ((1 : ℝ) / n M) := by
      apply_rules [ lm_reals ];
      · linarith;
      · exact fun i hi => one_div_pos.mpr <| Nat.cast_pos.mpr <| h_n_pos _;
      · intro i hi; gcongr <;> aesop;
      · have h_apply_finite_seq : ∀ i < M, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i M, (1 : ℝ) / n j) + (1 : ℝ) / n M := by
          apply_rules [ finite_seq_satisfies_condition ];
        have icc_succ : ∀ a b : ℕ, Finset.Icc (a + 1) b = Finset.Ioc a b := fun a b => by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
        intro i hi
        rcases i with _ | i
        · have := (Finset.mem_Icc.mp hi).1
          omega
        · have hiM : i < M := by
            have := (Finset.mem_Icc.mp hi).2
            omega
          refine le_trans ( h_apply_finite_seq i hiM ) ?_;
          have h_range : Finset.Icc (i + 2) (M + 1) =
              (Finset.Ioc i M).image (fun x => x + 1) := by
            ext x
            constructor
            · intro hx
              have hx' := Finset.mem_Icc.mp hx
              refine Finset.mem_image.mpr ⟨x - 1, ?_, ?_⟩
              · exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
              · omega
            · intro hx
              obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
              have hy' := Finset.mem_Ioc.mp hy
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          rw [h_range, Finset.sum_image]
          · simp [Nat.add_sub_cancel, add_comm, add_left_comm, add_assoc]
          · intro a ha b hb hab
            exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)
    convert h_apply_lm_reals using 1;
    · ext; simp [S, Finset.Icc];
      constructor <;> rintro ⟨ t, ht, rfl ⟩;
      · use t.image (fun i => i + 1);
        simp_all +decide [ Finset.subset_iff ];
        exact fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ ht hx ], by linarith [ ht hx ] ⟩;
      · refine ⟨t.image (fun x => x - 1), ?_, ?_⟩
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_range.mpr (by
            have hy' := Finset.mem_Icc.mp (ht hy)
            omega)
        · rw [Finset.sum_image]
          intro a ha b hb hab
          have ha' := (Finset.mem_Icc.mp (ht ha)).1
          have hb' := (Finset.mem_Icc.mp (ht hb)).1
          have h_eq : a - 1 + 1 = b - 1 + 1 := by
            simpa [Nat.succ_eq_add_one] using congrArg Nat.succ hab
          rwa [Nat.sub_add_cancel ha', Nat.sub_add_cancel hb'] at h_eq
    · erw [ Finset.sum_Ico_eq_sum_range ] ; ac_rfl;
  have h_div : ∀ s ∈ S, ∃ k : ℤ, s = k * δ := by
    intro s hs
    obtain ⟨t, ht_sub, ht_eq⟩ := hs
    have h_div : ∀ i ∈ t, ∃ k : ℤ, (1 / (n i : ℝ)) = k * δ := by
      intro i hi
      have h_div_i : n i ∣ n M := by
        by_cases hiM : i < m K;
        · exact h_div_m K i hiM;
        · rw [ show i = m K from le_antisymm ( Finset.mem_range_succ_iff.mp ( ht_sub hi ) ) ( not_lt.mp hiM ) ]
      obtain ⟨k, hk⟩ := h_div_i
      use k
      field_simp [hk];
      rw [ mul_div, div_eq_div_iff ] <;> norm_cast <;> nlinarith [ h_n_pos i, h_n_pos M ];
    choose! k hk using h_div; exact ⟨ ∑ i ∈ t, k i, by push_cast; rw [ ht_eq, Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun i hi => hk i hi ⟩ ;
  exact fun h => dense_and_divisible_implies_all_multiples S U δ h_dense h_div ( by exact one_div_pos.mpr <| Nat.cast_pos.mpr <| h_n_pos _ ) ⟨ h.1, h.2 ⟩

/-
The main proposition, which states that under the given conditions, the set of subset sums of $1/n_i$ is exactly the set of rational numbers in the interval $[0, \sum 1/n_i)$.
-/
lemma prop_general (n : ℕ → ℕ) (m : ℕ → ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_mono : StrictMono n)
  (h_m_mono : StrictMono m)
  (h_div : ∀ k > 0, ∃ i, k ∣ n i)
  (h_div_m : ∀ k : ℕ, ∀ j < m k, n j ∣ n (m k))
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  SubsetSums (fun i => (1 : ℝ) / n i) =
    (TargetInterval (fun i => (1 : ℝ) / n i)) ∩ {x | ∃ q : ℚ, x = q} := by
  apply Set.eq_of_subset_of_subset;
  · unfold TargetInterval SubsetSums;
    by_cases h : Summable ( fun i => ( n i : ℝ ) ⁻¹ ) <;> simp_all +decide [ Set.subset_def ];
    · refine' fun x s hx => ⟨ ⟨ Finset.sum_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _, _ ⟩, ⟨ ∑ i ∈ s, ( n i : ℚ ) ⁻¹, by push_cast; rfl ⟩ ⟩;
      refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( s ∪ { s.sup id + 1 } ) ( fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) h );
      rw [ Finset.sum_union ] <;> norm_num [ h_n_pos ];
      exact fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) ( Nat.lt_succ_self _ );
    · exact fun x t hx => ⟨ Finset.sum_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _, ⟨ ∑ i ∈ t, ( n i : ℚ ) ⁻¹, by push_cast; rfl ⟩ ⟩;
  · intro x hx
    obtain ⟨K1, hK1⟩ : ∃ K1, x ≤ ∑ i ∈ Finset.range (m K1 + 1), (1 : ℝ) / n i := by
      by_cases h_summable : Summable (fun i => (1 : ℝ) / n i);
      · have h_summable : Filter.Tendsto (fun K => ∑ i ∈ Finset.range (m K + 1), (1 : ℝ) / n i) Filter.atTop (nhds (∑' i, (1 : ℝ) / n i)) := by
          exact h_summable.hasSum.tendsto_sum_nat.comp <| Filter.tendsto_atTop_mono ( fun K => Nat.le_succ _ ) <| h_m_mono.tendsto_atTop;
        exact Filter.Eventually.exists ( h_summable.eventually ( le_mem_nhds <| show x < ∑' i : ℕ, 1 / ( n i : ℝ ) from hx.1 |> fun h => by unfold TargetInterval at h; aesop ) ) |> fun ⟨ K, hK ⟩ => ⟨ K, hK ⟩;
      · have h_unbounded : Filter.Tendsto (fun K => ∑ i ∈ Finset.range (m K + 1), (1 : ℝ) / n i) Filter.atTop Filter.atTop := by
          exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h_summable |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun K => Nat.le_succ _ ) <| h_m_mono.tendsto_atTop;
        exact ( h_unbounded.eventually_ge_atTop x ) |> fun h => h.exists
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d > 0 ∧ ∃ q : ℚ, x = q ∧ q.den = d := by
      exact ⟨ hx.2.choose.den, Nat.cast_pos.mpr hx.2.choose.pos, hx.2.choose, hx.2.choose_spec, rfl ⟩
    obtain ⟨i0, hi0⟩ : ∃ i0, d ∣ n i0 := by
      exact h_div d hd.1 |> fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩
    obtain ⟨K, hK⟩ : ∃ K ≥ K1, m K > i0 := by
      -- Since $m$ is strictly monotone, it is unbounded. Therefore, there exists some $K$ such that $m K > i0$.
      obtain ⟨K, hK⟩ : ∃ K, m K > i0 := by
        exact ⟨ _, h_m_mono.id_le _ ⟩;
      exact ⟨ _, le_max_left _ _, hK.trans_le <| h_m_mono.monotone <| le_max_right _ _ ⟩
    have h_div_mk : d ∣ n (m K) := by
      exact dvd_trans hi0 ( h_div_m K i0 hK.2 )
    have h_q_mult : ∃ k : ℤ, x = k * (1 : ℝ) / n (m K) := by
      obtain ⟨q, hq⟩ : ∃ q : ℚ, x = q ∧ q.den = d := hd.right
      obtain ⟨k, hk⟩ : ∃ k : ℤ, q = k / d := by
        exact ⟨ q.num, by simpa [ hq.2 ] using q.num_div_den.symm ⟩
      use k * (n (m K) / d);
      simp_all +decide [ne_of_gt, mul_assoc, mul_comm, div_eq_mul_inv]
    have h_q_sum : x ∈ { s | ∃ t ⊆ Finset.range (m K + 1), s = ∑ i ∈ t, (1 : ℝ) / n i } := by
      have h_q_sum : {x ∈ Set.Icc 0 (∑ i ∈ Finset.range (m K + 1), (1 : ℝ) / n i) | ∃ k : ℤ, x = k * (1 : ℝ) / n (m K)} ⊆ { s | ∃ t ⊆ Finset.range (m K + 1), s = ∑ i ∈ t, (1 : ℝ) / n i } := by
        convert finite_subset_sums_contain_multiples n m K h_n_pos h_n_mono h_m_mono h_div_m h_ineq_0 h_ineq_k using 1;
        simp +decide only [mul_one_div];
        norm_num;
      apply h_q_sum; exact ⟨⟨by
      unfold TargetInterval at hx; aesop;, by
        exact hK1.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith [ h_m_mono.monotone hK.1 ] ) ) fun _ _ _ => by positivity )⟩, h_q_mult⟩;
    exact (by
    exact ⟨ h_q_sum.choose, h_q_sum.choose_spec.2 ⟩)

/-
If $n_{i+1} \le 2n_i$, then $1/n_i \le \sum_{j=i+1}^M 1/n_j + 1/n_M$.
-/
lemma remark_cond (n : ℕ → ℕ) (M : ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_growth : ∀ i, n (i + 1) ≤ 2 * n i)
  (i : ℕ) (hi : i < M) :
  (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i M, (1 : ℝ) / n j) + (1 : ℝ) / n M := by
  induction' hi with k hk ih <;> norm_num [ Finset.sum_Ioc_succ_top ] at *;
  · field_simp;
    rw [ div_le_div_iff₀ ] <;> norm_cast <;> linarith [ h_n_pos i, h_n_pos ( i + 1 ), h_n_growth i ];
  · rw [ Finset.sum_Ioc_succ_top ] <;> try linarith;
    linarith [ show ( n k : ℝ ) ⁻¹ ≤ ( n ( k + 1 ) : ℝ ) ⁻¹ + ( n ( k + 1 ) : ℝ ) ⁻¹ by rw [ inv_eq_one_div, inv_eq_one_div, ← add_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith [ h_n_pos k, h_n_pos ( k + 1 ), h_n_growth k ] ]

/-
Any rational number in the target interval is a subset sum.
-/
lemma target_subset_subset_sums (n : ℕ → ℕ) (m : ℕ → ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_mono : StrictMono n)
  (h_m_mono : StrictMono m)
  (h_div : ∀ k > 0, ∃ i, k ∣ n i)
  (h_div_m : ∀ k : ℕ, ∀ j < m k, n j ∣ n (m k))
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  (TargetInterval (fun i => (1 : ℝ) / n i)) ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i) := by
  have := prop_general n m h_n_pos h_n_mono h_m_mono h_div h_div_m h_ineq_0 h_ineq_k ; aesop;

/-
If $Q$ is a power of 2, the lemma holds.
-/
lemma lemma_divisors_power_of_two (lambda : ℝ) (Q : ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q)
  (h_pow2 : ∃ k : ℕ, Q = 2 ^ k) :
  ∃ N : ℕ, Q ∣ N ∧ ∃ d : ℕ → ℕ, ∃ M : ℕ,
    d 0 = 1 ∧ d M = N ∧
    (∀ j ≤ M, d j ∣ N) ∧
    (StrictMonoOn d (Set.Icc 0 M)) ∧
    (∀ j < M, lambda ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
  obtain ⟨k, rfl⟩ := h_pow2;
  refine' ⟨ _, dvd_rfl, fun j => 2 ^ j, k, _, _, _, _, _ ⟩ <;> norm_num [ StrictMonoOn ];
  · exact fun j hj => pow_dvd_pow _ hj;
  · exact fun a ha b hb hab => pow_lt_pow_right₀ ( by norm_num ) hab;
  · norm_num [ pow_succ' ];
    exact fun _ _ => h_lambda.2.le

/-
If $Q$ is not a power of 2, then $\log_2 Q$ is irrational.
-/
lemma irrational_logb_two_of_not_pow_two (Q : ℕ) (hQ : Q > 0) (h_not_pow2 : ¬ ∃ k : ℕ, Q = 2 ^ k) :
  Irrational (Real.logb 2 Q) := by
    -- Assume for contradiction that $\log_2 Q$ is rational. Then there exist positive integers $p$ and $q$ with $\gcd(p, q) = 1$ such that $\log_2 Q = p/q$.
    by_contra h_contra
    obtain ⟨p, q, hq_pos, hgcd, h_eq⟩ : ∃ p q : ℕ, 0 < q ∧ Nat.gcd p q = 1 ∧ Real.logb 2 Q = p / q := by
      unfold Irrational at h_contra;
      norm_num +zetaDelta at *;
      obtain ⟨ y, hy ⟩ := h_contra; exact ⟨ y.num.natAbs, y.den, Nat.cast_pos.mpr y.pos, y.reduced, by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ y by exact_mod_cast hy.symm ▸ Real.logb_nonneg one_lt_two ( Nat.one_le_cast.mpr hQ ) ) ), Rat.cast_def ] using hy.symm ⟩ ;
    -- Then we have $Q^q = 2^p$.
    have h_exp : Q^q = 2^p := by
      rw [ eq_div_iff ( by positivity ) ] at h_eq;
      rw [ ← @Nat.cast_inj ℝ ] ; push_cast ; rw [ ← Real.rpow_natCast _ p, ← h_eq, Real.rpow_mul ] <;> norm_num [ hQ ];
    have : Q ∣ 2 ^ p := h_exp ▸ dvd_pow_self _ hq_pos.ne'; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at this; aesop; )

/-
The fractional parts of natural multiples of an irrational number are dense in $[0, 1]$.
-/
lemma dense_fract_of_irrational (alpha : ℝ) (h_irr : Irrational alpha) :
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n : ℕ, a < Int.fract (n * alpha) ∧ Int.fract (n * alpha) < b := by
    -- Consider the circle group $S^1 = \mathbb{R}/\mathbb{Z}$, which is `AddCircle 1`.
    set G : Type := AddCircle (1 : ℝ);
    -- The element corresponding to $\alpha$ is $x = \alpha \pmod 1$.
    set x : G := QuotientAddGroup.mk alpha;
    -- Since $\alpha$ is irrational, $\alpha/1$ is irrational.
    have h_alpha_irr : Irrational (alpha / 1) := by
      simpa using h_irr;
    -- By `AddCircle.denseRange_zsmul_coe_iff`, the set $\{n x \mid n \in \mathbb{Z}\}$ is dense in $S^1$.
    have h_dense_z : DenseRange (fun n : ℤ => n • x) := by
      convert AddCircle.denseRange_zsmul_coe_iff.mpr _;
      exact h_alpha_irr;
    -- By `denseRange_zsmul_iff_nsmul`, the set $\{n x \mid n \in \mathbb{N}\}$ is dense in $S^1$.
    have h_dense_n : DenseRange (fun n : ℕ => n • x) := by
      convert denseRange_zsmul_iff_nsmul.mp h_dense_z;
    intro a b ha hb hb1
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (QuotientAddGroup.mk (n * alpha) : G) ∈ Metric.ball (QuotientAddGroup.mk (a + (b - a) / 2)) ((b - a) / 2) := by
      have := h_dense_n.exists_dist_lt ( QuotientAddGroup.mk ( a + ( b - a ) / 2 ) ) ( by linarith : 0 < ( b - a ) / 2 );
      obtain ⟨ n, hn ⟩ := this;
      use n;
      convert hn using 1;
      rw [ dist_comm ] ; aesop;
    erw [ Metric.mem_ball, dist_eq_norm ] at hn;
    erw [ QuotientAddGroup.norm_lt_iff ] at hn;
    obtain ⟨ m, hm₁, hm₂ ⟩ := hn;
    erw [ QuotientAddGroup.eq ] at hm₁;
    obtain ⟨ k, hk ⟩ := hm₁;
    norm_num [ Norm.norm ] at *;
    exact ⟨ n, by linarith [ abs_lt.mp hm₂, Int.fract_add_floor ( ( n : ℝ ) * alpha ), show ( Int.floor ( ( n : ℝ ) * alpha ) : ℝ ) = k by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith [ abs_lt.mp hm₂ ], by linarith [ abs_lt.mp hm₂ ] ⟩ ], by linarith [ abs_lt.mp hm₂, Int.fract_add_floor ( ( n : ℝ ) * alpha ), show ( Int.floor ( ( n : ℝ ) * alpha ) : ℝ ) = k by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith [ abs_lt.mp hm₂ ], by linarith [ abs_lt.mp hm₂ ] ⟩ ] ⟩

/-
If $Q$ is not a power of 2, we can find powers $a, b$ such that $Q^b / 2^a \in [\lambda, 2]$.
-/
lemma exists_powers_in_range (lambda : ℝ) (Q : ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q)
  (h_not_pow2 : ¬ ∃ k : ℕ, Q = 2 ^ k) :
  ∃ a b : ℕ, lambda ≤ (Q : ℝ) ^ b / 2 ^ a ∧ (Q : ℝ) ^ b / 2 ^ a ≤ 2 := by
    -- By `dense_fract_of_irrational`, there exists $b \in \mathbb{N}$ such that $\{b \alpha\} \in (x, 1)$.
    obtain ⟨b, hb⟩ : ∃ b : ℕ, b > 0 ∧ Int.fract (b * Real.logb 2 Q) ∈ Set.Ioo (Real.logb 2 lambda) 1 := by
      -- By `dense_fract_of_irrational`, since $Q$ is not a power of 2, $\log_2 Q$ is irrational, and the fractional parts of its multiples are dense in $[0, 1]$.
      have h_irr : Irrational (Real.logb 2 Q) := by
        apply irrational_logb_two_of_not_pow_two Q h_Q_pos h_not_pow2
      have h_dense : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n : ℕ, a < Int.fract (n * Real.logb 2 Q) ∧ Int.fract (n * Real.logb 2 Q) < b := by
        exact fun a b a_1 a_2 a_3 =>
          dense_fract_of_irrational (Real.logb 2 ↑Q) h_irr a b a_1 a_2 a_3
      have h_exists_b : ∃ b : ℕ, b > 0 ∧ Int.fract (b * Real.logb 2 Q) ∈ Set.Ioo (Real.logb 2 lambda) 1 := by
        obtain ⟨ b, hb₁, hb₂ ⟩ := h_dense ( Real.logb 2 lambda ) 1 ( Real.logb_nonneg ( by norm_num ) ( by linarith ) ) ( by rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num <;> linarith ) ( by norm_num ) ; exact ⟨ b, Nat.pos_of_ne_zero fun h => by norm_num [ h ] at hb₁ ; linarith [ Real.logb_pos one_lt_two h_lambda.1 ], hb₁, hb₂ ⟩ ;
      exact h_exists_b;
    use ⌊b * Real.logb 2 Q⌋₊, b;
    -- By definition of fractional part, we have $b \log_2 Q = \lfloor b \log_2 Q \rfloor + \{b \log_2 Q\}$.
    have h_frac : b * Real.logb 2 Q = ⌊b * Real.logb 2 Q⌋₊ + Int.fract (b * Real.logb 2 Q) := by
      convert Eq.symm ( Int.floor_add_fract ( ( b : ℝ ) * Real.logb 2 Q ) ) using 1;
      exact congrArg₂ _ ( mod_cast Int.toNat_of_nonneg <| Int.floor_nonneg.2 <| mul_nonneg ( Nat.cast_nonneg _ ) <| Real.logb_nonneg ( by norm_num ) <| Nat.one_le_cast.2 h_Q_pos ) rfl;
    -- Exponentiating both sides of $b \log_2 Q = \lfloor b \log_2 Q \rfloor + \{b \log_2 Q\}$, we get $Q^b = 2^{\lfloor b \log_2 Q \rfloor} \cdot 2^{\{b \log_2 Q\}}$.
    have h_exp : (Q : ℝ) ^ b = 2 ^ ⌊b * Real.logb 2 Q⌋₊ * 2 ^ (Int.fract (b * Real.logb 2 Q)) := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add ] <;> norm_num [ h_Q_pos ];
      rw [ ← h_frac, mul_comm, Real.rpow_mul ] <;> norm_num [ h_Q_pos ];
    rw [ h_exp, mul_div_cancel_left₀ _ ( by positivity ) ];
    exact ⟨ by rw [ ← Real.logb_le_iff_le_rpow ( by linarith ) ( by linarith ) ] ; linarith [ hb.2.1 ], by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) hb.2.2.le ) ( by norm_num ) ⟩

/-
For every $\lambda\in(1,2)$ and every $Q\in\mathbb{N}$, there exists a positive integer $N$ divisible by $Q$ and for which some subsequence of its divisors satisfies the lacunary condition.
-/
lemma lm_divisors (lambda : ℝ) (Q : ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q) :
  ∃ N : ℕ, Q ∣ N ∧ ∃ d : ℕ → ℕ, ∃ M : ℕ,
    d 0 = 1 ∧ d M = N ∧
    (∀ j ≤ M, d j ∣ N) ∧
    (StrictMonoOn d (Set.Icc 0 M)) ∧
    (∀ j < M, lambda ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
      -- Distinguish two cases: $Q$ is a power of 2 or it is not.
      by_cases h_pow2 : ∃ k : ℕ, Q = 2 ^ k;
      · exact lemma_divisors_power_of_two lambda Q h_lambda h_Q_pos h_pow2;
      · obtain ⟨a, b, h_lambda_le, h_le_two⟩ : ∃ a b : ℕ, lambda ≤ (Q : ℝ) ^ b / 2 ^ a ∧ (Q : ℝ) ^ b / 2 ^ a ≤ 2 := by
          exact exists_powers_in_range lambda Q h_lambda h_Q_pos h_pow2;
        refine' ⟨ 2 ^ a * Q ^ b, _, _ ⟩;
        · rcases b with ( _ | b ) <;> simp_all +decide [ pow_succ', dvd_mul_of_dvd_right ];
          linarith [ inv_le_one_of_one_le₀ ( one_le_pow₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) : ( 1 : ℝ ) ≤ 2 ^ a ) ];
        · refine' ⟨ fun j => if j ≤ a then 2 ^ j else 2 ^ ( j - ( a + 1 ) ) * Q ^ b, a + ( a + 1 ), _, _, _, _, _ ⟩ <;> norm_num [ StrictMonoOn ];
          · intro j hj; split_ifs <;> simp_all +decide ;
            · exact dvd_mul_of_dvd_left ( pow_dvd_pow _ ‹_› ) _;
            · exact mul_dvd_mul ( pow_dvd_pow _ ( Nat.sub_le_of_le_add <| by linarith ) ) dvd_rfl;
          · intro i hi j hj hij; split_ifs <;> try linarith [ pow_lt_pow_right₀ ( by norm_num : ( 1 : ℕ ) < 2 ) hij ] ;
            · refine' lt_of_le_of_lt ( pow_le_pow_right₀ ( by norm_num ) ‹i ≤ a› ) _;
              rw [ le_div_iff₀ ( by positivity ) ] at *;
              exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℝ ) a, pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show j - ( a + 1 ) ≥ 0 by norm_num ), pow_pos ( show 0 < ( Q : ℝ ) by positivity ) b ] : ( 2 : ℝ ) ^ a < 2 ^ ( j - ( a + 1 ) ) * Q ^ b );
            · exact mul_lt_mul_of_pos_right ( pow_lt_pow_right₀ ( by norm_num ) ( by omega ) ) ( pow_pos h_Q_pos _ );
          · intro j hj; split_ifs <;> norm_num [ pow_succ', mul_assoc, mul_div_mul_left ] at *;
            · linarith;
            · linarith;
            · norm_num [ show j = a by linarith ] at * ; aesop;
            · simp_all +decide [ Nat.succ_sub ( by linarith : a + 1 ≤ j ), mul_div_mul_right, ne_of_gt ( pow_pos ( by positivity : 0 < ( Q : ℝ ) ) _ ) ];
              norm_num [ pow_succ', div_eq_mul_inv ];
              linarith

/-
Definition of $\lambda_k = \max(\lambda, 2 - 1/(k+1))$.
-/
def lambda_seq (lambda : ℝ) (k : ℕ) : ℝ := max lambda (2 - 1 / (k + 1))

/-
Definition of $Q_k$ as the product of the first $k$ primes.
-/
def Q_seq (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-
Bounds for $\lambda_k$.
-/
lemma lambda_seq_bounds (lambda : ℝ) (h : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  1 < lambda_seq lambda k ∧ lambda_seq lambda k < 2 := by
    exact ⟨ lt_max_of_lt_left h.1, max_lt h.2 ( by linarith [ div_pos zero_lt_one ( by linarith : 0 < ( k : ℝ ) + 1 ) ] ) ⟩

/-
$Q_k$ is positive.
-/
lemma Q_seq_pos (k : ℕ) (_hk : k ≥ 1) : 0 < Q_seq k := by
  exact Finset.prod_pos fun i hi => Nat.Prime.pos <| by aesop;

/-
Definitions of $N_k, d_k, M_k$ using `Classical.choose`.
-/
noncomputable def step_data (lambda : ℝ) (k : ℕ) : ℕ × (ℕ → ℕ) × ℕ :=
  let l := lambda_seq lambda k
  let Q := Q_seq k
  if h : 1 < l ∧ l < 2 ∧ 0 < Q then
    let ex := lm_divisors l Q ⟨h.1, h.2.1⟩ h.2.2
    let N := Classical.choose ex
    let spec_N := Classical.choose_spec ex
    let ex_d := spec_N.2
    let d := Classical.choose ex_d
    let spec_d := Classical.choose_spec ex_d
    let M := Classical.choose spec_d
    (N, d, M)
  else
    (1, fun _ => 1, 1)

noncomputable def N_at (lambda : ℝ) (k : ℕ) := (step_data lambda k).1
noncomputable def d_at (lambda : ℝ) (k : ℕ) := (step_data lambda k).2.1
noncomputable def M_at (lambda : ℝ) (k : ℕ) := (step_data lambda k).2.2

/-
Properties of $N_k, d_k, M_k$.
-/
lemma step_data_props (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  let N := N_at lambda k
  let d := d_at lambda k
  let M := M_at lambda k
  let l := lambda_seq lambda k
  let Q := Q_seq k
  Q ∣ N ∧
  d 0 = 1 ∧ d M = N ∧
  (∀ j ≤ M, d j ∣ N) ∧
  (StrictMonoOn d (Set.Icc 0 M)) ∧
  (∀ j < M, l ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
    convert Classical.choose_spec ( lm_divisors ( lambda_seq lambda k ) ( Q_seq k ) ?_ ?_ ) using 1;
    any_goals exact lambda_seq_bounds _ h_lambda _;
    field_simp;
    any_goals exact Finset.prod_pos fun i hi => Nat.Prime.pos ( by simp );
    · unfold N_at;
      unfold step_data;
      simp +zetaDelta at *;
      split_ifs <;> simp_all +decide [lambda_seq_bounds];
      exact absurd ‹Q_seq k = 0› ( ne_of_gt ( Q_seq_pos k ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num [ Q_seq ] at * ) ) ) );
    · constructor <;> intro h;
      · convert Classical.choose_spec ( Classical.choose_spec ( lm_divisors ( lambda_seq lambda k ) ( Q_seq k ) ( lambda_seq_bounds _ h_lambda _ ) ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by simp ) ) ) |> And.right ) using 1;
        constructor <;> rintro ⟨ M, hM ⟩;
        · convert Classical.choose_spec ( Classical.choose_spec ( lm_divisors ( lambda_seq lambda k ) ( Q_seq k ) ( lambda_seq_bounds _ h_lambda _ ) ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by simp ) ) ) |> And.right ) using 1;
        · exact ⟨ _, _, hM ⟩;
      · convert Classical.choose_spec ( Classical.choose_spec h ) using 1;
        · unfold d_at;
          unfold step_data;
          simp +zetaDelta at *;
          split_ifs <;> simp_all +decide [ lambda_seq_bounds ];
          · congr! 2;
            ext; simp [exists_and_left];
          · exact absurd ‹_› ( ne_of_gt ( Q_seq_pos k ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num [ Q_seq ] at * ) ) ) );
        · simp +decide [ N_at, d_at, M_at, step_data ];
          split_ifs <;> simp +decide [ * ];
          · congr!;
            all_goals simp +decide [exists_and_left] ;
          · exact False.elim <| ‹¬ ( 1 < lambda_seq lambda k ∧ lambda_seq lambda k < 2 ∧ 0 < Q_seq k ) › ⟨ lambda_seq_bounds _ h_lambda _ |>.1, lambda_seq_bounds _ h_lambda _ |>.2, Q_seq_pos _ <| Nat.pos_of_ne_zero <| by rintro rfl; exact absurd ‹¬ ( 1 < lambda_seq lambda 0 ∧ lambda_seq lambda 0 < 2 ∧ 0 < Q_seq 0 ) › <| by norm_num [ lambda_seq, Q_seq ] ; constructor <;> linarith ⟩

/-
$M_k$ is positive for $k \ge 1$.
-/
lemma M_at_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) (hk : k ≥ 1) :
  0 < M_at lambda k := by
    apply Nat.pos_of_ne_zero
    intro h_contra
    have h_eq : d_at lambda k 0 = d_at lambda k (M_at lambda k) := by
      rw [h_contra]
    have h_contra : 1 = N_at lambda k := by
      have := step_data_props lambda h_lambda k; aesop;
    have h_contra' : 2 ≤ N_at lambda k := by
      have := step_data_props lambda h_lambda k; norm_num at *; (
      exact absurd ( this.1 ) ( by rw [ ← h_contra ] ; exact Nat.not_dvd_of_pos_of_lt ( by positivity ) ( by exact lt_of_lt_of_le ( by norm_num [ Q_seq ] ) ( show Q_seq k ≥ 2 from Nat.le_trans ( by norm_num [ Q_seq ] ) ( Finset.prod_le_prod_of_subset_of_one_le' ( Finset.range_mono hk ) fun _ _ _ => Nat.Prime.pos ( by aesop ) ) ) ) ) ;);
    linarith [h_contra, h_contra']

/-
Definition of $m_k$ and its monotonicity.
-/
noncomputable def m_seq (lambda : ℝ) : ℕ → ℕ
| 0 => 1
| 1 => 2
| (k + 2) => m_seq lambda (k + 1) + M_at lambda (k + 2)

lemma m_seq_zero (lambda : ℝ) : m_seq lambda 0 = 1 := by rfl
lemma m_seq_one (lambda : ℝ) : m_seq lambda 1 = 2 := by rfl
lemma m_seq_succ (lambda : ℝ) (k : ℕ) : m_seq lambda (k + 2) = m_seq lambda (k + 1) + M_at lambda (k + 2) := by rfl

lemma m_seq_strictMono (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  StrictMono (m_seq lambda) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n;
    induction n <;> simp_all +decide [ m_seq ];
    exact M_at_pos _ h_lambda _ ( Nat.le_add_left _ _ )

/-
$m_k \ge k$ for all $k$.
-/
lemma m_seq_ge_k (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  m_seq lambda k ≥ k := by
    induction' k with k ih <;> norm_num [ *, m_seq_one ];
    induction' k with k ih <;> norm_num [ *, m_seq_zero, m_seq_one ];
    linarith! [ m_seq_succ lambda k, M_at_pos lambda h_lambda ( k + 2 ) ( by linarith ) ]

/-
Definition of `k_of_index` and its specification.
-/
noncomputable def k_of_index (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) : ℕ :=
  let P := fun k => m_seq lambda k ≥ i
  have h : ∃ k, P k := ⟨i, m_seq_ge_k lambda h_lambda i⟩
  have : DecidablePred P := Classical.decPred P
  Nat.find h

lemma k_of_index_spec (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  let k := k_of_index lambda h_lambda i
  m_seq lambda k ≥ i ∧ ∀ j < k, m_seq lambda j < i := by
    -- By definition of $k_of_index$, we know that $m_seq \lambda k \geq i$ and for all $j < k$, $m_seq \lambda j < i$. This follows directly from the properties of the \\Classical eks' function.
    unfold k_of_index;
    simp +zetaDelta at *;
    grind

/-
`k_of_index` is positive for $i > 1$.
-/
lemma k_of_index_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) (hi : i > 1) :
  k_of_index lambda h_lambda i ≥ 1 := by
    -- Assume that `k_of_index ... < 1`. Then `k_of_index ... = 0`.
    by_contra h_contra
    have h_zero : k_of_index lambda h_lambda i = 0 := by
      linarith;
    -- By definition of `k_of_index`, we have `m_seq lambda 0 ≥ i`.
    have h_m_seq_zero : (m_seq lambda 0) ≥ i := by
      exact h_zero ▸ k_of_index_spec _ _ _ |>.1;
    linarith [ show m_seq lambda 0 = 1 from m_seq_zero _ ]

/-
Definition of `n_seq`.
-/
noncomputable def n_seq (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (n : ℕ) : ℕ :=
  if _h : n < 2 then 1
  else
    let k := k_of_index lambda h_lambda n
    let prev_m := m_seq lambda (k - 1)
    let j := n - prev_m
    let d := d_at lambda k j
    d * n_seq lambda h_lambda prev_m
termination_by n
decreasing_by
  simp_wf
  have _hn : n ≥ 2 := by linarith
  have hk : k_of_index lambda h_lambda n ≥ 1 := k_of_index_pos lambda h_lambda n (by linarith)
  let k := k_of_index lambda h_lambda n
  have h_spec := k_of_index_spec lambda h_lambda n
  have h_lt := h_spec.2 (k - 1) (by omega)
  exact h_lt

/-
$n_i > 0$ for all $i$.
-/
lemma n_seq_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (n : ℕ) :
  0 < n_seq lambda h_lambda n := by
    induction' n using Nat.strong_induction_on with n ih;
    unfold n_seq; split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ] ;
    refine' ⟨ _, ih _ _ ⟩;
    · have := step_data_props lambda h_lambda ( k_of_index lambda h_lambda n );
      refine' Nat.pos_of_dvd_of_pos ( this.2.2.2.1 _ _ ) _;
      · have := k_of_index_spec lambda h_lambda n;
        rcases k : k_of_index lambda h_lambda n with ( _ | _ | k ) <;> simp_all +decide [ m_seq ];
        · linarith [ show M_at lambda 1 ≥ 1 from M_at_pos lambda h_lambda 1 ( by norm_num ) ];
        · linarith;
      · refine' Nat.pos_of_ne_zero _;
        intro h; have := this.2.2.1; simp_all +decide ;
        have := ‹d_at lambda ( k_of_index lambda h_lambda n ) 0 = 1 ∧ StrictMonoOn ( d_at lambda ( k_of_index lambda h_lambda n ) ) ( Icc 0 ( M_at lambda ( k_of_index lambda h_lambda n ) ) ) ∧ ∀ j < M_at lambda ( k_of_index lambda h_lambda n ), _›.2.1 ( show 0 ∈ Icc 0 ( M_at lambda ( k_of_index lambda h_lambda n ) ) from ⟨ by norm_num, Nat.zero_le _ ⟩ ) ( show M_at lambda ( k_of_index lambda h_lambda n ) ∈ Icc 0 ( M_at lambda ( k_of_index lambda h_lambda n ) ) from ⟨ Nat.zero_le _, le_rfl ⟩ ) ; aesop;
    · exact k_of_index_spec lambda h_lambda n |>.2 _ ( Nat.pred_lt ( ne_bot_of_gt ( k_of_index_pos lambda h_lambda n ‹_› ) ) )

/-
$m_k - m_{k-1} \le M_k$.
-/
lemma m_seq_diff_le_M (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) (hk : k ≥ 1) :
  m_seq lambda k - m_seq lambda (k - 1) ≤ M_at lambda k := by
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq_succ ];
    rw [ show m_seq lambda 1 = 2 by exact m_seq_one _, show m_seq lambda 0 = 1 by exact m_seq_zero _ ] ; linarith [ show M_at lambda 1 ≥ 1 from M_at_pos _ h_lambda 1 le_rfl ] ;

/-
The ratio $n_{i+1}/n_i$ is bounded by $\lambda_k$ and 2.
-/
lemma n_seq_ratio_properties (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) (hi : i ≥ 1) :
  let k := k_of_index lambda h_lambda (i + 1)
  let l := lambda_seq lambda k
  l ≤ (n_seq lambda h_lambda (i + 1) : ℝ) / n_seq lambda h_lambda i ∧
  (n_seq lambda h_lambda (i + 1) : ℝ) / n_seq lambda h_lambda i ≤ 2 := by
    -- Let $k = k\_of\_index(i+1)$.
    set k := k_of_index lambda h_lambda (i + 1);
    -- So $m_{k-1} < i+1 \le m_k$.
    have h_mk : m_seq lambda (k - 1) < i + 1 ∧ i + 1 ≤ m_seq lambda k := by
      exact ⟨ k_of_index_spec _ _ _ |>.2 _ ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by
        exact Nat.ne_of_gt ( k_of_index_pos _ _ _ ( by linarith ) ) ) ) zero_lt_one ), k_of_index_spec _ _ _ |>.1 ⟩;
    -- Case 1: $i+1$ is not a boundary, i.e., $m_{k-1} < i < i+1 \le m_k$.
    by_cases h_boundary : i = m_seq lambda (k - 1);
    · -- Since $i = m_{k-1}$, we have $n_{i+1} = d^{(k)}_1 n_{m_{k-1}}$.
      have h_n_i_plus_1 : n_seq lambda h_lambda (i + 1) = d_at lambda k 1 * n_seq lambda h_lambda (m_seq lambda (k - 1)) := by
        rw [ n_seq ];
        grind +ring;
      -- By `step_data_props`, we know that $d^{(k)}_1$ is in $[\lambda_k, 2]$.
      have h_d_k1 : lambda_seq lambda k ≤ (d_at lambda k 1 : ℝ) ∧ (d_at lambda k 1 : ℝ) ≤ 2 := by
        have := step_data_props lambda h_lambda k;
        have := this.2.2.2.2.2 0 ( Nat.pos_of_ne_zero ?_ ) <;> norm_num at *;
        · norm_num [ ‹Q_seq k ∣ N_at lambda k ∧ d_at lambda k 0 = 1 ∧ d_at lambda k ( M_at lambda k ) = N_at lambda k ∧ ( ∀ j ≤ M_at lambda k, d_at lambda k j ∣ N_at lambda k ) ∧ StrictMonoOn ( d_at lambda k ) ( Icc 0 ( M_at lambda k ) ) ∧ ∀ j < M_at lambda k, lambda_seq lambda k ≤ ( d_at lambda k ( j + 1 ) : ℝ ) / ( d_at lambda k j : ℝ ) ∧ ( d_at lambda k ( j + 1 ) : ℝ ) / ( d_at lambda k j : ℝ ) ≤ 2›.2.1 ] at this ⊢ ; exact ⟨ this.1, by exact_mod_cast this.2 ⟩ ;
        · linarith [ M_at_pos lambda h_lambda k ( Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at * ; linarith ) ) ];
      simp_all +decide [ ne_of_gt ( n_seq_pos _ _ _ ) ];
    · -- Since $i \neq m_{k-1}$, we have $k\_of\_index(i) = k$.
      have h_k_eq : k_of_index lambda h_lambda i = k := by
        have h_k_eq : ∀ j < k, m_seq lambda j < i := by
          intros j hj_lt_k
          have h_j_lt_i : m_seq lambda j < i + 1 := by
            exact lt_of_le_of_lt ( m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_sub_one_of_lt hj_lt_k ) h_mk.1
          have h_j_lt_i' : m_seq lambda j < i := by
            exact lt_of_le_of_ne ( Nat.le_of_lt_succ h_j_lt_i ) ( Ne.symm <| by rintro h; exact h_boundary <| by linarith [ show m_seq lambda j ≤ m_seq lambda ( k - 1 ) from by exact monotone_nat_of_le_succ ( fun n => by exact m_seq_strictMono _ h_lambda |> StrictMono.monotone |> fun h => h ( Nat.le_succ _ ) ) ( Nat.le_sub_one_of_lt hj_lt_k ) ] )
          exact h_j_lt_i';
        refine' le_antisymm _ _ <;> contrapose! h_k_eq;
        · exact absurd ( k_of_index_spec lambda h_lambda i |>.2 _ h_k_eq ) ( by linarith );
        · exact ⟨ k_of_index lambda h_lambda i, h_k_eq, k_of_index_spec lambda h_lambda i |>.1 ⟩;
      -- By definition of $n_seq$, we have $n_{i+1} = d^{(k)}_{i+1-m_{k-1}} n_{m_{k-1}}$ and $n_i = d^{(k)}_{i-m_{k-1}} n_{m_{k-1}}$.
      have h_n_seq_def : n_seq lambda h_lambda (i + 1) = d_at lambda k (i + 1 - m_seq lambda (k - 1)) * n_seq lambda h_lambda (m_seq lambda (k - 1)) ∧ n_seq lambda h_lambda i = d_at lambda k (i - m_seq lambda (k - 1)) * n_seq lambda h_lambda (m_seq lambda (k - 1)) := by
        constructor <;> rw [ n_seq ] <;> simp +decide [h_k_eq];
        · grind;
        · intro hi'; interval_cases i ; simp_all +decide ;
          rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq ];
          linarith [ show m_seq lambda ( k + 1 ) ≥ 2 from Nat.recOn k ( by linarith! [ m_seq_zero lambda, m_seq_one lambda ] ) fun n ihn => by linarith! [ m_seq_succ lambda n, M_at_pos lambda h_lambda ( n + 2 ) ( by linarith ) ] ];
      -- By definition of $d_at$, we know that $d^{(k)}_{j+1}/d^{(k)}_j \in [\lambda_k, 2]$ for all $j < M_k$.
      have h_d_at_ratio : ∀ j < M_at lambda k, lambda_seq lambda k ≤ (d_at lambda k (j + 1) : ℝ) / (d_at lambda k j) ∧ (d_at lambda k (j + 1) : ℝ) / (d_at lambda k j) ≤ 2 := by
        exact step_data_props lambda h_lambda k |>.2.2.2.2.2;
      have h_j_lt_M : i - m_seq lambda (k - 1) < M_at lambda k := by
        have h_j_lt_M : m_seq lambda k - m_seq lambda (k - 1) ≤ M_at lambda k := by
          apply m_seq_diff_le_M;
          · tauto;
          · exact Nat.pos_of_ne_zero ( by rintro h; simp_all +decide [ m_seq ] );
        omega;
      simp_all +decide [ Nat.sub_add_comm ( show m_seq lambda ( k - 1 ) ≤ i from Nat.le_of_lt_succ h_mk.1 ) ];
      convert h_d_at_ratio ( i - m_seq lambda ( k - 1 ) ) h_j_lt_M using 1 <;> rw [ mul_div_mul_right _ _ <| Nat.cast_ne_zero.mpr <| ne_of_gt <| n_seq_pos _ _ _ ]

/-
$\lambda_k \to 2$.
-/
lemma lambda_seq_tendsto (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Filter.Tendsto (lambda_seq lambda) Filter.atTop (nhds 2) := by
    have h_two_minus_one_div : Filter.Tendsto (fun k => 2 - 1 / (k + 1 : ℝ)) Filter.atTop (nhds 2) := by
      exact le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_id.atTop_add tendsto_const_nhds ) <| by norm_num;
    convert h_two_minus_one_div.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.max ( tendsto_const_nhds ) using 1 ; norm_num [ lambda_seq ];
    linarith

/-
Formula for `n_seq` within a step.
-/
lemma n_seq_formula (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) (i : ℕ)
  (hk : k ≥ 1) (hi_lower : m_seq lambda (k - 1) ≤ i) (hi_upper : i ≤ m_seq lambda k) :
  n_seq lambda h_lambda i = d_at lambda k (i - m_seq lambda (k - 1)) * n_seq lambda h_lambda (m_seq lambda (k - 1)) := by
    rcases eq_or_lt_of_le hi_lower with ( rfl | hi_lower );
    · have := step_data_props lambda h_lambda k; aesop;
    · have h_k_of_index : k_of_index lambda h_lambda i = k := by
        refine' le_antisymm _ _ <;> contrapose! hi_lower;
        · -- Since $k < k_of_index lambda h_lambda i$, we have $m_seq lambda k < i$ by the definition of $k_of_index$.
          have h_m_seq_lt_i : m_seq lambda k < i := by
            exact k_of_index_spec _ _ _ |>.2 _ hi_lower;
          linarith;
        · have := k_of_index_spec lambda h_lambda i;
          exact this.1.trans ( m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_pred_of_lt hi_lower );
      rw [ n_seq ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq ];
      · interval_cases i ; norm_num at *;
      · intro hi; interval_cases i <;> simp_all +decide ;
        exact absurd hi_lower ( ne_of_gt ( Nat.recOn k ( by linarith! [ m_seq_zero lambda, m_seq_one lambda, m_seq_strictMono lambda h_lambda ( Nat.lt_succ_self 0 ) ] ) fun n ihn => by linarith! [ m_seq_succ lambda n, m_seq_strictMono lambda h_lambda ( Nat.lt_succ_self ( n + 1 ) ) ] ) )

/-
Definition of `final_n` and its positivity.
-/
noncomputable def final_n (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) : ℕ :=
  n_seq lambda h_lambda (i + 1)

lemma final_n_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  0 < final_n lambda h_lambda i := by
    convert n_seq_pos _ _ _ using 1

/-
`final_n` is $\lambda$-lacunary.
-/
lemma final_n_is_lacunary (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  IsLambdaLacunary lambda (fun i => final_n lambda h_lambda i) := by
    intro i;
    have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith );
    unfold lambda_seq at this; aesop;

/-
`k_of_index` tends to infinity.
-/
lemma k_of_index_tendsto_atTop (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Filter.Tendsto (k_of_index lambda h_lambda) Filter.atTop Filter.atTop := by
    refine' Filter.tendsto_atTop_atTop.mpr _;
    -- Let $b$ be any natural number. We need to find an $i$ such that for all $a \geq i$, $b \leq k\_of\_index(a)$.
    intro b
    use m_seq lambda b + 1
    intro a ha
    have h_k_of_index : b ≤ k_of_index lambda h_lambda a := by
      contrapose! ha;
      have := k_of_index_spec lambda h_lambda a;
      exact Nat.lt_succ_of_le ( this.1.trans ( by exact monotone_nat_of_le_succ ( fun n => by linarith [ m_seq_strictMono lambda h_lambda |> StrictMono.monotone <| Nat.le_succ n ] ) ha.le ) )
    exact h_k_of_index

/-
The ratio of `final_n` tends to 2.
-/
lemma final_n_ratio_tendsto (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Filter.Tendsto (fun i => (final_n lambda h_lambda (i + 1) : ℝ) / final_n lambda h_lambda i) Filter.atTop (nhds 2) := by
    -- By `n_seq_ratio_properties` (applied to $i+1 \ge 1$), $\lambda_{k_i} \le r_i \le 2$, where $k_i = k\_of\_index(i+2)$.
    have h_bound : Filter.Tendsto (fun i => lambda_seq lambda (k_of_index lambda h_lambda (i + 2))) Filter.atTop (nhds 2) := by
      refine' lambda_seq_tendsto _ h_lambda |> Filter.Tendsto.comp <| k_of_index_tendsto_atTop _ h_lambda |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2;
    refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_bound tendsto_const_nhds _ _;
    · refine' Filter.Eventually.of_forall fun i => _;
      have := n_seq_ratio_properties ( lambda := lambda ) ( h_lambda := h_lambda ) ( i + 1 ) ( by linarith ) ; aesop;
    · refine' Filter.Eventually.of_forall _;
      intro i; have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) ; aesop;

/-
Definition of `final_m` and its strict monotonicity.
-/
noncomputable def final_m (lambda : ℝ) (k : ℕ) : ℕ :=
  m_seq lambda (k + 1) - 1

lemma final_m_strictMono (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  StrictMono (final_m lambda) := by
  intro a b h
  dsimp [final_m]
  have h_mono := m_seq_strictMono lambda h_lambda
  have h_lt := h_mono (Nat.succ_lt_succ h)
  have h_ge : m_seq lambda (a + 1) ≥ 1 := by
    calc m_seq lambda (a + 1) ≥ a + 1 := m_seq_ge_k lambda h_lambda (a + 1)
         _ ≥ 1 := Nat.succ_le_succ (Nat.zero_le a)
  exact Nat.pred_lt_pred (Nat.ne_of_gt h_ge) h_lt

/-
$n_i \le 2^i$.
-/
lemma final_n_le_two_pow (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  final_n lambda h_lambda i ≤ 2 ^ i := by
    induction' i with i ih;
    · unfold final_n n_seq; aesop;
    · -- By definition of `final_n`, we have `final_n (i + 1) = n_seq (i + 2)`.
      unfold final_n;
      -- By definition of `n_seq`, we have `n_seq (i + 2) ≤ 2 * n_seq (i + 1)`.
      have h_n_seq_le : (n_seq lambda h_lambda (i + 2) : ℝ) ≤ 2 * (n_seq lambda h_lambda (i + 1) : ℝ) := by
        convert n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) |> And.right |> fun x => mul_le_mul_of_nonneg_right x ( Nat.cast_nonneg ( n_seq lambda h_lambda ( i + 1 ) ) ) using 1 ; ring_nf! ; norm_num [ ne_of_gt ( n_seq_pos _ _ _ ) ] ;
      rw [ pow_succ' ] ; norm_cast at * ; linarith! [ show final_n lambda h_lambda i = n_seq lambda h_lambda ( i + 1 ) from rfl ] ;

/-
$n_{m_k}$ divides $n_{m_{k+1}}$.
-/
lemma n_seq_div_prev_m_seq (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  n_seq lambda h_lambda (m_seq lambda k) ∣ n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
    -- Apply the formula for `n_seq` within a step.
    have h_formula : n_seq lambda h_lambda (m_seq lambda (k + 1)) = d_at lambda (k + 1) (m_seq lambda (k + 1) - m_seq lambda k) * n_seq lambda h_lambda (m_seq lambda k) := by
      apply n_seq_formula;
      · linarith;
      · exact m_seq_strictMono _ ⟨ h_lambda.1, h_lambda.2 ⟩ |> StrictMono.monotone <| Nat.le_succ _;
      · rfl;
    exact h_formula.symm ▸ dvd_mul_left _ _


/-
The sequence `final_n` is strictly increasing.
-/
lemma final_n_strictMono (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  StrictMono (final_n lambda h_lambda) := by
    -- By definition of `final_n`, we know that `final_n i = n_seq (i + 1)`.
    unfold final_n;
    -- By definition of `final_n`, we know that `final_n i = n_seq (i + 1)`. We need to show that this sequence is strictly increasing.
    have h_final_inc : ∀ i, n_seq lambda h_lambda (i + 1) < n_seq lambda h_lambda (i + 2) := by
      intro i
      have h_ratio : (n_seq lambda h_lambda (i + 2) : ℝ) / (n_seq lambda h_lambda (i + 1) : ℝ) > 1 := by
        have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith );
        exact lt_of_lt_of_le ( lt_max_of_lt_left h_lambda.1 ) this.1;
      exact_mod_cast ( by rw [ gt_iff_lt, lt_div_iff₀ ( Nat.cast_pos.mpr ( n_seq_pos _ _ _ ) ) ] at h_ratio; linarith : ( n_seq lambda h_lambda ( i + 1 ) : ℝ ) < n_seq lambda h_lambda ( i + 2 ) );
    exact strictMono_nat_of_lt_succ h_final_inc

/-
For every $k$, the term $n_{m_k}$ is divisible by all preceding terms $n_j$.
-/
lemma final_n_div_m (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  ∀ j < final_m lambda k, final_n lambda h_lambda j ∣ final_n lambda h_lambda (final_m lambda k) := by
    intro j hj;
    -- By Lemma 3, $n_{m_k}$ is divisible by all preceding terms $n_j$ for $j < m_k$.
    have h_div : ∀ k j, j < m_seq lambda (k + 1) → n_seq lambda h_lambda j ∣ n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
      intros k j hj
      induction' k with k ih generalizing j;
      · rcases j with ( _ | _ | j ) <;> simp_all +arith +decide [ m_seq ];
        · unfold n_seq; aesop;
        · unfold n_seq; aesop;
      · by_cases hj' : j < m_seq lambda (k + 1);
        · exact dvd_trans ( ih j hj' ) ( n_seq_div_prev_m_seq _ _ _ );
        · -- Since $j \geq m_seq lambda (k + 1)$, we can write $j = m_seq lambda (k + 1) + t$ for some $t$.
          obtain ⟨t, ht⟩ : ∃ t, j = m_seq lambda (k + 1) + t := by
            exact Nat.exists_eq_add_of_le <| le_of_not_gt hj';
          -- By definition of `n_seq`, we have `n_seq lambda h_lambda (m_seq lambda (k + 1) + t) = d_at lambda (k + 2) t * n_seq lambda h_lambda (m_seq lambda (k + 1))`.
          have h_n_seq_def : n_seq lambda h_lambda (m_seq lambda (k + 1) + t) = d_at lambda (k + 2) t * n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
            convert n_seq_formula _ _ _ _ _ _ _ using 1 <;> norm_num [ ht ];
            rotate_left;
            exact k + 2;
            · linarith;
            · exact Nat.le_add_right _ _;
            · linarith;
            · norm_num [ Nat.add_sub_cancel_left ];
          have h_n_seq_def' : n_seq lambda h_lambda (m_seq lambda (k + 2)) = d_at lambda (k + 2) (M_at lambda (k + 2)) * n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
            convert n_seq_formula lambda h_lambda ( k + 2 ) ( m_seq lambda ( k + 2 ) ) ( by linarith ) ( by
              exact m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_succ _ ) ( by
              norm_num +zetaDelta at * ) using 1
            generalize_proofs at *; (
            simp +decide [ m_seq_succ ]);
          have := step_data_props lambda h_lambda (k + 2);
          simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          exact Nat.mod_eq_zero_of_dvd ( mul_dvd_mul ( Nat.dvd_of_mod_eq_zero ( this.2.2.2.1 t ( by linarith [ show t < M_at lambda ( k + 2 ) from by linarith [ show m_seq lambda ( k + 2 ) = m_seq lambda ( k + 1 ) + M_at lambda ( k + 2 ) from m_seq_succ _ _ ] ] ) ) ) ( dvd_refl _ ) );
    unfold final_n
    generalize_proofs at *; (
    unfold final_m; (
    rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by
      exact ne_of_gt <| Nat.recOn k ( by linarith! [ m_seq_one lambda ] ) fun n ihn => by linarith! [ m_seq_succ lambda n, M_at_pos lambda h_lambda ( n + 2 ) ( by linarith ) ] ; ) ] ; exact h_div k _ <| by
      exact Nat.add_lt_of_lt_sub hj))

/-
The product of `Q_seq`s divides `final_n`.
-/
def super_Q (k : ℕ) : ℕ := ∏ j ∈ Finset.range k, Q_seq (j + 1)

lemma super_Q_dvd_final_n (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  super_Q k ∣ final_n lambda h_lambda (final_m lambda (k - 1)) := by
    rcases k with ( _ | k ) <;> simp_all +decide [ super_Q, final_n ];
    -- By definition of `n_seq`, we know that `n_seq lambda h_lambda (m_seq lambda (k + 1))` is divisible by `∏ j ∈ Finset.range (k + 1), Q_seq (j + 1)`.
    have h_div : ∀ k, (∏ j ∈ Finset.range (k + 1), Q_seq (j + 1)) ∣ n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
      intro k;
      induction' k with k ih;
      · unfold n_seq Q_seq m_seq; norm_num;
        rw [ show k_of_index lambda h_lambda 2 = 1 from _ ] ; norm_num [ m_seq ];
        · unfold n_seq; norm_num [ m_seq ] ;
          have := step_data_props lambda h_lambda 1;
          rcases k : M_at lambda 1 with ( _ | _ | k ) <;> simp_all +decide [ StrictMonoOn ];
          · linarith [ M_at_pos lambda h_lambda 1 ( by norm_num ) ];
          · unfold Q_seq at this; aesop;
          · have := this.2.2.2.2.2 0; norm_num at this;
            unfold lambda_seq at this; norm_num at this;
            norm_num [ ‹Q_seq 1 ∣ N_at lambda 1 ∧ d_at lambda 1 0 = 1 ∧ d_at lambda 1 ( _ + 1 + 1 ) = N_at lambda 1 ∧ _› ] at this ⊢;
            exact ⟨ 1, by norm_num; exact le_antisymm ( mod_cast this.2 ) ( mod_cast by exact Nat.le_of_not_lt fun h => by interval_cases d_at lambda 1 1 <;> norm_num at * ) ⟩;
        · unfold k_of_index;
          simp +decide [ Nat.find_eq_iff, m_seq ];
      · have h_div : n_seq lambda h_lambda (m_seq lambda (k + 2)) = N_at lambda (k + 2) * n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
          rw [ n_seq_formula ];
          rotate_left;
          exact k + 2;
          · linarith;
          · exact m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_succ _;
          · norm_num;
          · have := step_data_props lambda h_lambda ( k + 2 );
            simp_all +decide [ m_seq_succ ];
        simp_all +decide [ Finset.prod_range_succ ];
        convert Nat.mul_dvd_mul ( step_data_props ( lambda ) h_lambda ( k + 2 ) |>.1 ) ih using 1 ; ring;
    convert h_div k using 1;
    exact congr_arg _ ( Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by linarith [ m_seq_strictMono lambda h_lambda ( show k + 1 > 0 from Nat.succ_pos _ ) ] ) )

/-
Every positive integer divides `super_Q k` for some `k`.
-/
lemma q_dvd_super_Q (q : ℕ) (hq : q > 0) :
  ∃ k, q ∣ super_Q k := by
    -- Let $q = \prod_{i=1}^k p_i^{a_i}$ be the prime factorization of $q$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ p ∈ Nat.primeFactors q, p ≤ Nat.nth Nat.Prime (k - 1) := by
      use ( Finset.sup ( Nat.primeFactors q ) ( fun p => Nat.count ( Nat.Prime ) p ) ) + 1;
      norm_num +zetaDelta at *;
      intro p pp dp _; refine' le_trans _ ( Nat.nth_monotone _ <| Finset.le_sup <| Nat.mem_primeFactors.mpr ⟨ pp, dp, by aesop ⟩ ) ; aesop;
      exact Nat.infinite_setOf_prime;
    -- Choose $k$ large enough such that $k > \max_{i=1}^k a_i$.
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, ∀ p ∈ Nat.primeFactors q, Nat.factorization q p ≤ k' - Nat.count (Nat.Prime) p := by
      use ∑ p ∈ q.primeFactors, q.factorization p + ∑ p ∈ q.primeFactors, Nat.count Nat.Prime p + 1;
      exact fun p hp => le_tsub_of_add_le_left <| by linarith [ Finset.single_le_sum ( fun x _ => Nat.zero_le ( q.factorization x ) ) hp, Finset.single_le_sum ( fun x _ => Nat.zero_le ( Nat.count Nat.Prime x ) ) hp ] ;
    refine' ⟨ k + k', _ ⟩;
    have h_div : ∀ p ∈ Nat.primeFactors q, Nat.factorization q p ≤ ∑ j ∈ Finset.range (k + k'), Nat.factorization (Q_seq (j + 1)) p := by
      intros p hp
      have h_factorization : ∀ j ≥ Nat.count (Nat.Prime) p, Nat.factorization (Q_seq (j + 1)) p ≥ 1 := by
        intros j hj
        have h_prime_factor_count : p ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (j + 1)) := by
          refine' Finset.mem_image.mpr ⟨ Nat.count Nat.Prime p, Finset.mem_range.mpr ( by linarith ), _ ⟩;
          rw [ Nat.nth_count ] ; aesop;
        obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp h_prime_factor_count; simp +decide [ Q_seq ] ;
        rw [ Nat.factorization_prod ] <;> norm_num [ Nat.Prime.ne_zero ];
        rw [ Finset.sum_eq_add_sum_diff_singleton hi ] ; aesop;
      refine le_trans ( hk' p hp ) ?_;
      refine' le_trans _ ( Finset.sum_le_sum_of_subset <| Finset.range_mono <| show k + k' ≥ Nat.count Nat.Prime p + ( k' - Nat.count Nat.Prime p ) from _ );
      · rw [ Finset.sum_range_add ];
        exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => h_factorization _ ( by linarith ) ) );
      · rw [ add_tsub_cancel_of_le ];
        · linarith;
        · contrapose! hk';
          exact ⟨ p, hp, by rw [ Nat.sub_eq_zero_of_le hk'.le ] ; exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ⟩;
    rw [ ← Nat.factorization_le_iff_dvd ];
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ q <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
      unfold super_Q; rw [ Nat.factorization_prod ] ; aesop;
      exact fun x hx => Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop;
    · positivity;
    · exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => Nat.Prime.ne_zero <| by aesop;

/-
Every positive integer divides some term of the sequence `final_n`.
-/
lemma final_n_div_all (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (q : ℕ) (hq : q > 0) :
  ∃ i, q ∣ final_n lambda h_lambda i := by
    -- By `super_Q_dvd_final_n`, we know that `super_Q k ∣ final_n (final_m (k - 1))`.
    obtain ⟨k, hk⟩ : ∃ k, q ∣ super_Q k := q_dvd_super_Q q hq
    have h_div : super_Q k ∣ final_n lambda h_lambda (final_m lambda (k - 1)) := by
      exact super_Q_dvd_final_n lambda h_lambda k;
    exact ⟨ _, dvd_trans hk h_div ⟩

/-
There exists an index `i` such that `final_n i < 2^i`.
-/
lemma exists_final_n_lt_two_pow (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∃ i, final_n lambda h_lambda i < 2 ^ i := by
    -- By `final_n_div_all`, there exists an index `i` such that `3 ∣ final_n i`.
    obtain ⟨i, hi⟩ : ∃ i, 3 ∣ final_n lambda h_lambda i := by
      exact final_n_div_all lambda h_lambda 3 ( by norm_num ) |> fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩;
    by_contra h_contra
    push_neg at h_contra
    have h_eq : final_n lambda h_lambda i = 2 ^ i := by
      exact le_antisymm ( final_n_le_two_pow _ _ _ ) ( h_contra _ )
    have h_false : 3 ∣ 2 ^ i := by
      exact h_eq ▸ hi
    exact absurd h_false (by
    norm_num [ Nat.Prime.dvd_iff_one_le_factorization ])

/-
The sum of reciprocals of `final_n` converges.
-/
lemma final_n_summable (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Summable (fun i => (1 : ℝ) / final_n lambda h_lambda i) := by
    -- By induction, we can show that $final_n i \geq \lambda^i$ for all $i$.
    have h_exp_growth : ∀ i, (final_n lambda h_lambda i : ℝ) ≥ lambda ^ i := by
      -- We use induction to prove that $n_{i+1} \ge \lambda n_i$.
      have h_inductive_step : ∀ i, (final_n lambda h_lambda (i + 1) : ℝ) ≥ lambda * (final_n lambda h_lambda i : ℝ) := by
        have := final_n_is_lacunary lambda h_lambda;
        exact fun i => by have := this i; rw [ ge_iff_le, le_div_iff₀ ( Nat.cast_pos.mpr <| final_n_pos _ _ _ ) ] at this; linarith;
      intro i; induction i <;> simp_all +decide [pow_succ'] ;
      · exact Nat.one_le_of_lt ( final_n_pos _ _ _ ) |> le_trans <| Nat.le_refl _;
      · exact le_trans ( mul_le_mul_of_nonneg_left ‹_› ( by linarith ) ) ( h_inductive_step _ );
    -- Since $1/\lambda < 1$, the geometric series $\sum (1/\lambda)^i$ converges.
    have h_geo_series : Summable (fun i => (1 / lambda : ℝ) ^ i) := by
      exact summable_geometric_of_lt_one ( by exact one_div_nonneg.mpr ( by linarith ) ) ( by rw [ div_lt_iff₀ ] <;> linarith );
    exact h_geo_series.of_nonneg_of_le ( fun i => by positivity ) fun i => by simpa using inv_anti₀ ( pow_pos ( by linarith ) _ ) ( h_exp_growth i ) ;

/-
The sum of reciprocals of `final_n` is strictly greater than 2.
-/
lemma final_n_sum_gt_two (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∑' i, (1 : ℝ) / final_n lambda h_lambda i > 2 := by
    obtain ⟨ k, hk ⟩ := exists_final_n_lt_two_pow lambda h_lambda;
    -- We have if `final_n i < 2^i` for some `i`, then the sum of reciprocals is strictly greater than `2`.
    have h_sum_gt : ∑' i, (1 : ℝ) / (final_n lambda h_lambda i) > ∑' i, (1 : ℝ) / (2 ^ i) := by
      apply_rules [ Summable.tsum_lt_tsum ];
      · intro n; exact (by
        simp +zetaDelta at *;
        gcongr;
        · exact Nat.cast_pos.mpr ( final_n_pos _ _ _ );
        · exact_mod_cast final_n_le_two_pow _ _ _);
      · gcongr ; norm_cast ; linarith [ final_n_pos lambda h_lambda k ];
        norm_cast;
      · simpa using summable_geometric_two;
      · convert final_n_summable lambda h_lambda using 1;
    exact h_sum_gt.trans_le' ( by simpa using by ring_nf; rw [ tsum_geometric_of_lt_one ] <;> norm_num )


/-
The source file contains additional formalizations of later paper theorems.
The benchmark target only uses Theorem 1, so the unrelated later sections are
omitted here to keep the oracle narrow and robust on the pinned environment.
-/
/-
Theorem 1: For every $λ \in (1, 2)$, there exists a $λ$-lacunary sequence of positive integers with limit ratio $2$ such that finite sums of its reciprocals contain all rationals in $[0, 2]$.
-/
theorem Theorem_1 (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Filter.Tendsto (fun i => (n (i + 1) : ℝ) / n i) Filter.atTop (nhds 2) ∧
    Set.Icc 0 2 ∩ {x : ℝ | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i) := by
      use final_n lambda h_lambda;
      refine' ⟨ _, _, _, _ ⟩;
      · exact fun i => final_n_pos lambda h_lambda i;
      · exact final_n_is_lacunary lambda h_lambda;
      · exact final_n_ratio_tendsto lambda h_lambda;
      · intro x hx
        obtain ⟨hx_range, ⟨q, hq⟩⟩ := hx
        have h_sum : x ∈ TargetInterval (fun i => (1 : ℝ) / final_n lambda h_lambda i) := by
          have h_sum : x < ∑' i, (1 : ℝ) / final_n lambda h_lambda i := by
            exact lt_of_le_of_lt hx_range.2 ( by simpa using final_n_sum_gt_two lambda h_lambda );
          unfold TargetInterval; aesop;
        have h_rational : ∃ q : ℚ, x = q := by
          use q
        have h_subset_sum : x ∈ SubsetSums (fun i => (1 : ℝ) / final_n lambda h_lambda i) := by
          apply target_subset_subset_sums (final_n lambda h_lambda) (final_m lambda) (fun i => by
            exact final_n_pos lambda h_lambda i) (fun i => by
            exact fun j hj => final_n_strictMono _ _ hj) (final_m_strictMono lambda h_lambda) (fun k => by
            exact fun hk => final_n_div_all _ _ _ hk.nat_succ_le |> fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩) (fun k j hj => by
            apply_rules [ final_n_div_m ]) (fun k => by
            intro hk
            have h_sum : (1 : ℝ) / final_n lambda h_lambda k ≤ (∑ j ∈ Finset.Ioc k (final_m lambda 0), (1 : ℝ) / final_n lambda h_lambda j) + (1 : ℝ) / final_n lambda h_lambda (final_m lambda 0) := by
              convert remark_cond _ _ _ _ _ _ using 1;
              · exact fun i => final_n_pos lambda h_lambda i;
              · intro i
                have h_ratio : (final_n lambda h_lambda (i + 1) : ℝ) / final_n lambda h_lambda i ≤ 2 := by
                  have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) ; aesop;
                exact_mod_cast (by
                rwa [ div_le_iff₀ ( Nat.cast_pos.mpr ( final_n_pos _ _ _ ) ) ] at h_ratio : (final_n lambda h_lambda (i + 1) : ℝ) ≤ 2 * final_n lambda h_lambda i);
              · exact hk
            exact h_sum) (fun k i hi => by
            intro hi';
            have h_ratio : ∀ i, final_n lambda h_lambda (i + 1) ≤ 2 * final_n lambda h_lambda i := by
              intro i
              have h_ratio : (final_n lambda h_lambda (i + 1) : ℝ) / final_n lambda h_lambda i ≤ 2 := by
                have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) ; aesop;
              rw [ div_le_iff₀ ] at h_ratio <;> norm_cast at * ; linarith [ final_n_pos lambda h_lambda i ];
            have := remark_cond ( fun i => final_n lambda h_lambda i ) ( final_m lambda ( k + 1 ) ) ( fun i => by
              exact final_n_pos lambda h_lambda i ) ( fun i => by
              exact h_ratio i ) i ( by
              linarith );
            convert this using 1);
          exact ⟨ h_sum, h_rational ⟩
        exact h_subset_sum

end Erdos355Oracle
