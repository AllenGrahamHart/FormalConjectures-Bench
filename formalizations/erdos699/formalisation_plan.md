# Erdős 699 Formalisation Plan

Target:

```lean
theorem Erdos699.sylvester_schur
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

## Current Status

The file `Erdos699Formalization.lean` now formalises the exact binomial
target unconditionally:

```lean
theorem sylvester_schur
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

It also retains the bridge from the `Erdos961Prop` smooth-number interval
formulation to the same interval theorem, but the final theorem above does
not depend on the unresolved `formal-conjectures` Erdős 961 statement.

It additionally proves two easy unconditional fragments of the interval
theorem:

```lean
lemma sylvester_schur_interval_one {m : ℕ} (hm : 1 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 1) ∧ p.Prime ∧ 1 < p ∧ p ∣ j

lemma sylvester_schur_interval_boundary {k : ℕ} (hk : 0 < k) :
    ∃ j p : ℕ, j ∈ Set.Ico (k + 1) (k + 1 + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_two {m : ℕ} (hm : 2 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 2) ∧ p.Prime ∧ 2 < p ∧ p ∣ j

lemma sylvester_schur_interval_three {m : ℕ} (hm : 3 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 3) ∧ p.Prime ∧ 3 < p ∧ p ∣ j

lemma sylvester_schur_interval_four {m : ℕ} (hm : 4 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 4) ∧ p.Prime ∧ 4 < p ∧ p ∣ j

lemma sylvester_schur_interval_le_four {m k : ℕ}
    (hk : 0 < k) (hk4 : k ≤ 4) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_threshold_le_four {k : ℕ}
    (hk : 0 < k) (hk4 : k ≤ 4) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_five {m : ℕ} (hm : 5 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 5) ∧ p.Prime ∧ 5 < p ∧ p ∣ j

lemma sylvester_schur_interval_le_five {m k : ℕ}
    (hk : 0 < k) (hk5 : k ≤ 5) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_threshold_le_five {k : ℕ}
    (hk : 0 < k) (hk5 : k ≤ 5) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_six {m : ℕ} (hm : 6 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 6) ∧ p.Prime ∧ 6 < p ∧ p ∣ j

lemma sylvester_schur_interval_le_six {m k : ℕ}
    (hk : 0 < k) (hk6 : k ≤ 6) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_threshold_le_six {k : ℕ}
    (hk : 0 < k) (hk6 : k ≤ 6) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_seven {m : ℕ} (hm : 7 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 7) ∧ p.Prime ∧ 7 < p ∧ p ∣ j

lemma sylvester_schur_interval_le_seven {m k : ℕ}
    (hk : 0 < k) (hk7 : k ≤ 7) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_threshold_le_seven {k : ℕ}
    (hk : 0 < k) (hk7 : k ≤ 7) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_eight {m : ℕ} (hm : 8 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 8) ∧ p.Prime ∧ 8 < p ∧ p ∣ j

lemma sylvester_schur_interval_le_eight {m k : ℕ}
    (hk : 0 < k) (hk8 : k ≤ 8) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_threshold_le_eight {k : ℕ}
    (hk : 0 < k) (hk8 : k ≤ 8) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_nine {m : ℕ} (hm : 9 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 9) ∧ p.Prime ∧ 9 < p ∧ p ∣ j

lemma sylvester_schur_interval_ten {m : ℕ} (hm : 10 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 10) ∧ p.Prime ∧ 10 < p ∧ p ∣ j

lemma sylvester_schur_interval_eleven {m : ℕ} (hm : 11 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 11) ∧ p.Prime ∧ 11 < p ∧ p ∣ j

lemma sylvester_schur_interval_twelve {m : ℕ} (hm : 12 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 12) ∧ p.Prime ∧ 12 < p ∧ p ∣ j

lemma sylvester_schur_interval_thirteen {m : ℕ} (hm : 13 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 13) ∧ p.Prime ∧ 13 < p ∧ p ∣ j

lemma sylvester_schur_interval_fourteen {m : ℕ} (hm : 14 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 14) ∧ p.Prime ∧ 14 < p ∧ p ∣ j

lemma sylvester_schur_interval_fifteen {m : ℕ} (hm : 15 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 15) ∧ p.Prime ∧ 15 < p ∧ p ∣ j

lemma sylvester_schur_interval_sixteen {m : ℕ} (hm : 16 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 16) ∧ p.Prime ∧ 16 < p ∧ p ∣ j

lemma sylvester_schur_interval_seventeen {m : ℕ} (hm : 17 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 17) ∧ p.Prime ∧ 17 < p ∧ p ∣ j

lemma sylvester_schur_interval_eighteen {m : ℕ} (hm : 18 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 18) ∧ p.Prime ∧ 18 < p ∧ p ∣ j

lemma sylvester_schur_interval_nineteen {m : ℕ} (hm : 19 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 19) ∧ p.Prime ∧ 19 < p ∧ p ∣ j

lemma sylvester_schur_interval_twenty {m : ℕ} (hm : 20 < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + 20) ∧ p.Prime ∧ 20 < p ∧ p ∣ j

lemma sylvester_schur_interval_le_twenty {m k : ℕ}
    (hk : 0 < k) (hk20 : k ≤ 20) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_threshold_le_twenty {k : ℕ}
    (hk : 0 < k) (hk20 : k ≤ 20) :
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma sylvester_schur_interval_le_forty_eight {m k : ℕ}
    (hk : 0 < k) (hk48 : k ≤ 48) (hm : k < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j
```

The second fragment is Bertrand's postulate: some prime in `(k, 2k]` belongs
to the boundary interval `k + 1, ..., 2k`.
The `k = 2` fragment uses parity: among two consecutive integers above `2`,
one is odd and greater than `1`, hence has an odd prime divisor.
The `k = 3` fragment splits on `m mod 6`; five residue classes contain an odd
number not divisible by `3`, and the remaining class uses
`Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`.
The `k = 4` fragment is a short consequence of `k = 3`, since a prime greater
than `3` cannot be `4`.
The `k ≤ 4` threshold lemma packages these direct cases in the same format
needed by the global threshold route.
The `k = 5` fragment is the first nontrivial use of the threshold route:
starts `m = 6, ..., 11` are checked directly with witnesses `7` and `11`,
while the Granville binomial inequality is checked at `m = 12` and propagated
to all later starts by `choose_inequality_of_ge_start`.
The `k = 6` fragment is similar: starts `m = 7,8` are direct, and the
threshold inequality starts at `m = 9`.
The `k = 7` fragment checks starts below `m = 18` with witnesses
`11`, `13`, and `17`, then propagates the inequality from `m = 18`.
The `k = 8` fragment checks starts below `m = 14` with witnesses `11` and
`13`, then propagates the inequality from `m = 14`.
The `k = 9` fragment checks the two starts below `m = 12` directly with
witness `11`, then propagates the inequality from `m = 12`.
The `k = 10` fragment has no exceptional starts beyond `m > 10`: the
threshold inequality already holds at `m = 11`, and propagation gives all
later starts.
The `k = 11` fragment checks starts below `m = 18` directly with witnesses
`13` and `17`, then propagates the inequality from `m = 18`.
The `k = 12` fragment checks starts below `m = 16` directly with witnesses
`13` and `17`, then propagates the inequality from `m = 16`.
The `k = 13,14,15,16` fragments follow the same threshold pattern, using
small prime witnesses below thresholds `24,22,20,19`, respectively.
The `k = 17,18,19,20` fragments use thresholds `26,24,33,31`,
respectively.  A generated finite extension now covers all `21 ≤ k ≤ 48`,
using the same direct-witness-below-threshold and binomial-inequality-above-
threshold pattern.  The largest threshold in this finite block is `m₀ = 60`
for `k = 47`.
This gives the small-index base case `i ≤ 48` used by the final theorem.

The file now also formalises Granville's standard binomial-coefficient
criterion.  In interval notation, define:

```lean
def SylvesterSchurChooseInequality : Prop :=
  ∀ ⦃m k : ℕ⦄, 0 < k → k < m →
    (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k
```

The following implication is proved:

```lean
theorem sylvester_schur_interval_of_choose_inequality
    (hineq : SylvesterSchurChooseInequality) :
    SylvesterSchurInterval
```

The key supporting lemma is:

```lean
lemma choose_le_pow_primesBelow_card_of_prime_factors_below
    {N k : ℕ} (hkn : k ≤ N) (hN : 0 < N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N k → p < k + 1) :
    Nat.choose N k ≤ N ^ (k + 1).primesBelow.card
```

This is the formal version of the argument: if all prime factors of the
interval are at most `k`, then every prime factor of the binomial coefficient
is below `k + 1`, and each prime-power contribution is at most `N`.

There is now also a direct binomial version of the same criterion, avoiding
the interval product when the goal is already a divisor of `Nat.choose N k`:

```lean
theorem exists_large_prime_factor_of_choose_gt_pow_prime_count_direct
    {N k : ℕ} (hkN : k ≤ N) (hN : 0 < N)
    (hgt : N ^ (k + 1).primesBelow.card < Nat.choose N k) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ Nat.choose N k

theorem sylvester_schur_of_choose_inequality
    (hineq : ∀ ⦃n i : ℕ⦄, 1 ≤ i → i ≤ n / 2 →
      n ^ (i + 1).primesBelow.card < Nat.choose n i)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

The monotonicity part of Granville's criterion is also now formalised:

```lean
lemma choose_inequality_succ_start {m k : ℕ} (hk : 0 < k) (hm : k < m)
    (h : (m + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m + k - 1) k) :
    (m + 1 + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + 1 + k - 1) k
```

The proof uses the natural-number inequality

```lean
lemma succ_pow_mul_sub_le_pow_mul_succ {N r : ℕ} (hr : r ≤ N + 1) :
    (N + 1) ^ r * (N + 1 - r) ≤ N ^ r * (N + 1)
```

together with `Nat.choose_mul_succ_eq`.

The file also proves a fully general large-start version of the binomial
criterion.  The key elementary estimates are:

```lean
lemma primesBelow_succ_card_le_pred (k : ℕ) :
    (k + 1).primesBelow.card ≤ k - 1

lemma primesBelow_succ_card_le_half_add_one (k : ℕ) :
    (k + 1).primesBelow.card ≤ k / 2 + 1

lemma primesBelow_succ_card_le_half {k : ℕ} (hk : 8 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 2

lemma primesBelow_succ_card_le_third {k : ℕ} (hk : 49 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 3

lemma primesBelow_succ_card_le_fourth {k : ℕ} (hk : 2500 ≤ k) :
    (k + 1).primesBelow.card ≤ k / 4

lemma pow_le_ascFactorial (m k : ℕ) :
    m ^ k ≤ m.ascFactorial k

lemma choose_inequality_of_prime_count_bound {m k r : ℕ}
    (hk : 0 < k) (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r)
    (hlarge : k.factorial * (m + k - 1) ^ r < m ^ k) :
    (m + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + k - 1) k

lemma choose_inequality_of_large_start_with_prime_count_bound {m k r : ℕ}
    (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r) (hrk : r < k)
    (hlarge : k.factorial * 2 ^ r < m ^ (k - r)) :
    (m + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + k - 1) k

lemma choose_inequality_of_large_start {m k : ℕ}
    (hk : 1 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k - 1) < m) :
    (m + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + k - 1) k
```

Thus the interval theorem is now proved for every sufficiently large start,
with an explicit elementary threshold depending on `k`:

```lean
theorem sylvester_schur_interval_of_large_start {m k : ℕ}
    (hk : 1 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k - 1) < m) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

theorem sylvester_schur_interval_of_large_start_with_prime_count_bound {m k r : ℕ}
    (hm : k < m)
    (hr_count : (k + 1).primesBelow.card ≤ r) (hrk : r < k)
    (hlarge : k.factorial * 2 ^ r < m ^ (k - r)) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

lemma choose_inequality_of_large_start_half_bound {m k : ℕ}
    (hk : 2 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k / 2 + 1) <
      m ^ (k - (k / 2 + 1))) :
    (m + k - 1) ^ (k + 1).primesBelow.card <
      Nat.choose (m + k - 1) k

theorem sylvester_schur_interval_of_large_start_half_bound {m k : ℕ}
    (hk : 2 < k) (hm : k < m)
    (hlarge : k.factorial * 2 ^ (k / 2 + 1) <
      m ^ (k - (k / 2 + 1))) :
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j
```

This does not finish Sylvester-Schur, but it removes the genuinely asymptotic
part without using prime-counting estimates: for each fixed `k > 1`, only
starts `k < m ≤ k! * 2^(k-1)` remain.

The prime-count parameterized form is the more flexible route for future work:
any certified bound `(k + 1).primesBelow.card ≤ r < k` lowers the remaining
large-start condition to `k! * 2^r < m^(k-r)`.  This avoids asking Lean to
compute large prime-counts directly.

The sharper `choose_inequality_of_prime_count_bound` avoids the auxiliary
estimate `m + k - 1 ≤ 2m`: with a certified prime-count bound
`(k + 1).primesBelow.card ≤ r`, it is enough to prove the exact inequality
`k! * (m+k-1)^r < m^k`.  This is the preferred interface for future finite
certificates and analytic threshold arguments.

The exact target now has the corresponding direct prime-count interface:

```lean
theorem sylvester_schur_of_prime_count_bound
    (n i r : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ r)
    (hlarge : i.factorial * n ^ r < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_half_prime_count_bound
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i.factorial * n ^ (i / 2) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma pow_le_pow_mul_choose (n k : ℕ) (hk : k ≤ n) :
    n ^ k ≤ k ^ k * Nat.choose n k

theorem sylvester_schur_of_power_gap
    (n i r : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ r)
    (hgap : i ^ i * n ^ r < n ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma choose_le_pow_sqrt_mul_primorial_third_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk_half : k ≤ n / 2)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ Nat.choose n k) :
    Nat.choose n k ≤ n ^ n.sqrt * primorial (n / 3)

lemma choose_le_pow_sqrt_mul_primorial_index_of_no_large_prime
    {n k : ℕ} (hn : 0 < n) (hk_half : k ≤ n / 2)
    (hno : ∀ p : ℕ, p.Prime → k < p → ¬ p ∣ Nat.choose n k) :
    Nat.choose n k ≤ n ^ n.sqrt * primorial k

theorem sylvester_schur_of_central_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem real_central_gap_five_halves {x : ℝ} (hx_large : (4410 : ℝ) ≤ x) :
    x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) *
        4 ^ (((5 : ℝ) / 2 * x) / 3) < 4 ^ x

theorem real_scaled_power_boundary_five_halves {x : ℝ} (hx_large : (4840 : ℝ) ≤ x) :
    x * (((5 : ℝ) / 2 * x) ^ √(((5 : ℝ) / 2 * x))) < ((5 : ℝ) / 4) ^ x

theorem real_scaled_power_of_deriv_bound {x y : ℝ} (hx_large : (4840 : ℝ) ≤ x)
    (hy_lower : (5 : ℝ) / 2 * x ≤ y)
    (hderiv : ∀ z ∈ Set.Icc (((5 : ℝ) / 2) * x) y,
      √z * (2 + Real.log z) ≤ 2 * x) :
    x * y ^ √y < (y / (2 * x)) ^ x

theorem real_deriv_bound_four_thirds {x y : ℝ} (hx_large : (4840 : ℝ) ≤ x)
    (hy_pos : 0 < y) (hy_cube : y ^ (3 : ℕ) ≤ x ^ (4 : ℕ)) :
    √y * (2 + Real.log y) ≤ 2 * x

lemma central_gap_of_le_five_halves {n i : ℕ} (hi_large : 4410 ≤ i)
    (hi_half : i ≤ n / 2) (hn_le : 2 * n ≤ 5 * i) :
    i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i

theorem sylvester_schur_of_central_five_halves
    (n i : ℕ) (hi_large : 4410 ≤ i) (hi_half : i ≤ n / 2)
    (hn_le : 2 * n ≤ 5 * i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_factorial_gap
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i.factorial * (n ^ n.sqrt * 4 ^ i) < (n - i + 1) ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma pow_mul_centralBinom_le_pow_mul_choose_of_half
    {n i : ℕ} (hi_half : i ≤ n / 2) :
    n ^ i * i.centralBinom ≤ (2 * i) ^ i * Nat.choose n i

theorem sylvester_schur_of_scaled_central_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i)) < n ^ i * 4 ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_scaled_central_power_gap
    (n i : ℕ) (hi : 4 ≤ i) (hi_half : i ≤ n / 2)
    (hgap : i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma scaled_power_gap_of_four_thirds_window {n i : ℕ} (hi_large : 4840 ≤ i)
    (hi_half : i ≤ n / 2) (hn_lower : 5 * i ≤ 2 * n) (hn_upper : n ^ 3 ≤ i ^ 4) :
    i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i

theorem sylvester_schur_of_four_thirds_window
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2)
    (hn_lower : 5 * i ≤ 2 * n) (hn_upper : n ^ 3 ≤ i ^ 4) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma pow_mul_pow_half_lt_pow_of_sq_lt {n i : ℕ}
    (hi : 0 < i) (hlarge : i ^ 2 < n) :
    i ^ i * n ^ (i / 2) < n ^ i

theorem sylvester_schur_of_superquadratic_top
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 2 < n) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma pow_mul_pow_third_lt_pow_of_cube_lt_sq {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hlarge : i ^ 3 < n ^ 2) :
    i ^ i * n ^ (i / 3) < n ^ i

theorem sylvester_schur_of_third_prime_count_bound
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ i / 3)
    (hlarge : i ^ 3 < n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_cube_lt_square
    (n i : ℕ) (hi : 49 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 3 < n ^ 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma pow_mul_pow_fourth_lt_pow_of_fourth_lt_cube {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hlarge : i ^ 4 < n ^ 3) :
    i ^ i * n ^ (i / 4) < n ^ i

theorem sylvester_schur_of_fourth_prime_count_bound
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hr_count : (i + 1).primesBelow.card ≤ i / 4)
    (hlarge : i ^ 4 < n ^ 3) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_fourth_lt_cube
    (n i : ℕ) (hi : 2500 ≤ i) (hi_half : i ≤ n / 2)
    (hlarge : i ^ 4 < n ^ 3) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty
    (n i : ℕ) (hi_large : 4840 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma factorial_mul_pow_half_lt_of_quadratic_large {n i : ℕ}
    (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hm_large : 4 * i ^ 2 ≤ n - i + 1) :
    i.factorial * n ^ (i / 2) < (n - i + 1) ^ i

theorem sylvester_schur_of_quadratic_large
    (n i : ℕ) (hi : 8 ≤ i) (hi_half : i ≤ n / 2)
    (hm_large : 4 * i ^ 2 ≤ n - i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_large_n {n i : ℕ}
    (hi : 1 < i) (hi_half : i ≤ n / 2)
    (hlarge : i.factorial * 2 ^ (i - 1) < n - i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma prime_dvd_choose_of_dvd_mem_interval
    {n i p j : ℕ} (hi_le_n : i ≤ n) (hp : p.Prime) (hip : i < p)
    (hj : j ∈ Set.Ico (n - i + 1) (n + 1)) (hpj : p ∣ j) :
    p ∣ Nat.choose n i

theorem sylvester_schur_of_prime_in_top_interval
    (n i : ℕ) (hi_half : i ≤ n / 2)
    (hprime : ∃ p : ℕ, p.Prime ∧ n - i < p ∧ p ≤ n) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_twice
    (n i : ℕ) (hi : 1 ≤ i) (hn : n = 2 * i) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_twice_add_one
    (n i : ℕ) (hi : 1 ≤ i) (hn : n = 2 * i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

lemma exists_prime_sub_49_le_of_le_600 (n : ℕ) (hlo : 98 ≤ n) (hhi : n ≤ 600) :
    ∃ p : ℕ, p.Prime ∧ n - 49 < p ∧ p ≤ n

lemma exists_prime_sub_72_le_of_le_125000 (n : ℕ) (hlo : 144 ≤ n)
    (hhi : n ≤ 125000) :
    ∃ p : ℕ, p.Prime ∧ n - 72 < p ∧ p ≤ n

theorem sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty
    (n i : ℕ) (hi49 : 49 ≤ i) (hi_lt : i < 4840) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_current_frontier
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2)
    (hcovered :
      i ≤ 48 ∨ 4840 ≤ i ∨ 8 ≤ i ∧ i ^ 2 < n ∨ 49 ≤ i ∧ i ^ 3 < n ^ 2 ∨
      2500 ≤ i ∧ i ^ 4 < n ^ 3 ∨
      4410 ≤ i ∧ 2 * n ≤ 5 * i ∨
      4 ≤ i ∧ i * (n ^ n.sqrt * 4 ^ (n / 3)) < 4 ^ i ∨
      i.factorial * (n ^ n.sqrt * 4 ^ i) < (n - i + 1) ^ i ∨
      4 ≤ i ∧ i * ((2 * i) ^ i * n ^ n.sqrt) < n ^ i ∨
      4 ≤ i ∧ i * ((2 * i) ^ i * (n ^ n.sqrt * 4 ^ i)) < n ^ i * 4 ^ i ∨
      n = 2 * i ∨ n = 2 * i + 1) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

The latter theorem is the exact binomial target for the large-start range
already covered by the interval proof, stated without the intermediate
`SylvesterSchurInterval`.

The file now includes the elementary all-`k` bound
`(k + 1).primesBelow.card ≤ k / 2 + 1`, obtained by separating the prime `2`
from the odd primes and mapping each odd prime `p ≤ k` to `p / 2`.  This gives
a concrete instantiation of the parameterized large-start route with
`r = k / 2 + 1`; it is mainly scaffolding for stronger certified prime-count
estimates.

For `k ≥ 8`, the file sharpens this elementary count to
`(k + 1).primesBelow.card ≤ k / 2`.  The even case maps odd primes below
`k + 1` into the odd numbers `3, 5, ..., k - 1`; the odd case removes the
composite odd number `9` from the candidate list.

For `k ≥ 49`, there is now also a residue-class bound
`(k + 1).primesBelow.card ≤ k / 3`.  The proof puts every prime above `3`
in one of the two residue classes `1` or `5` modulo `6`, then removes the
fixed composite candidates `1`, `25`, `35`, and `49` from the resulting
superset.  This gives a certified one-third prime-count interface without
using analytic number theory.

For `k ≥ 2500`, the file further proves
`(k + 1).primesBelow.card ≤ k / 4` by covering all primes above `7` with
the 48 residue classes coprime to `210 = 2 * 3 * 5 * 7`.  The residue-class
cardinality is checked by kernel `decide`; no `native_decide` or external
computation is used in the proof object.

The file now has a second, sharper binomial lower-bound interface.  The lemma
`pow_le_pow_mul_choose` proves the classical estimate
`n^k ≤ k^k * choose n k`; its proof is an induction in the top parameter,
using the already-formalized monotonicity inequality
`(N+1)^r * (N+1-r) ≤ N^r * (N+1)`.  Combining this lower bound with the
half-prime-count upper bound proves the exact target whenever `i ≥ 8` and
`i^2 < n`.

The same interface has been generalized to a one-third prime-count route:
`pow_mul_pow_third_lt_pow_of_cube_lt_sq` proves
`i^i * n^(i/3) < n^i` from `i^3 < n^2`; combined with the one-third
prime-count bound, this proves the exact target whenever `i ≥ 49` and
`i^3 < n^2`.

The fourth-prime-count route is analogous:
`pow_mul_pow_fourth_lt_pow_of_fourth_lt_cube` proves
`i^i * n^(i/4) < n^i` from `i^4 < n^3`; combined with the modulo-210
prime-count bound, this proves the exact target whenever `i ≥ 2500` and
`i^4 < n^3`.

The file now also has the first piece of the classical Erdős/Sylvester-Schur
large-prime-factor split.  If no prime above `i` divides `choose n i`, the
prime factors are split at `sqrt n`: primes below `sqrt n` contribute at most
`n` each, while primes above `sqrt n` have multiplicity at most one.  The
medium-prime part is bounded either by `primorial i`, or, using
`Nat.factorization_choose_of_lt_three_mul`, by `primorial (n/3)`.
Together with `primorial_le_4_pow`, this gives two new exact-target
interfaces:

* `sylvester_schur_of_central_gap`, using the central binomial lower bound
  `4^i < i * centralBinom i`, is aimed at the near-central range
  `2i ≤ n < 3i`.
* `sylvester_schur_of_central_five_halves` now discharges a concrete
  near-central subrange: for `i ≥ 4410` and `2n ≤ 5i`, a Bertrand-style
  concavity estimate proves the central-gap hypothesis.
  The complementary boundary estimate
  `real_scaled_power_boundary_five_halves` is also formalised: for
  `i ≥ 4840`, the scaled-power inequality holds at the boundary
  `n = 5i/2`.  The derivative package
  `real_scaled_power_of_deriv_bound` propagates this boundary estimate while
  `√n * (2 + log n) ≤ 2i`; the concrete estimate
  `real_deriv_bound_four_thirds` verifies that condition throughout
  `n^3 ≤ i^4`.  Together these prove the exact target for all `i ≥ 4840`.
* `sylvester_schur_of_factorial_gap`, using
  `(n-i+1)^i ≤ i! * choose n i`, is aimed at the range starting around
  `n ≥ 3i` before the existing power-gap estimates take over.
* `sylvester_schur_of_scaled_central_gap`, using the termwise ratio
  `n^i * centralBinom i ≤ (2i)^i * choose n i`, supplies a variable-strength
  central lower bound.  This is intended for the middle range where `n/i`
  is bounded away from `2` but not large enough for the cruder factorial
  interface.  The corollary `sylvester_schur_of_scaled_central_power_gap`
  cancels the common `4^i` factor from the hypothesis and is the cleaner
  interface for future numerical inequalities.

The older factorial interface is still useful and remains in the file: using
`i! ≤ i^i`, `n ≤ 2(n-i+1)`, and the half-prime-count bound, it proves the
target whenever `4 * i^2 ≤ n - i + 1`.

The exact target is now proved for all indices.  The final theorem splits into
three ranges:

* `i ≤ 48`, handled by the finite interval-threshold development.
* `i ≥ 4840`, handled by the central/four-thirds analytic split above.
* `49 ≤ i < 4840`, handled by the finite-index theorem
  `sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty`.

The finite-index theorem closes the former gap by combining the one-third and
one-fourth power routes with generated prime-gap certificates.  For
`49 ≤ i < 72`, either `i^3 < n^2` and the one-third route applies, or
`n ≤ 600` and `exists_prime_sub_49_le_of_le_600` supplies a prime in the top
numerator interval.  For `72 ≤ i < 2500`, either the one-third route applies,
or `n ≤ 125000` and `exists_prime_sub_72_le_of_le_125000` supplies such a
prime.  For `2500 ≤ i < 4840`, either `i^4 < n^3` and the one-fourth route
applies, or the same `n ≤ 125000` prime-gap certificate supplies the top
interval prime.

The older regional theorem `sylvester_schur_current_frontier` is retained as a
useful diagnostic statement, but it is no longer the endpoint of the
formalisation.

Two stronger interval-theorem routes are still named explicitly:

```lean
def SylvesterSchurSmallStart : Prop :=
  ∀ ⦃m k : ℕ⦄, 1 < k → k < m → m ≤ k.factorial * 2 ^ (k - 1) →
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

theorem sylvester_schur_interval_of_small_start
    (hsmall : SylvesterSchurSmallStart) :
    SylvesterSchurInterval

theorem sylvester_schur_of_small_start
    (hsmall : SylvesterSchurSmallStart)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

The small-start route is packaged through the following corrected threshold
interface:

```lean
def SylvesterSchurIntervalThreshold : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ m₀ : ℕ, k < m₀ ∧
      (m₀ + k - 1) ^ (k + 1).primesBelow.card < Nat.choose (m₀ + k - 1) k ∧
      ∀ m : ℕ, k < m → m < m₀ →
        ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j

theorem sylvester_schur_interval_of_threshold
    (hbase : SylvesterSchurIntervalThreshold) :
    SylvesterSchurInterval
```

The original binomial target is also connected directly to this threshold
obligation:

```lean
theorem sylvester_schur_of_interval_threshold
    (hthreshold : SylvesterSchurIntervalThreshold)
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_index_le_twenty
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) (hi20 : i ≤ 20) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

theorem sylvester_schur_of_index_le_forty_eight
    (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) (hi48 : i ≤ 48) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i
```

No unproved theorem from `formal-conjectures` is used to close the target.
The full classical interval Sylvester-Schur theorem remains available as a
stronger auxiliary route, but it is not needed for the final binomial theorem:

```lean
def SylvesterSchurInterval : Prop :=
  ∀ ⦃m k : ℕ⦄, 0 < k → k < m →
    ∃ j p : ℕ, j ∈ Set.Ico m (m + k) ∧ p.Prime ∧ k < p ∧ p ∣ j
```

The finite frontier has also been pushed through to the exact binomial target:
`sylvester_schur_of_index_le_forty_eight` proves the desired theorem whenever
the lower index satisfies `i ≤ 48`, and
`sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty` proves the
remaining finite range `49 ≤ i < 4840`.

## Why This Was The Hard Part

The local libraries contain the needed factorial and binomial APIs:

- `Nat.ascFactorial_eq_factorial_mul_choose`
- `Nat.Prime.dvd_factorial`
- `Nat.mem_smoothNumbers'`
- Kummer/Legendre-style factorization lemmas for binomial coefficients.

They do not contain a proved Sylvester-Schur theorem.  The statement in
`FormalConjectures.ErdosProblems.961` is still a `sorry`, and using it directly
would not be a genuine formalisation of Erdős 699.

The completed proof avoids importing a proved Sylvester-Schur interval theorem
by combining partial interval-threshold arguments, prime-count estimates,
real inequalities, and generated finite prime-gap certificates.  The
asymptotic large-start route remains in the file, but it is not the only
closing mechanism.

This also explains the relation to benchmark task `erdosproblems-961-
sylvester-schur`: proving the missing interval theorem would essentially solve
that target as well, but Erdős 699 is now closed directly through the binomial
formulation.

## Informal Proof Sources

- P. Erdős, "A theorem of Sylvester and Schur", Journal of the London
  Mathematical Society 9 (1934), 282-288.
  Public scan: https://users.renyi.hu/~p_erdos/1934-01.pdf
- J. J. Sylvester, "On arithmetical series", Messenger of Mathematics 21
  (1892), 1-19 and 87-120.
- I. Schur, "Einige Sätze über Primzahlen mit Anwendung auf
  Irreduzibilitätsfragen", Sitzungsberichte der Preussischen Akademie der
  Wissenschaften, Phys.-Math. Klasse 23 (1929), 1-24.
- Steven Brown, "An alternative proof of Sylvester's theorem and variations for
  more primes", arXiv:2303.05395.  This proof is modern and readable, but it
  uses real logarithmic estimates and finite computation, so it is not
  obviously shorter to formalise in Lean than Erdős's proof.

## Completed Milestones

1. Prove the small-index base case `i ≤ 48`.
2. Prove the large-index range `i ≥ 4840` using the central/four-thirds split.
3. Close the finite range `49 ≤ i < 4840` with one-third/fourth power routes
   plus generated prime-gap certificates.
4. Assemble the unconditional theorem `sylvester_schur`.

## Verification

The current formalisation file builds with:

```bash
cd formalizations/erdos699
lake build
```

The bridge theorems have no `sorryAx` dependency:

```lean
#print axioms Erdos699Formalization.sylvester_schur_interval_one
#print axioms Erdos699Formalization.sylvester_schur_interval_boundary
#print axioms Erdos699Formalization.odd_has_prime_gt_two
#print axioms Erdos699Formalization.sylvester_schur_interval_two
#print axioms Erdos699Formalization.odd_not_three_dvd_has_prime_gt_three
#print axioms Erdos699Formalization.odd_prime_dvd_not_three_has_prime_gt_three
#print axioms Erdos699Formalization.sylvester_schur_interval_three
#print axioms Erdos699Formalization.sylvester_schur_interval_four
#print axioms Erdos699Formalization.sylvester_schur_interval_le_four
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_four
#print axioms Erdos699Formalization.sylvester_schur_interval_five
#print axioms Erdos699Formalization.sylvester_schur_interval_le_five
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_five
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_five
#print axioms Erdos699Formalization.sylvester_schur_interval_six
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_six
#print axioms Erdos699Formalization.sylvester_schur_interval_le_six
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_six
#print axioms Erdos699Formalization.sylvester_schur_interval_seven
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_seven
#print axioms Erdos699Formalization.sylvester_schur_interval_le_seven
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_seven
#print axioms Erdos699Formalization.sylvester_schur_interval_eight
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_eight
#print axioms Erdos699Formalization.sylvester_schur_interval_le_eight
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_eight
#print axioms Erdos699Formalization.sylvester_schur_interval_nine
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_nine
#print axioms Erdos699Formalization.sylvester_schur_interval_ten
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_ten
#print axioms Erdos699Formalization.sylvester_schur_interval_le_ten
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_ten
#print axioms Erdos699Formalization.sylvester_schur_interval_eleven
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_eleven
#print axioms Erdos699Formalization.sylvester_schur_interval_le_eleven
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_eleven
#print axioms Erdos699Formalization.sylvester_schur_interval_twelve
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_twelve
#print axioms Erdos699Formalization.sylvester_schur_interval_le_twelve
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_twelve
#print axioms Erdos699Formalization.sylvester_schur_interval_prime_witness
#print axioms Erdos699Formalization.sylvester_schur_interval_thirteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_thirteen
#print axioms Erdos699Formalization.sylvester_schur_interval_fourteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_fourteen
#print axioms Erdos699Formalization.sylvester_schur_interval_fifteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_fifteen
#print axioms Erdos699Formalization.sylvester_schur_interval_sixteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_sixteen
#print axioms Erdos699Formalization.sylvester_schur_interval_le_sixteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_sixteen
#print axioms Erdos699Formalization.sylvester_schur_interval_seventeen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_seventeen
#print axioms Erdos699Formalization.sylvester_schur_interval_eighteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_eighteen
#print axioms Erdos699Formalization.sylvester_schur_interval_nineteen
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_nineteen
#print axioms Erdos699Formalization.sylvester_schur_interval_twenty
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_twenty
#print axioms Erdos699Formalization.sylvester_schur_interval_le_twenty
#print axioms Erdos699Formalization.sylvester_schur_interval_threshold_le_twenty
#print axioms Erdos699Formalization.sylvester_schur_interval_le_forty_eight
#print axioms Erdos699Formalization.dvd_ascFactorial_of_mem
#print axioms Erdos699Formalization.prime_not_dvd_factorial_of_lt
#print axioms Erdos699Formalization.exists_mem_Ico_dvd_of_prime_dvd_ascFactorial
#print axioms Erdos699Formalization.choose_le_pow_primesBelow_card_of_prime_factors_below
#print axioms Erdos699Formalization.exists_large_prime_factor_of_choose_gt_pow_prime_count_direct
#print axioms Erdos699Formalization.exists_large_prime_factor_of_choose_gt_pow_prime_count
#print axioms Erdos699Formalization.sylvester_schur_interval_of_choose_inequality
#print axioms Erdos699Formalization.sylvester_schur_of_choose_inequality
#print axioms Erdos699Formalization.succ_pow_mul_sub_le_pow_mul_succ
#print axioms Erdos699Formalization.choose_inequality_succ
#print axioms Erdos699Formalization.pow_le_pow_mul_choose
#print axioms Erdos699Formalization.primesBelow_succ_card_le
#print axioms Erdos699Formalization.choose_inequality_succ_start
#print axioms Erdos699Formalization.choose_inequality_of_ge_start
#print axioms Erdos699Formalization.primesBelow_succ_card_le_pred
#print axioms Erdos699Formalization.primesBelow_succ_card_le_half_add_one
#print axioms Erdos699Formalization.primesBelow_succ_card_le_half
#print axioms Erdos699Formalization.primesBelow_succ_card_le_third
#print axioms Erdos699Formalization.primesBelow_succ_card_le_fourth
#print axioms Erdos699Formalization.pow_le_ascFactorial
#print axioms Erdos699Formalization.ascFactorial_eq_factorial_mul_choose_start
#print axioms Erdos699Formalization.choose_inequality_of_prime_count_bound
#print axioms Erdos699Formalization.sylvester_schur_of_prime_count_bound
#print axioms Erdos699Formalization.sylvester_schur_of_half_prime_count_bound
#print axioms Erdos699Formalization.sylvester_schur_of_power_gap
#print axioms Erdos699Formalization.pow_mul_pow_half_lt_pow_of_sq_lt
#print axioms Erdos699Formalization.sylvester_schur_of_superquadratic_top
#print axioms Erdos699Formalization.pow_mul_pow_third_lt_pow_of_cube_lt_sq
#print axioms Erdos699Formalization.sylvester_schur_of_third_prime_count_bound
#print axioms Erdos699Formalization.sylvester_schur_of_cube_lt_square
#print axioms Erdos699Formalization.pow_mul_pow_fourth_lt_pow_of_fourth_lt_cube
#print axioms Erdos699Formalization.sylvester_schur_of_fourth_prime_count_bound
#print axioms Erdos699Formalization.sylvester_schur_of_fourth_lt_cube
#print axioms Erdos699Formalization.real_scaled_power_of_deriv_bound
#print axioms Erdos699Formalization.real_deriv_bound_four_thirds
#print axioms Erdos699Formalization.scaled_power_gap_of_deriv_bound
#print axioms Erdos699Formalization.scaled_power_gap_of_four_thirds_window
#print axioms Erdos699Formalization.sylvester_schur_of_four_thirds_window
#print axioms Erdos699Formalization.sylvester_schur_of_index_ge_four_thousand_eight_hundred_forty
#print axioms Erdos699Formalization.factorial_mul_pow_half_lt_of_quadratic_large
#print axioms Erdos699Formalization.sylvester_schur_of_quadratic_large
#print axioms Erdos699Formalization.sylvester_schur_of_large_n
#print axioms Erdos699Formalization.prime_dvd_choose_of_dvd_mem_interval
#print axioms Erdos699Formalization.sylvester_schur_of_prime_in_top_interval
#print axioms Erdos699Formalization.sylvester_schur_of_twice
#print axioms Erdos699Formalization.sylvester_schur_of_twice_add_one
#print axioms Erdos699Formalization.exists_prime_sub_49_le_of_le_600
#print axioms Erdos699Formalization.exists_prime_sub_72_le_of_le_125000
#print axioms Erdos699Formalization.sylvester_schur_of_index_lt_four_thousand_eight_hundred_forty
#print axioms Erdos699Formalization.sylvester_schur
#print axioms Erdos699Formalization.sylvester_schur_current_frontier
#print axioms Erdos699Formalization.choose_inequality_of_large_start_with_prime_count_bound
#print axioms Erdos699Formalization.choose_inequality_of_large_start
#print axioms Erdos699Formalization.sylvester_schur_interval_of_large_start
#print axioms Erdos699Formalization.sylvester_schur_interval_of_large_start_with_prime_count_bound
#print axioms Erdos699Formalization.choose_inequality_of_large_start_half_bound
#print axioms Erdos699Formalization.sylvester_schur_interval_of_large_start_half_bound
#print axioms Erdos699Formalization.sylvester_schur_interval_of_small_start
#print axioms Erdos699Formalization.sylvester_schur_interval_of_threshold
#print axioms Erdos699Formalization.sylvester_schur_of_interval
#print axioms Erdos699Formalization.sylvester_schur_of_index_le_twenty
#print axioms Erdos699Formalization.sylvester_schur_of_index_le_forty_eight
#print axioms Erdos699Formalization.sylvester_schur_of_interval_threshold
#print axioms Erdos699Formalization.sylvester_schur_of_small_start
#print axioms Erdos699Formalization.interval_of_erdos961
#print axioms Erdos699Formalization.sylvester_schur_of_erdos961
```

Each reports only the standard Lean/quotient axioms: `propext`,
`Classical.choice`, and `Quot.sound`.

## Completion Update

This target was materially harder than the initial roadmap suggested.  The
bridge is short, but the full theorem required a substantial number-theory
development rather than a direct application of existing Mathlib lemmas.

The final proof is now present as `Erdos699Formalization.sylvester_schur`.
It is comparable to a larger benchmark contribution rather than to the shorter
previous Erdős 330, Erdős 953, Erdős 1151, or AME(4,3) formalisation tasks.
