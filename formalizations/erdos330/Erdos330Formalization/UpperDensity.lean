import Erdos330Formalization.Global

/-!
# Upper-density helper lemmas for Erdős Problem 330

The construction naturally produces dense finite blocks at arbitrarily large
endpoints.  This file bridges those witnesses to the `Set.upperDensity` API.
-/

namespace Erdos330Formalization

open Filter

theorem partialDensity_univ_nat (S : Set ℕ) (b : ℕ) :
    S.partialDensity Set.univ b = ((S ∩ Set.Iio b).ncard : ℝ) / b := by
  simp [Set.partialDensity, Nat.ncard_Iio]

theorem le_partialDensity_univ_nat_of_count {S : Set ℕ} {b : ℕ} {c : ℝ}
    (hb : 0 < b)
    (hcount : c * (b : ℝ) ≤ ((S ∩ Set.Iio b).ncard : ℝ)) :
    c ≤ S.partialDensity Set.univ b := by
  rw [partialDensity_univ_nat]
  rwa [le_div_iff₀ (Nat.cast_pos.mpr hb)]

theorem le_partialDensity_univ_nat_of_finset {S : Set ℕ} {B : Finset ℕ} {b : ℕ} {c : ℝ}
    (hb : 0 < b)
    (hB : ∀ n ∈ B, n ∈ S ∧ n < b)
    (hcount : c * (b : ℝ) ≤ (B.card : ℝ)) :
    c ≤ S.partialDensity Set.univ b := by
  have hBsub : (B : Set ℕ) ⊆ S ∩ Set.Iio b := by
    intro n hn
    exact hB n hn
  have hcard_nat : B.card ≤ (S ∩ Set.Iio b).ncard := by
    simpa using Set.ncard_le_ncard hBsub
  have hcard_real : (B.card : ℝ) ≤ ((S ∩ Set.Iio b).ncard : ℝ) := by
    exact_mod_cast hcard_nat
  exact le_partialDensity_univ_nat_of_count hb (hcount.trans hcard_real)

/--
Arbitrarily late positive lower bounds on partial density imply positive upper
density.  This is the main limsup bridge used by the global construction.
-/
theorem upperDensity_pos_of_frequently_partialDensity_ge {S : Set ℕ} {c : ℝ}
    (hc : 0 < c)
    (hfreq : ∀ N : ℕ, ∃ b : ℕ, N ≤ b ∧ c ≤ S.partialDensity Set.univ b) :
    0 < S.upperDensity := by
  have hbounded :
      Filter.atTop.IsBoundedUnder (· ≤ ·) (fun b : ℕ => S.partialDensity Set.univ b) := by
    refine isBoundedUnder_of_eventually_le (a := (1 : ℝ)) ?_
    exact Eventually.of_forall fun b => Set.partialDensity_le_one S Set.univ b
  have hle : c ≤ S.upperDensity := by
    rw [Set.upperDensity]
    refine le_limsup_of_le hbounded ?_
    intro B hB
    rcases eventually_atTop.mp hB with ⟨N, hN⟩
    rcases hfreq N with ⟨b, hbN, hcb⟩
    exact hcb.trans (hN b hbN)
  exact hc.trans_le hle

end Erdos330Formalization
