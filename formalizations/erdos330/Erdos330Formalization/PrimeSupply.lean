import Mathlib.NumberTheory.LSeries.PrimesInAP
import Erdos330Formalization.UpperDensity

/-!
# Prime supply for Erdős Problem 330

The roadmap suggests an elementary Euclid-style proof for primes `3 mod 4`.
For now we use Mathlib's formalized Dirichlet theorem in arithmetic
progressions as a reliable supply lemma.
-/

namespace Erdos330Formalization

theorem exists_prime_three_mod_four_ge (N : ℕ) :
    ∃ p ≥ N, Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hpgt, hpprime, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3)
      (by decide) (by decide : Nat.Coprime 3 4)
  exact ⟨p, hpgt.le, hpprime, by simpa using hpmod⟩

theorem exists_prime_three_mod_four_gt (N : ℕ) :
    ∃ p > N, Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hpge, hpprime, hpmod⟩ := exists_prime_three_mod_four_ge (N + 1)
  exact ⟨p, Nat.succ_le_iff.mp hpge, hpprime, hpmod⟩

end Erdos330Formalization
