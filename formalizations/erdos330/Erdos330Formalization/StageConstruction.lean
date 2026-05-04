import Erdos330Formalization.PrimeSupply
import Erdos330Formalization.StageCoverage

/-!
# Stage-construction data for Erdős Problem 330

This file starts the concrete one-stage construction layer.  The first part is
the fresh-prime package used when activating a dormant element.
-/

namespace Erdos330Formalization

structure FreshPrimeData (st : StageState) (p : ℕ) where
  X_lt_p : st.X < p
  ge23 : 23 ≤ p
  prime : Nat.Prime p
  mod4 : p % 4 = 3

theorem exists_freshPrimeData (st : StageState) : ∃ p : ℕ, FreshPrimeData st p := by
  obtain ⟨p, hpge, hpprime, hpmod⟩ := exists_prime_three_mod_four_ge (max (st.X + 1) 23)
  refine ⟨p, ?_⟩
  exact {
    X_lt_p := by omega
    ge23 := by omega
    prime := hpprime
    mod4 := hpmod
  }

theorem FreshPrimeData.eq_of_zmod_eq_of_old {st : StageState} {p u v : ℕ}
    (hp : FreshPrimeData st p) (hu : u ≤ st.X) (hv : v ≤ st.X)
    (huv : (u : ZMod p) = (v : ZMod p)) :
    u = v :=
  nat_eq_of_zmod_eq_of_le_lt hu hv hp.X_lt_p huv

end Erdos330Formalization
