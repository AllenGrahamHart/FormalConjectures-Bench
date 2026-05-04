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
  M_lt_p : st.M < p
  ge23 : 23 ≤ p
  prime : Nat.Prime p
  mod4 : p % 4 = 3
  coprime_old : ∀ a ∈ st.P, Nat.Coprime p (st.m a)

theorem exists_freshPrimeData (st : StageState) : ∃ p : ℕ, FreshPrimeData st p := by
  obtain ⟨p, hpge, hpprime, hpmod⟩ :=
    exists_prime_three_mod_four_ge (max (max (st.X + 1) (st.M + 1)) 23)
  refine ⟨p, ?_⟩
  exact {
    X_lt_p := by omega
    M_lt_p := by omega
    ge23 := by omega
    prime := hpprime
    mod4 := hpmod
    coprime_old := by
      intro a ha
      have hmpos : 0 < st.m a := st.modulus_pos ha
      have hprod_pos : 0 < st.P.prod st.m := by
        exact Finset.prod_pos (fun b hb => st.modulus_pos hb)
      have hMpos : 0 < st.M := by
        rw [st.M_def]
        exact hprod_pos
      have hdvd : st.m a ∣ st.M := by
        rw [st.M_def]
        exact Finset.dvd_prod_of_mem st.m ha
      have hm_le_M : st.m a ≤ st.M := Nat.le_of_dvd hMpos hdvd
      have hm_lt_p : st.m a < p := lt_of_le_of_lt hm_le_M (by omega)
      exact Nat.coprime_of_lt_prime (Nat.ne_of_gt hmpos) hm_lt_p hpprime
  }

theorem FreshPrimeData.eq_of_zmod_eq_of_old {st : StageState} {p u v : ℕ}
    (hp : FreshPrimeData st p) (hu : u ≤ st.X) (hv : v ≤ st.X)
    (huv : (u : ZMod p) = (v : ZMod p)) :
    u = v :=
  nat_eq_of_zmod_eq_of_le_lt hu hv hp.X_lt_p huv

end Erdos330Formalization
