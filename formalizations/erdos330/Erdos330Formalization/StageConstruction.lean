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

/-- The active set after activating a dormant element. -/
def activatedActiveSet (st : StageState) (b : ℕ) : Finset ℕ :=
  insert b st.P

/-- The modulus assignment after activating `b` with fresh modulus `p`. -/
def activatedModulus (st : StageState) (b p : ℕ) : ℕ → ℕ :=
  fun c => if c = b then p else st.m c

/-- The active modulus product after activating `b`. -/
def activatedM (st : StageState) (b p : ℕ) : ℕ :=
  (activatedActiveSet st b).prod (activatedModulus st b p)

theorem activatedModulus_new (st : StageState) (b p : ℕ) :
    activatedModulus st b p b = p := by
  simp [activatedModulus]

theorem activatedModulus_old_of_ne (st : StageState) {b p c : ℕ} (hcb : c ≠ b) :
    activatedModulus st b p c = st.m c := by
  simp [activatedModulus, hcb]

theorem activatedModulus_old_of_mem (st : StageState) {b p c : ℕ}
    (hbDormant : b ∉ st.P) (hc : c ∈ st.P) :
    activatedModulus st b p c = st.m c := by
  exact activatedModulus_old_of_ne st (fun hcb => hbDormant (hcb ▸ hc))

theorem activated_m_prime (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ c ∈ activatedActiveSet st b, Nat.Prime (activatedModulus st b p c) := by
  intro c hc
  rw [activatedActiveSet] at hc
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · simpa [activatedModulus_new] using hp.prime
  · rw [activatedModulus_old_of_mem st hbDormant hcP]
    exact st.m_prime c hcP

theorem activated_m_ge23 (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ c ∈ activatedActiveSet st b, 23 ≤ activatedModulus st b p c := by
  intro c hc
  rw [activatedActiveSet] at hc
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · simpa [activatedModulus_new] using hp.ge23
  · rw [activatedModulus_old_of_mem st hbDormant hcP]
    exact st.m_ge23 c hcP

theorem activated_m_mod4 (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ c ∈ activatedActiveSet st b, activatedModulus st b p c % 4 = 3 := by
  intro c hc
  rw [activatedActiveSet] at hc
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · simpa [activatedModulus_new] using hp.mod4
  · rw [activatedModulus_old_of_mem st hbDormant hcP]
    exact st.m_mod4 c hcP

theorem activated_m_pairwise_coprime (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    ∀ ⦃c⦄, c ∈ activatedActiveSet st b →
      ∀ ⦃d⦄, d ∈ activatedActiveSet st b → c ≠ d →
        Nat.Coprime (activatedModulus st b p c) (activatedModulus st b p d) := by
  intro c hc d hd hcd
  rw [activatedActiveSet] at hc hd
  rcases Finset.mem_insert.mp hc with rfl | hcP
  · rcases Finset.mem_insert.mp hd with hdb | hdP
    · exact (hcd hdb.symm).elim
    · simpa [activatedModulus_new, activatedModulus_old_of_mem st hbDormant hdP]
        using hp.coprime_old d hdP
  · rcases Finset.mem_insert.mp hd with rfl | hdP
    · simpa [activatedModulus_new, activatedModulus_old_of_mem st hbDormant hcP]
        using (hp.coprime_old c hcP).symm
    · rw [activatedModulus_old_of_mem st hbDormant hcP,
        activatedModulus_old_of_mem st hbDormant hdP]
      exact st.m_pairwise_coprime hcP hdP hcd

theorem activatedM_eq (st : StageState) {b p : ℕ} (hbDormant : b ∉ st.P) :
    activatedM st b p = p * st.M := by
  classical
  unfold activatedM activatedActiveSet
  rw [Finset.prod_insert hbDormant, activatedModulus_new, st.M_def]
  congr 1
  exact Finset.prod_congr rfl fun c hc =>
    activatedModulus_old_of_mem st hbDormant hc

theorem activatedM_pos (st : StageState) {b p : ℕ}
    (hbDormant : b ∉ st.P) (hp : FreshPrimeData st p) :
    0 < activatedM st b p := by
  rw [activatedM_eq st hbDormant]
  have hMpos : 0 < st.M := by
    rw [st.M_def]
    exact Finset.prod_pos fun c hc => st.modulus_pos hc
  exact Nat.mul_pos hp.prime.pos hMpos

end Erdos330Formalization
