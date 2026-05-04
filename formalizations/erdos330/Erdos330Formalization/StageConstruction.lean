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

/--
Concrete numeric and CRT choices for one service-and-tail stage after activating
`b`.  The inequality fields are intentionally added only as later lemmas need
them; this structure starts by naming the three new finite blocks.
-/
structure StageParams (st : StageState) (a b p : ℕ) where
  Dplus : Finset (ZMod (activatedM st b p))
  G : CRTGadget (activatedActiveSet st b) (activatedModulus st b p)
    (activatedM st b p) a Dplus
  N : ℕ
  L : ℕ
  LZ : ℕ

namespace StageParams

def Mplus {st : StageState} {a b p : ℕ} (_params : StageParams st a b p) : ℕ :=
  activatedM st b p

/-- Endpoint reached after the service block and private block. -/
def serviceR {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  2 * params.N + 2 * params.L - params.Mplus

/-- Endpoint of the protected private sums, before the tail starts. -/
def protectedEndpoint {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  params.serviceR - st.X

/-- Lower endpoint of the next tail reservoir. -/
def K {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  params.protectedEndpoint + 1

def nextX {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  params.K + params.LZ

def nextR {st : StageState} {a b p : ℕ} (params : StageParams st a b p) : ℕ :=
  2 * params.K + 2 * params.LZ - params.Mplus

/-- The service block using the CRT gadget's `T` residues. -/
def lowerBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  residueBlockFinset params.Mplus params.G.T params.N (params.N + params.L)

/-- The private-partner block whose translate by `a` is protected. -/
def privateBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  residueBlockFinset params.Mplus params.G.Pstar
    (2 * params.N + params.Mplus - a) (params.serviceR - a)

/-- The tail reservoir for the next stage. -/
def tailBlock {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  residueBlockFinset params.Mplus params.Dplus params.K params.nextX

/-- The finite set after adding all three new blocks. -/
def nextS {st : StageState} {a b p : ℕ} (params : StageParams st a b p) :
    Finset ℕ :=
  ((st.S ∪ params.lowerBlock) ∪ params.privateBlock) ∪ params.tailBlock

theorem old_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    st.S ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem lowerBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.lowerBlock ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem privateBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.privateBlock ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem tailBlock_subset_nextS {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) :
    params.tailBlock ⊆ params.nextS := by
  intro n hn
  simp [nextS, hn]

theorem mem_lowerBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.lowerBlock ↔
      params.N ≤ n ∧ n ≤ params.N + params.L ∧ (n : ZMod params.Mplus) ∈ params.G.T := by
  simp [lowerBlock, mem_residueBlockFinset]

theorem mem_privateBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.privateBlock ↔
      2 * params.N + params.Mplus - a ≤ n ∧ n ≤ params.serviceR - a ∧
        (n : ZMod params.Mplus) ∈ params.G.Pstar := by
  simp [privateBlock, mem_residueBlockFinset]

theorem mem_tailBlock {st : StageState} {a b p n : ℕ}
    {params : StageParams st a b p} :
    n ∈ params.tailBlock ↔
      params.K ≤ n ∧ n ≤ params.nextX ∧ (n : ZMod params.Mplus) ∈ params.Dplus := by
  simp [tailBlock, mem_residueBlockFinset, nextX]

theorem privateBlock_lo_gt_X {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) (ha : a ∈ st.P) (hN : st.X < params.N) :
    st.X < 2 * params.N + params.Mplus - a := by
  have haX : a ≤ st.X := st.active_le_X ha
  omega

theorem nextS_new_elements_above_old_X {st : StageState} {a b p : ℕ}
    (params : StageParams st a b p) (ha : a ∈ st.P)
    (hN : st.X < params.N) (hK : st.X < params.K) :
    ∀ n ∈ params.nextS, n ∉ st.S → st.X < n := by
  classical
  intro n hn hnotS
  simp [nextS] at hn
  rcases hn with hnS | hnLower | hnPrivate | hnTail
  · exact (hnotS hnS).elim
  · rw [mem_lowerBlock] at hnLower
    exact lt_of_lt_of_le hN hnLower.1
  · rw [mem_privateBlock] at hnPrivate
    exact lt_of_lt_of_le (params.privateBlock_lo_gt_X ha hN) hnPrivate.1
  · rw [mem_tailBlock] at hnTail
    exact lt_of_lt_of_le hK hnTail.1

end StageParams

end Erdos330Formalization
