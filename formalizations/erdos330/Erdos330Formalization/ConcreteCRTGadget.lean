import Erdos330Formalization.ProductGadget
import Erdos330Formalization.Stage

/-!
# Concrete CRT gadget wrapper for Erdős Problem 330

This file connects the product-coordinate gadget to the abstract `CRTGadget`
interface used by the stage construction.  The finite set equations and subset
fields are supplied by `ProductGadget`; the remaining input is the cardinality
formula for the translated private slice.
-/

namespace Erdos330Formalization

open scoped Pointwise

abbrev NonselectedIndex (P : Finset ℕ) (a : ℕ) := {b // b ∈ P.erase a}

theorem exists_crtProduct_CRTGadget_of_card_formula {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (m : ℕ → ℕ) (M a : ℕ)
    (p0 : ℕ) [NeZero M] [Fact p0.Prime] [NeZero p0]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (ha1 : (φ (a : ZMod M)).1 = α)
    (he : e = affineNormalize p β (φ (a : ZMod M)).2)
    (hcard : ∀ h : ZMod p0,
      ((crtProductPstarFinset M p0 p φ (a : ZMod M) β e h).card : ℝ) / (M : ℝ) =
        (1 : ℝ) / (m a : ℝ) *
          (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ))) :
    ∃ h u1 u2 : ZMod p0,
      ∃ G : CRTGadget P m M a (crtProductAllowedFinset M p0 p φ α β),
        G.T = crtProductTFinset M p0 p φ β e data h u1 u2 ∧
        G.Pstar = crtProductPstarFinset M p0 p φ (a : ZMod M) β e h ∧
        G.Tbase = crtProductTbaseFinset M p0 p φ β h u1 u2 := by
  obtain ⟨h, u1, u2, hbase_sub, hT_sub, hP_sub, hTT, hDT⟩ :=
    exists_crtProduct_gadget_core M p0 p hp7 hp0_3 hp0_23 φ (a : ZMod M) α β e data
      ha1 he
  refine ⟨h, u1, u2, ?_⟩
  refine ⟨{
    T := crtProductTFinset M p0 p φ β e data h u1 u2
    Pstar := crtProductPstarFinset M p0 p φ (a : ZMod M) β e h
    Tbase := crtProductTbaseFinset M p0 p φ β h u1 u2
    Tbase_subset_T := hbase_sub
    T_subset_D := hT_sub
    Pstar_subset_D := hP_sub
    T_add_T_compl_private := hTT
    D_add_T_full := hDT
    Pstar_card_formula := hcard h
  }, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

theorem exists_crtProduct_CRTGadget_of_subtype_product_index
    (P : Finset ℕ) (m : ℕ → ℕ) (M a : ℕ)
    [NeZero M] [Fact (Nat.Prime (m a))] [NeZero (m a)]
    [(i : NonselectedIndex P a) → Fact (Nat.Prime (m (i : ℕ)))]
    [(i : NonselectedIndex P a) → Fintype (ZMod (m (i : ℕ)))]
    (hma23 : 23 ≤ m a) (hma3 : m a % 4 = 3)
    (hm_ge7 : ∀ i : NonselectedIndex P a, 7 ≤ m (i : ℕ))
    (hm_pos : ∀ i : NonselectedIndex P a, 0 < m (i : ℕ))
    (hM : M = m a * ∏ i : NonselectedIndex P a, m (i : ℕ))
    (φ : ZMod M ≃+ ProductSpace (m a) (fun i : NonselectedIndex P a => m (i : ℕ)))
    (α : ZMod (m a))
    (β e : ∀ i : NonselectedIndex P a, ZMod (m (i : ℕ)))
    (data : ∀ i : NonselectedIndex P a, SafePairData (ZMod (m (i : ℕ))) (e i))
    (ha1 : (φ (a : ZMod M)).1 = α)
    (he : e = affineNormalize (fun i : NonselectedIndex P a => m (i : ℕ)) β
      (φ (a : ZMod M)).2) :
    ∃ h u1 u2 : ZMod (m a),
      ∃ G : CRTGadget P m M a
          (crtProductAllowedFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
            φ α β),
        G.T = crtProductTFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          φ β e data h u1 u2 ∧
        G.Pstar = crtProductPstarFinset M (m a)
          (fun i : NonselectedIndex P a => m (i : ℕ)) φ (a : ZMod M) β e h ∧
        G.Tbase = crtProductTbaseFinset M (m a)
          (fun i : NonselectedIndex P a => m (i : ℕ)) φ β h u1 u2 := by
  refine exists_crtProduct_CRTGadget_of_card_formula P m M a (m a)
    (fun i : NonselectedIndex P a => m (i : ℕ)) hm_ge7 hma3 hma23 φ α β e data ha1 he ?_
  intro h
  calc
    ((crtProductPstarFinset M (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          φ (a : ZMod M) β e h).card : ℝ) / (M : ℝ) =
        (1 : ℝ) / (m a : ℝ) *
          ∏ i : NonselectedIndex P a, (1 - (1 : ℝ) / (m (i : ℕ) : ℝ)) := by
      exact crtProductPstarFinset_card_real_formula M (m a)
        (fun i : NonselectedIndex P a => m (i : ℕ)) φ (a : ZMod M) β e h
        (show 0 < m a from (Fact.out : Nat.Prime (m a)).pos) hm_pos hM
    _ = (1 : ℝ) / (m a : ℝ) *
          (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ)) := by
      congr 1
      rw [← Finset.prod_subtype (s := P.erase a) (p := fun b => b ∈ P.erase a)
        (f := fun b => 1 - (1 : ℝ) / (m b : ℝ))]
      intro b
      rfl

theorem exists_crtProduct_CRTGadget_for_exact_product
    (P : Finset ℕ) (m : ℕ → ℕ) (a : ℕ)
    [Fact (Nat.Prime (m a))] [NeZero (m a)]
    [NeZero (m a * ∏ i : NonselectedIndex P a, m (i : ℕ))]
    [(i : NonselectedIndex P a) → Fact (Nat.Prime (m (i : ℕ)))]
    [(i : NonselectedIndex P a) → Fintype (ZMod (m (i : ℕ)))]
    (hma23 : 23 ≤ m a) (hma3 : m a % 4 = 3)
    (hm_ge7 : ∀ i : NonselectedIndex P a, 7 ≤ m (i : ℕ))
    (hcop0 : Nat.Coprime (m a) (∏ i : NonselectedIndex P a, m (i : ℕ)))
    (hcop : Pairwise fun i j : NonselectedIndex P a => Nat.Coprime (m (i : ℕ)) (m (j : ℕ))) :
    ∃ h u1 u2 : ZMod (m a),
      ∃ G : CRTGadget P m (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) a
          (crtProductAllowedFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) (m a)
            (fun i : NonselectedIndex P a => m (i : ℕ))
            (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
            (a : ZMod (m a))
            (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))),
        G.T = crtProductTFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) (m a)
          (fun i : NonselectedIndex P a => m (i : ℕ))
          (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
          (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))
          (fun i : NonselectedIndex P a => (a : ZMod (m (i : ℕ))) -
            ((i : ℕ) : ZMod (m (i : ℕ))))
          (fun i : NonselectedIndex P a =>
            safePairDataZMod (m (i : ℕ)) (hm_ge7 i)
              ((a : ZMod (m (i : ℕ))) - ((i : ℕ) : ZMod (m (i : ℕ)))))
          h u1 u2 ∧
        G.Pstar = crtProductPstarFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ))
          (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
          (a : ZMod (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)))
          (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))
          (fun i : NonselectedIndex P a => (a : ZMod (m (i : ℕ))) -
            ((i : ℕ) : ZMod (m (i : ℕ)))) h ∧
        G.Tbase = crtProductTbaseFinset (m a * ∏ i : NonselectedIndex P a, m (i : ℕ))
          (m a) (fun i : NonselectedIndex P a => m (i : ℕ))
          (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
          (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ)))) h u1 u2 := by
  refine exists_crtProduct_CRTGadget_of_subtype_product_index P m
    (m a * ∏ i : NonselectedIndex P a, m (i : ℕ)) a hma23 hma3 hm_ge7 ?_ rfl
    (productCRTAddEquiv (m a) (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop)
    (a : ZMod (m a))
    (fun i : NonselectedIndex P a => ((i : ℕ) : ZMod (m (i : ℕ))))
    (fun i : NonselectedIndex P a => (a : ZMod (m (i : ℕ))) -
      ((i : ℕ) : ZMod (m (i : ℕ))))
    (fun i : NonselectedIndex P a =>
      safePairDataZMod (m (i : ℕ)) (hm_ge7 i)
        ((a : ZMod (m (i : ℕ))) - ((i : ℕ) : ZMod (m (i : ℕ))))) ?_ ?_
  · intro i
    have h7 := hm_ge7 i
    omega
  · exact productCRTAddEquiv_fst_natCast (m a)
      (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop a
  · funext i
    dsimp [affineNormalize]
    have hsnd := productCRTAddEquiv_snd_natCast (m a)
      (fun i : NonselectedIndex P a => m (i : ℕ)) hcop0 hcop a i
    simpa using hsnd.symm

theorem prod_eq_selected_mul_nonselected (P : Finset ℕ) (m : ℕ → ℕ) {a : ℕ}
    (ha : a ∈ P) :
    P.prod m = m a * ∏ i : NonselectedIndex P a, m (i : ℕ) := by
  classical
  rw [← Finset.mul_prod_erase _ _ ha]
  congr 1
  rw [← Finset.prod_subtype (s := P.erase a) (p := fun b => b ∈ P.erase a) (f := m)]
  intro b
  rfl

lemma stage_M_eq_selected_mul_nonselected (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    st.M = st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ) := by
  rw [st.M_def, prod_eq_selected_mul_nonselected st.P st.m ha]

lemma stage_selected_coprime_nonselected_prod (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    Nat.Coprime (st.m a) (∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) := by
  classical
  rw [Nat.coprime_fintype_prod_right_iff]
  intro i
  rcases Finset.mem_erase.mp i.property with ⟨hia, hiP⟩
  exact st.m_pairwise_coprime ha hiP hia.symm

lemma stage_pairwise_coprime_nonselected (st : StageState) {a : ℕ} :
    Pairwise fun i j : NonselectedIndex st.P a =>
      Nat.Coprime (st.m (i : ℕ)) (st.m (j : ℕ)) := by
  intro i j hij
  rcases Finset.mem_erase.mp i.property with ⟨_hia, hiP⟩
  rcases Finset.mem_erase.mp j.property with ⟨_hja, hjP⟩
  exact st.m_pairwise_coprime hiP hjP (fun hijNat => hij (Subtype.ext hijNat))

lemma stage_nonselected_product_pos (st : StageState) {a : ℕ} :
    0 < ∏ i : NonselectedIndex st.P a, st.m (i : ℕ) := by
  classical
  exact Finset.prod_pos fun i _hi =>
    st.modulus_pos ((Finset.mem_erase.mp i.property).2)

lemma stage_exact_product_pos (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    0 < st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ) := by
  exact Nat.mul_pos (st.modulus_pos ha) (stage_nonselected_product_pos st)

theorem exists_stage_exact_product_CRTGadget (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    ∃ D : Finset (ZMod (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ))),
      Nonempty (CRTGadget st.P st.m
        (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) a D) := by
  classical
  letI : Fact (Nat.Prime (st.m a)) := ⟨st.m_prime a ha⟩
  letI : NeZero (st.m a) := NeZero.of_pos (st.modulus_pos ha)
  letI : NeZero (st.m a * ∏ i : NonselectedIndex st.P a, st.m (i : ℕ)) :=
    NeZero.of_pos (stage_exact_product_pos st ha)
  letI : (i : NonselectedIndex st.P a) → Fact (Nat.Prime (st.m (i : ℕ))) := fun i =>
    ⟨st.m_prime (i : ℕ) ((Finset.mem_erase.mp i.property).2)⟩
  letI : (i : NonselectedIndex st.P a) → NeZero (st.m (i : ℕ)) := fun i =>
    NeZero.of_pos (st.modulus_pos ((Finset.mem_erase.mp i.property).2))
  letI : (i : NonselectedIndex st.P a) → Fintype (ZMod (st.m (i : ℕ))) := fun _ =>
    inferInstance
  obtain ⟨_, _, _, G, _⟩ :=
    exists_crtProduct_CRTGadget_for_exact_product st.P st.m a
      (st.m_ge23 a ha) (st.m_mod4 a ha)
      (fun i => by
        have h23 := st.m_ge23 (i : ℕ) ((Finset.mem_erase.mp i.property).2)
        omega)
      (stage_selected_coprime_nonselected_prod st ha)
      (stage_pairwise_coprime_nonselected st (a := a))
  exact ⟨_, ⟨G⟩⟩

theorem exists_stage_CRTGadget (st : StageState) {a : ℕ} (ha : a ∈ st.P) :
    ∃ D : Finset (ZMod st.M), Nonempty (CRTGadget st.P st.m st.M a D) := by
  rw [stage_M_eq_selected_mul_nonselected st ha]
  exact exists_stage_exact_product_CRTGadget st ha

end Erdos330Formalization
