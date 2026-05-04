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

end Erdos330Formalization
