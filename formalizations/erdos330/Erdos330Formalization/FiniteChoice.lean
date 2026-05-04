import Erdos330Formalization.QuadraticResidue

/-!
# Finite choice lemmas for Erdős Problem 330

These combinatorial lemmas support the safe-pairs part of the CRT gadget.
-/

namespace Erdos330Formalization

theorem exists_disjoint_subsets_card_eq {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (a b : ℕ) (hab : a + b ≤ U.card) :
    ∃ S T : Finset ι,
      S ⊆ U ∧ T ⊆ U ∧ Disjoint S T ∧ S.card = a ∧ T.card = b := by
  obtain ⟨S, hSU, hScard⟩ :=
    Finset.exists_subset_card_eq (s := U) (n := a) (by omega)
  have hbU : b ≤ (U \ S).card := by
    rw [Finset.card_sdiff_of_subset hSU, hScard]
    omega
  obtain ⟨T, hTUS, hTcard⟩ := Finset.exists_subset_card_eq (s := U \ S) (n := b) hbU
  refine ⟨S, T, hSU, ?_, ?_, hScard, hTcard⟩
  · exact fun x hx => (Finset.mem_sdiff.mp (hTUS hx)).1
  · exact Finset.disjoint_left.mpr fun x hxS hxT => (Finset.mem_sdiff.mp (hTUS hxT)).2 hxS

end Erdos330Formalization
