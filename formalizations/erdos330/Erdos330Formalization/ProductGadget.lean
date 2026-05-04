import Erdos330Formalization.AffineSafePairs

/-!
# Product-coordinate CRT gadget pieces for Erdős Problem 330

This file defines the product-coordinate version of the finite CRT gadget and
proves the first structural inclusion: the constructed set `T` lies inside the
allowed box.
-/

namespace Erdos330Formalization

open scoped Pointwise

abbrev ProductSpace {ι : Type*} (p0 : ℕ) (p : ι → ℕ) :=
  ZMod p0 × (∀ i : ι, ZMod (p i))

def productAllowed {ι : Type*} (p0 : ℕ) (p : ι → ℕ)
    (α : ZMod p0) (β : ∀ i : ι, ZMod (p i)) : Set (ProductSpace p0 p) :=
  {x | x.1 ≠ α ∧ x.2 ∈ shiftedNonzeroBox p β}

def productBase {ι : Type*} (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (h : ZMod p0) (U : Finset (ZMod p0)) (β : ∀ i : ι, ZMod (p i)) :
    Set (ProductSpace p0 p) :=
  {x | x.1 ∈ shiftedQRDelete p0 h U ∧ x.2 ∈ shiftedNonzeroBox p β}

def productLeftCorrection {ι : Type*} [Fintype ι] (p0 : ℕ) (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u : ZMod p0) (ν : Bool) : Set (ProductSpace p0 p) :=
  {x | x.1 = h + u ∧ x.2 ∈ affineLeftSafeSet p β e data ν (safeLeftThreshold ι)}

def productRightCorrection {ι : Type*} [Fintype ι] (p0 : ℕ) (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u : ZMod p0) (ν : Bool) : Set (ProductSpace p0 p) :=
  {x | x.1 = h - u ∧ x.2 ∈ affineRightSafeSet p β e data ν (safeRightThreshold ι)}

def productT {ι : Type*} [Fintype ι] (p0 : ℕ) [NeZero p0]
    (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) : Set (ProductSpace p0 p) :=
  productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β ∪
    (productLeftCorrection p0 p β e data h u1 true ∪
      (productRightCorrection p0 p β e data h u1 true ∪
        (productLeftCorrection p0 p β e data h u2 false ∪
          productRightCorrection p0 p β e data h u2 false)))

theorem productBase_subset_allowed {ι : Type*} (p0 : ℕ) [NeZero p0]
    (p : ι → ℕ) (α h : ZMod p0) (U : Finset (ZMod p0))
    (β : ∀ i : ι, ZMod (p i))
    (hQavoid : ∀ q ∈ shiftedQRDelete p0 h U, q ≠ α) :
    productBase p0 p h U β ⊆ productAllowed p0 p α β := by
  intro x hx
  exact ⟨hQavoid x.1 hx.1, hx.2⟩

lemma add_deleted_residue_ne_forbidden {p0 : ℕ} (α h u : ZMod p0)
    (hu : u ≠ α - h) : h + u ≠ α := by
  intro hhu
  apply hu
  linear_combination hhu

lemma sub_deleted_residue_ne_forbidden {p0 : ℕ} (α h u : ZMod p0)
    (hu : u ≠ -(α - h)) : h - u ≠ α := by
  intro hhu
  apply hu
  linear_combination -hhu

theorem productLeftCorrection_subset_allowed {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ) (α h u : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (ν : Bool) (hu : u ≠ α - h) :
    productLeftCorrection p0 p β e data h u ν ⊆ productAllowed p0 p α β := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hx.1]
    exact add_deleted_residue_ne_forbidden α h u hu
  · exact affineLeftSafeSet_subset_shiftedNonzeroBox p β e data ν (safeLeftThreshold ι) hx.2

theorem productRightCorrection_subset_allowed {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ) (α h u : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (ν : Bool) (hu : u ≠ -(α - h)) :
    productRightCorrection p0 p β e data h u ν ⊆ productAllowed p0 p α β := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hx.1]
    exact sub_deleted_residue_ne_forbidden α h u hu
  · exact affineRightSafeSet_subset_shiftedNonzeroBox p β e data ν (safeRightThreshold ι) hx.2

theorem productT_subset_allowed {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ) (α h u1 u2 : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (hu1_pos : u1 ≠ α - h) (hu2_pos : u2 ≠ α - h)
    (hu1_neg : u1 ≠ -(α - h)) (hu2_neg : u2 ≠ -(α - h))
    (hQavoid : ∀ q ∈ shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)), q ≠ α) :
    productT p0 p β e data h u1 u2 ⊆ productAllowed p0 p α β := by
  intro x hx
  rcases hx with hbase | hrest
  · exact productBase_subset_allowed p0 p α h ({u1, u2} : Finset (ZMod p0)) β hQavoid
      hbase
  rcases hrest with hleft1 | hrest
  · exact productLeftCorrection_subset_allowed p0 p α h u1 β e data true hu1_pos hleft1
  rcases hrest with hright1 | hrest
  · exact productRightCorrection_subset_allowed p0 p α h u1 β e data true hu1_neg hright1
  rcases hrest with hleft2 | hright2
  · exact productLeftCorrection_subset_allowed p0 p α h u2 β e data false hu2_pos hleft2
  · exact productRightCorrection_subset_allowed p0 p α h u2 β e data false hu2_neg hright2

end Erdos330Formalization
