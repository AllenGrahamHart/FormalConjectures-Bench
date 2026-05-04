import Mathlib.Data.ZMod.QuotientRing
import Erdos330Formalization.SafePairs

/-!
# CRT bridge lemmas for Erdős Problem 330

This file records the thin interface needed to pull product-coordinate sumset
identities back through the Chinese remainder equivalence.
-/

namespace Erdos330Formalization

open scoped Pointwise

theorem addEquiv_preimage_add {α β : Type*} [Add α] [Add β]
    (φ : α ≃+ β) (A B : Set β) :
    {x | φ x ∈ A + B} = {x | φ x ∈ A} + {x | φ x ∈ B} := by
  ext z
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨φ.symm a, ?_, φ.symm b, ?_, ?_⟩
    · simpa using ha
    · simpa using hb
    · apply φ.injective
      have hab' : a + b = φ z := by simpa using hab
      calc
        φ (φ.symm a + φ.symm b) = a + b := by simp [φ.map_add]
        _ = φ z := hab'
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨φ x, hx, φ y, hy, ?_⟩
    have hxy' : x + y = z := by simpa using hxy
    calc
      φ x + φ y = φ (x + y) := (φ.map_add x y).symm
      _ = φ z := by rw [hxy']

noncomputable def addEquivPreimageFinset {α β : Type*} [Fintype α] [Add α] [Add β]
    (φ : α ≃+ β) (S : Set β) : Finset α := by
  classical
  exact Finset.univ.filter fun x => φ x ∈ S

noncomputable def addEquivTranslatePreimageFinset {α β : Type*} [Fintype α]
    [Add α] [Add β] (a : α) (φ : α ≃+ β) (S : Set β) : Finset α := by
  classical
  exact Finset.univ.filter fun x => φ (a + x) ∈ S

theorem coe_addEquivPreimageFinset {α β : Type*} [Fintype α] [Add α] [Add β]
    (φ : α ≃+ β) (S : Set β) :
    (addEquivPreimageFinset φ S : Set α) = {x | φ x ∈ S} := by
  classical
  ext x
  simp [addEquivPreimageFinset]

theorem coe_addEquivTranslatePreimageFinset {α β : Type*} [Fintype α]
    [Add α] [Add β] (a : α) (φ : α ≃+ β) (S : Set β) :
    (addEquivTranslatePreimageFinset a φ S : Set α) = {x | φ (a + x) ∈ S} := by
  classical
  ext x
  simp [addEquivTranslatePreimageFinset]

theorem addEquiv_preimage_add_eq_compl {α β : Type*} [Add α] [Add β]
    (φ : α ≃+ β) (A B P : Set β) (hAB : A + B = Set.univ \ P) :
    {x | φ x ∈ A} + {x | φ x ∈ B} = Set.univ \ {x | φ x ∈ P} := by
  rw [← addEquiv_preimage_add φ A B, hAB]
  ext x
  simp

theorem addEquiv_preimage_add_eq_univ {α β : Type*} [Add α] [Add β]
    (φ : α ≃+ β) (A B : Set β) (hAB : A + B = Set.univ) :
    {x | φ x ∈ A} + {x | φ x ∈ B} = Set.univ := by
  rw [← addEquiv_preimage_add φ A B, hAB]
  ext x
  simp

theorem addEquiv_translate_image_preimage {α β : Type*}
    [AddGroup α] [Add β] (φ : α ≃+ β) (a : α) (P : Set β) :
    ((fun x : α => a + x) '' {x | φ (a + x) ∈ P}) = {x | φ x ∈ P} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    refine ⟨-a + z, ?_, ?_⟩
    · change φ (a + (-a + z)) ∈ P
      have hsum : a + (-a + z) = z := by simp
      rwa [hsum]
    · simp

theorem addEquiv_preimage_add_translate_eq_compl_image {α β : Type*}
    [AddGroup α] [Add β] (φ : α ≃+ β) (a : α) (A B P : Set β)
    (hAB : A + B = Set.univ \ P) :
    {x | φ x ∈ A} + {x | φ x ∈ B} =
      Set.univ \ ((fun x : α => a + x) '' {x | φ (a + x) ∈ P}) := by
  rw [addEquiv_translate_image_preimage φ a P]
  exact addEquiv_preimage_add_eq_compl φ A B P hAB

theorem addEquivPreimageFinset_add_eq_compl_translate_image {α β : Type*}
    [Fintype α] [AddGroup α] [Add β]
    (φ : α ≃+ β) (a : α) (A B P : Set β) (hAB : A + B = Set.univ \ P) :
    ((addEquivPreimageFinset φ A : Set α) + (addEquivPreimageFinset φ B : Set α)) =
      Set.univ \ ((fun x : α => a + x) ''
        (addEquivTranslatePreimageFinset a φ P : Set α)) := by
  rw [coe_addEquivPreimageFinset, coe_addEquivPreimageFinset,
    coe_addEquivTranslatePreimageFinset]
  exact addEquiv_preimage_add_translate_eq_compl_image φ a A B P hAB

theorem addEquivPreimageFinset_add_eq_univ {α β : Type*}
    [Fintype α] [Add α] [Add β]
    (φ : α ≃+ β) (A B : Set β) (hAB : A + B = Set.univ) :
    ((addEquivPreimageFinset φ A : Set α) + (addEquivPreimageFinset φ B : Set α)) =
      Set.univ := by
  rw [coe_addEquivPreimageFinset, coe_addEquivPreimageFinset]
  exact addEquiv_preimage_add_eq_univ φ A B hAB

theorem addEquivPreimageFinset_subset {α β : Type*} [Fintype α] [Add α] [Add β]
    {φ : α ≃+ β} {A B : Set β} (hAB : A ⊆ B) :
    addEquivPreimageFinset φ A ⊆ addEquivPreimageFinset φ B := by
  classical
  intro x hx
  simp [addEquivPreimageFinset] at hx ⊢
  exact hAB hx

noncomputable def zmodProdEquivPi {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hcoprime : Pairwise fun i j => Nat.Coprime (m i) (m j)) :
    ZMod (∏ i, m i) ≃+* ∀ i, ZMod (m i) :=
  ZMod.prodEquivPi m hcoprime

theorem crt_safePair_sum_union_eq_coordinateTarget_preimage {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (hcoprime : Pairwise fun i j => Nat.Coprime (p i) (p j))
    (e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    let φ : ZMod (∏ i, p i) ≃+ ∀ i, ZMod (p i) :=
      (zmodProdEquivPi p hcoprime).toAddEquiv
    (({x | φ x ∈ leftSafeSet p e data true (safeLeftThreshold ι)} +
        {x | φ x ∈ rightSafeSet p e data true (safeRightThreshold ι)}) ∪
      ({x | φ x ∈ leftSafeSet p e data false (safeLeftThreshold ι)} +
        {x | φ x ∈ rightSafeSet p e data false (safeRightThreshold ι)})) =
      {x | φ x ∈ coordinateTarget p e} := by
  intro φ
  rw [← addEquiv_preimage_add φ, ← addEquiv_preimage_add φ]
  ext x
  change (φ x ∈ leftSafeSet p e data true (safeLeftThreshold ι) +
        rightSafeSet p e data true (safeRightThreshold ι) ∨
      φ x ∈ leftSafeSet p e data false (safeLeftThreshold ι) +
        rightSafeSet p e data false (safeRightThreshold ι)) ↔
    φ x ∈ coordinateTarget p e
  rw [← Set.mem_union]
  rw [safePair_sum_union_eq_coordinateTarget p hp7 e data]

end Erdos330Formalization
