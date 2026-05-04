import Erdos330Formalization.CRTBridge

/-!
# Affine safe-pair lemmas for Erdős Problem 330

The nonselected CRT coordinates use allowed residues of the form `x_i ≠ β_i`.
The safe-pair theorem is proved after subtracting `β`, where the allowed set
is the nonzero box.  This file packages that affine normalization.
-/

namespace Erdos330Formalization

open scoped Pointwise

def affineNormalize {ι : Type*} (p : ι → ℕ)
    (β x : ∀ i : ι, ZMod (p i)) : ∀ i : ι, ZMod (p i) :=
  fun i => x i - β i

def affineDoubleNormalize {ι : Type*} (p : ι → ℕ)
    (β x : ∀ i : ι, ZMod (p i)) : ∀ i : ι, ZMod (p i) :=
  fun i => x i - (β i + β i)

lemma affineNormalize_add {ι : Type*} (p : ι → ℕ)
    (β x y : ∀ i : ι, ZMod (p i)) :
    affineDoubleNormalize p β (x + y) = affineNormalize p β x + affineNormalize p β y := by
  funext i
  simp [affineNormalize, affineDoubleNormalize]
  ring

lemma affineNormalize_add_left {ι : Type*} (p : ι → ℕ)
    (β x : ∀ i : ι, ZMod (p i)) :
    affineNormalize p β (fun i => β i + x i) = x := by
  funext i
  simp [affineNormalize]

def shiftedNonzeroBox {ι : Type*} (p : ι → ℕ)
    (β : ∀ i : ι, ZMod (p i)) : Set (∀ i : ι, ZMod (p i)) :=
  {x | ∀ i, x i ≠ β i}

def affineLeftSafeSet {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    Set (∀ i : ι, ZMod (p i)) :=
  {x | affineNormalize p β x ∈ leftSafeSet p e data ν threshold}

def affineRightSafeSet {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    Set (∀ i : ι, ZMod (p i)) :=
  {x | affineNormalize p β x ∈ rightSafeSet p e data ν threshold}

theorem affineLeftSafeSet_subset_shiftedNonzeroBox {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    affineLeftSafeSet p β e data ν threshold ⊆ shiftedNonzeroBox p β := by
  intro x hx i hxi
  have hnonzero : affineNormalize p β x i ≠ 0 :=
    (leftSafeSet_subset_nonzeroBox p e data ν threshold hx) i
  exact hnonzero (by simp [affineNormalize, hxi])

theorem affineRightSafeSet_subset_shiftedNonzeroBox {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    affineRightSafeSet p β e data ν threshold ⊆ shiftedNonzeroBox p β := by
  intro x hx i hxi
  have hnonzero : affineNormalize p β x i ≠ 0 :=
    (rightSafeSet_subset_nonzeroBox p e data ν threshold hx) i
  exact hnonzero (by simp [affineNormalize, hxi])

theorem affineSafePair_sum_union_eq_coordinateTarget_preimage {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    ((affineLeftSafeSet p β e data true (safeLeftThreshold ι) +
        affineRightSafeSet p β e data true (safeRightThreshold ι)) ∪
      (affineLeftSafeSet p β e data false (safeLeftThreshold ι) +
        affineRightSafeSet p β e data false (safeRightThreshold ι))) =
      {z | affineDoubleNormalize p β z ∈ coordinateTarget p e} := by
  classical
  ext z
  constructor
  · intro hz
    change affineDoubleNormalize p β z ∈ coordinateTarget p e
    rcases hz with hz | hz
    · rcases hz with ⟨x, hx, y, hy, hxy⟩
      have hnorm : affineDoubleNormalize p β z =
          affineNormalize p β x + affineNormalize p β y := by
        rw [← hxy]
        exact affineNormalize_add p β x y
      rw [hnorm]
      exact safePair_sum_subset_coordinateTarget_thresholds p e data true ⟨_, hx, _, hy, rfl⟩
    · rcases hz with ⟨x, hx, y, hy, hxy⟩
      have hnorm : affineDoubleNormalize p β z =
          affineNormalize p β x + affineNormalize p β y := by
        rw [← hxy]
        exact affineNormalize_add p β x y
      rw [hnorm]
      exact safePair_sum_subset_coordinateTarget_thresholds p e data false ⟨_, hx, _, hy, rfl⟩
  · intro hz
    change affineDoubleNormalize p β z ∈ coordinateTarget p e at hz
    have hnorm_mem : affineDoubleNormalize p β z ∈
        ((leftSafeSet p e data true (safeLeftThreshold ι) +
            rightSafeSet p e data true (safeRightThreshold ι)) ∪
          (leftSafeSet p e data false (safeLeftThreshold ι) +
            rightSafeSet p e data false (safeRightThreshold ι))) := by
      rw [safePair_sum_union_eq_coordinateTarget p hp7 e data]
      exact hz
    rcases hnorm_mem with htrue | hfalse
    · rcases htrue with ⟨x, hx, y, hy, hxy⟩
      refine Or.inl ⟨fun i => β i + x i, ?_, fun i => β i + y i, ?_, ?_⟩
      · change affineNormalize p β (fun i => β i + x i) ∈
          leftSafeSet p e data true (safeLeftThreshold ι)
        rw [affineNormalize_add_left]
        exact hx
      · change affineNormalize p β (fun i => β i + y i) ∈
          rightSafeSet p e data true (safeRightThreshold ι)
        rw [affineNormalize_add_left]
        exact hy
      · funext i
        have hcoord := congrFun hxy i
        dsimp [affineDoubleNormalize] at hcoord
        simp at hcoord ⊢
        linear_combination hcoord
    · rcases hfalse with ⟨x, hx, y, hy, hxy⟩
      refine Or.inr ⟨fun i => β i + x i, ?_, fun i => β i + y i, ?_, ?_⟩
      · change affineNormalize p β (fun i => β i + x i) ∈
          leftSafeSet p e data false (safeLeftThreshold ι)
        rw [affineNormalize_add_left]
        exact hx
      · change affineNormalize p β (fun i => β i + y i) ∈
          rightSafeSet p e data false (safeRightThreshold ι)
        rw [affineNormalize_add_left]
        exact hy
      · funext i
        have hcoord := congrFun hxy i
        dsimp [affineDoubleNormalize] at hcoord
        simp at hcoord ⊢
        linear_combination hcoord

end Erdos330Formalization
