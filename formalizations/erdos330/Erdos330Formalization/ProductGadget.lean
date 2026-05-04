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

def productPrivateSlice {ι : Type*} (p0 : ℕ) (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) : Set (ProductSpace p0 p) :=
  {z | z.1 = h + h ∧ affineDoubleNormalize p β z.2 ∉ coordinateTarget p e}

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

theorem productBase_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inl hx

theorem productLeftCorrection_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productLeftCorrection p0 p β e data h u1 true ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inl hx)

theorem productRightCorrection_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productRightCorrection p0 p β e data h u1 true ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inr (Or.inl hx))

theorem productLeftCorrectionTwo_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productLeftCorrection p0 p β e data h u2 false ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inr (Or.inr (Or.inl hx)))

theorem productRightCorrectionTwo_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productRightCorrection p0 p β e data h u2 false ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inr (Or.inr (Or.inr hx)))

theorem productAllowed_add_productBase_eq_univ {ι : Type*}
    [Fintype ι] (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (hp7 : ∀ i, 7 ≤ p i)
    (α h : ZMod p0) (U : Finset (ZMod p0)) (hUcard : U.card ≤ 2)
    (β : ∀ i : ι, ZMod (p i)) :
    ((productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productBase p0 p h U β : Set (ProductSpace p0 p))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hsel := allowed_add_shiftedQRDelete_eq_univ hp0_3 hp0_23 h α U hUcard
  have hsel_mem : z.1 ∈ (Set.univ \ ({α} : Set (ZMod p0))) +
      (shiftedQRDelete p0 h U : Set (ZMod p0)) := by
    rw [hsel]
    exact Set.mem_univ z.1
  have hrest := shiftedNonzeroBox_add_self_eq_univ p hp7 β
  have hrest_mem : z.2 ∈ (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) +
      (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) := by
    rw [hrest]
    exact Set.mem_univ z.2
  rcases hsel_mem with ⟨a0, ha0, t0, ht0, h0sum⟩
  rcases hrest_mem with ⟨a', ha', t', ht', hrestsum⟩
  refine ⟨(a0, a'), ?_, (t0, t'), ?_, ?_⟩
  · exact ⟨ha0.2, ha'⟩
  · exact ⟨ht0, ht'⟩
  · ext <;> simp [h0sum, hrestsum]

theorem productAllowed_add_productT_eq_univ {ι : Type*}
    [Fintype ι] (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (hp7 : ∀ i, 7 ≤ p i)
    (α h u1 u2 : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    ((productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hbase_univ := productAllowed_add_productBase_eq_univ p p0 hp0_3 hp0_23 hp7 α h
    ({u1, u2} : Finset (ZMod p0)) (by exact Finset.card_le_two) β
  have hzbase : z ∈ (productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β :
        Set (ProductSpace p0 p)) := by
    rw [hbase_univ]
    exact Set.mem_univ z
  rcases hzbase with ⟨a, ha, t, ht, hsum⟩
  refine ⟨a, ha, t, ?_, hsum⟩
  exact productBase_subset_productT p0 p β e data h u1 u2 ht

lemma shiftedQRDelete_add_leftCorrection_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huQR : u ∈ QR p0) (hx : x ∈ shiftedQRDelete p0 h U) :
    x + (h + u) ≠ h + h := by
  intro hsum
  have hx_eq : x = h - u := by linear_combination hsum
  exact notMem_shiftedQRDelete_sub_QR hp3 h u U huQR (by simpa [hx_eq] using hx)

lemma shiftedQRDelete_add_rightCorrection_ne_tau {p0 : ℕ} [NeZero p0]
    (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huU : u ∈ U) (hx : x ∈ shiftedQRDelete p0 h U) :
    x + (h - u) ≠ h + h := by
  intro hsum
  have hx_eq : x = h + u := by linear_combination hsum
  exact notMem_shiftedQRDelete_add_deleted h u U huU (by simpa [hx_eq] using hx)

lemma leftCorrection_add_shiftedQRDelete_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huQR : u ∈ QR p0) (hx : x ∈ shiftedQRDelete p0 h U) :
    (h + u) + x ≠ h + h := by
  intro hsum
  exact shiftedQRDelete_add_leftCorrection_ne_tau hp3 h u x U huQR hx
    (by simpa [add_comm] using hsum)

lemma rightCorrection_add_shiftedQRDelete_ne_tau {p0 : ℕ} [NeZero p0]
    (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huU : u ∈ U) (hx : x ∈ shiftedQRDelete p0 h U) :
    (h - u) + x ≠ h + h := by
  intro hsum
  exact shiftedQRDelete_add_rightCorrection_ne_tau h u x U huU hx
    (by simpa [add_comm] using hsum)

lemma leftCorrection_add_leftCorrection_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u v : ZMod p0) (huQR : u ∈ QR p0) (hvQR : v ∈ QR p0) :
    (h + u) + (h + v) ≠ h + h := by
  intro hsum
  have huv : u + v = 0 := by linear_combination hsum
  exact QR_add_ne_zero hp3 huQR hvQR huv

lemma rightCorrection_add_rightCorrection_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u v : ZMod p0) (huQR : u ∈ QR p0) (hvQR : v ∈ QR p0) :
    (h - u) + (h - v) ≠ h + h := by
  intro hsum
  have huv : u + v = 0 := by linear_combination -hsum
  exact QR_add_ne_zero hp3 huQR hvQR huv

lemma leftCorrection_add_rightCorrection_ne_tau_of_ne {p0 : ℕ}
    (h u v : ZMod p0) (huv : u ≠ v) :
    (h + u) + (h - v) ≠ h + h := by
  intro hsum
  apply huv
  linear_combination hsum

lemma rightCorrection_add_leftCorrection_ne_tau_of_ne {p0 : ℕ}
    (h u v : ZMod p0) (huv : u ≠ v) :
    (h - u) + (h + v) ≠ h + h := by
  intro hsum
  apply huv
  linear_combination -hsum

theorem product_compl_private_subset_T_add_T {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (p0 : ℕ) [NeZero p0]
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0)
    (hbase_sum : ((shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) :
          Set (ZMod p0)) +
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0))) =
      Set.univ \ ({h + h} : Set (ZMod p0))) :
    Set.univ \ productPrivateSlice p0 p β e h ⊆
      (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) +
        (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) := by
  classical
  intro z hz
  by_cases hzsel : z.1 = h + h
  · have hcoord : affineDoubleNormalize p β z.2 ∈ coordinateTarget p e := by
      by_contra hnot
      exact hz.2 ⟨hzsel, hnot⟩
    have haff := affineSafePair_sum_union_eq_coordinateTarget_preimage p hp7 β e data
    have hz2mem : z.2 ∈
        ((affineLeftSafeSet p β e data true (safeLeftThreshold ι) +
            affineRightSafeSet p β e data true (safeRightThreshold ι)) ∪
          (affineLeftSafeSet p β e data false (safeLeftThreshold ι) +
            affineRightSafeSet p β e data false (safeRightThreshold ι))) := by
      rw [haff]
      exact hcoord
    rcases hz2mem with htrue | hfalse
    · rcases htrue with ⟨x, hx, y, hy, hxy⟩
      refine ⟨(h + u1, x), ?_, (h - u1, y), ?_, ?_⟩
      · exact productLeftCorrection_subset_productT p0 p β e data h u1 u2 ⟨rfl, hx⟩
      · exact productRightCorrection_subset_productT p0 p β e data h u1 u2 ⟨rfl, hy⟩
      · ext i
        · simp [hzsel]
        · exact congrFun hxy i
    · rcases hfalse with ⟨x, hx, y, hy, hxy⟩
      refine ⟨(h + u2, x), ?_, (h - u2, y), ?_, ?_⟩
      · exact productLeftCorrectionTwo_subset_productT p0 p β e data h u1 u2 ⟨rfl, hx⟩
      · exact productRightCorrectionTwo_subset_productT p0 p β e data h u1 u2 ⟨rfl, hy⟩
      · ext i
        · simp [hzsel]
        · exact congrFun hxy i
  · have hsel_mem : z.1 ∈
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0)) +
          (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0)) := by
      rw [hbase_sum]
      exact ⟨Set.mem_univ z.1, by simpa using hzsel⟩
    have hrest := shiftedNonzeroBox_add_self_eq_univ p hp7 β
    have hrest_mem : z.2 ∈ (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) +
        (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) := by
      rw [hrest]
      exact Set.mem_univ z.2
    rcases hsel_mem with ⟨x0, hx0, y0, hy0, hxy0⟩
    rcases hrest_mem with ⟨x', hx', y', hy', hxy'⟩
    refine ⟨(x0, x'), ?_, (y0, y'), ?_, ?_⟩
    · exact productBase_subset_productT p0 p β e data h u1 u2 ⟨hx0, hx'⟩
    · exact productBase_subset_productT p0 p β e data h u1 u2 ⟨hy0, hy'⟩
    · ext <;> simp [hxy0, hxy']

end Erdos330Formalization
