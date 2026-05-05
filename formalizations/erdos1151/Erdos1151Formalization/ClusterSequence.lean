import Erdos1151Formalization.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Bases

/-!
# Cluster-set sequences inside closed sets

This file proves the first reusable ingredient for the abstract diagonal
construction: every nonempty closed subset of `ℝ` admits a sequence taking
values in the set whose finite cluster set is exactly that set.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Erdos1151Formalization

lemma clusterSet_subset_of_forall_mem_closed
    {u : ℕ → ℝ} {A : Set ℝ} (hA_closed : IsClosed A)
    (huA : ∀ n, u n ∈ A) :
    clusterSet u ⊆ A := by
  intro y hy
  have hA_mem : A ∈ Filter.map u Filter.atTop := by
    rw [Filter.mem_map]
    exact Filter.Eventually.of_forall huA
  have hy_closure : y ∈ closure A := by
    exact hy.mem_closure_of_mem A hA_mem
  simpa [hA_closed.closure_eq] using hy_closure

/-- Repeat a dense sequence using the first coordinate of `Nat.unpair`. -/
def repeatedDenseSeq {A : Set ℝ} [Nonempty A] : ℕ → ℝ :=
  fun n => (TopologicalSpace.denseSeq A (Nat.unpair n).1 : A).1

lemma repeatedDenseSeq_mem {A : Set ℝ} [Nonempty A] (n : ℕ) :
    repeatedDenseSeq (A := A) n ∈ A :=
  (TopologicalSpace.denseSeq A (Nat.unpair n).1 : A).2

lemma subset_clusterSet_repeatedDenseSeq
    {A : Set ℝ} [Nonempty A] :
    A ⊆ clusterSet (repeatedDenseSeq (A := A)) := by
  intro y hy
  change MapClusterPt y Filter.atTop (repeatedDenseSeq (A := A))
  rw [mapClusterPt_iff_frequently]
  intro s hs
  rw [Filter.frequently_atTop]
  intro N
  rcases mem_nhds_iff.mp hs with ⟨t, hts, ht_open, hyt⟩
  let tA : Set A := {x | (x : ℝ) ∈ t}
  have htA_open : IsOpen tA := by
    exact ht_open.preimage continuous_subtype_val
  have htA_nonempty : tA.Nonempty := ⟨⟨y, hy⟩, hyt⟩
  obtain ⟨i, hi⟩ :=
    (TopologicalSpace.denseRange_denseSeq A).exists_mem_open htA_open htA_nonempty
  refine ⟨Nat.pair i N, Nat.right_le_pair i N, ?_⟩
  have hunpair : Nat.unpair (Nat.pair i N) = (i, N) := Nat.unpair_pair i N
  exact hts (by simpa [repeatedDenseSeq, hunpair, tA] using hi)

lemma clusterSet_repeatedDenseSeq_eq_closed
    {A : Set ℝ} [Nonempty A] (hA_closed : IsClosed A) :
    clusterSet (repeatedDenseSeq (A := A)) = A := by
  apply Set.Subset.antisymm
  · exact clusterSet_subset_of_forall_mem_closed hA_closed (repeatedDenseSeq_mem (A := A))
  · exact subset_clusterSet_repeatedDenseSeq (A := A)

lemma exists_seq_clusterSet_eq_closed_nonempty
    {A : Set ℝ} (hA_closed : IsClosed A) (hA_nonempty : A.Nonempty) :
    ∃ a : ℕ → ℝ,
      (∀ m, a m ∈ A) ∧ clusterSet a = A := by
  classical
  letI : Nonempty A := hA_nonempty.to_subtype
  exact ⟨repeatedDenseSeq (A := A), repeatedDenseSeq_mem (A := A),
    clusterSet_repeatedDenseSeq_eq_closed (A := A) hA_closed⟩

lemma abs_sub_le_two_of_mem_spaceI {x y : ℝ}
    (hx : x ∈ SpaceI) (hy : y ∈ SpaceI) :
    |x - y| ≤ 2 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma abs_sub_le_two_of_mem_subset_spaceI
    {A : Set ℝ} (hA_subset : A ⊆ SpaceI) {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ A) :
    |x - y| ≤ 2 :=
  abs_sub_le_two_of_mem_spaceI (hA_subset hx) (hA_subset hy)

lemma mapClusterPt_of_comp_tendsto_atTop
    {u : ℕ → ℝ} {v : ℕ → ℕ} {y : ℝ}
    (hv : Tendsto v Filter.atTop Filter.atTop)
    (hy : MapClusterPt y Filter.atTop (fun n : ℕ => u (v n))) :
    MapClusterPt y Filter.atTop u := by
  rw [MapClusterPt] at hy ⊢
  change ClusterPt y (Filter.map (u ∘ v) Filter.atTop) at hy
  rw [← Filter.map_map] at hy
  exact hy.mono (Filter.map_mono hv)

lemma clusterSet_comp_subset
    {u : ℕ → ℝ} {v : ℕ → ℕ}
    (hv : Tendsto v Filter.atTop Filter.atTop) :
    clusterSet (fun n : ℕ => u (v n)) ⊆ clusterSet u := by
  intro y hy
  exact mapClusterPt_of_comp_tendsto_atTop hv hy

lemma clusterSet_subset_of_selected_subsequence
    {u a : ℕ → ℝ} {nSeq : ℕ → ℕ}
    (hnSeq : Tendsto nSeq Filter.atTop Filter.atTop)
    (hselected : ∀ m : ℕ, u (nSeq m) = a m) :
    clusterSet a ⊆ clusterSet u := by
  intro y hy
  have hycomp : MapClusterPt y Filter.atTop (fun m : ℕ => u (nSeq m)) := by
    simpa [clusterSet, hselected] using hy
  exact mapClusterPt_of_comp_tendsto_atTop hnSeq hycomp

lemma clusterSet_subset_singleton_of_tendsto
    {u : ℕ → ℝ} {c : ℝ}
    (hu : Tendsto u Filter.atTop (nhds c)) :
    clusterSet u ⊆ {c} := by
  intro y hy
  change MapClusterPt y Filter.atTop u at hy
  rcases mapClusterPt_iff_ultrafilter.mp hy with ⟨U, hU_le, hUy⟩
  have hUc : Tendsto u (U : Filter ℕ) (nhds c) := hu.mono_left hU_le
  exact (tendsto_nhds_unique hUc hUy).symm

lemma clusterSet_subset_of_tendsto_mem
    {u : ℕ → ℝ} {A : Set ℝ} {c : ℝ}
    (hcA : c ∈ A) (hu : Tendsto u Filter.atTop (nhds c)) :
    clusterSet u ⊆ A := by
  intro y hy
  have hyc : y ∈ ({c} : Set ℝ) := clusterSet_subset_singleton_of_tendsto hu hy
  simpa using hyc ▸ hcA

end Erdos1151Formalization

end
