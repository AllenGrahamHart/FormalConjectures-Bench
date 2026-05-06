import FormalConjecturesBench.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.Bases
import Mathlib.Topology.Ultrafilter

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

lemma clusterSet_congr_eventually
    {u v : ℕ → ℝ} (huv : u =ᶠ[Filter.atTop] v) :
    clusterSet u = clusterSet v := by
  ext y
  change ClusterPt y (Filter.map u Filter.atTop) ↔
    ClusterPt y (Filter.map v Filter.atTop)
  rw [Filter.map_congr huv]

lemma clusterSet_congr
    {u v : ℕ → ℝ} (huv : ∀ n : ℕ, u n = v n) :
    clusterSet u = clusterSet v :=
  clusterSet_congr_eventually (Filter.Eventually.of_forall huv)

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

lemma exists_center_seq_clusterSet_eq_closed_nonempty_bounded
    {A : Set ℝ} (hA_closed : IsClosed A) (hA_nonempty : A.Nonempty)
    (hA_subset : A ⊆ SpaceI) :
    ∃ c : ℝ, c ∈ A ∧ ∃ a : ℕ → ℝ,
      (∀ m, a m ∈ A) ∧
      clusterSet a = A ∧
      ∀ m, |a m - c| ≤ 2 := by
  rcases hA_nonempty with ⟨c, hcA⟩
  obtain ⟨a, ha_mem, ha_cluster⟩ :=
    exists_seq_clusterSet_eq_closed_nonempty hA_closed ⟨c, hcA⟩
  exact ⟨c, hcA, a, ha_mem, ha_cluster,
    fun m => abs_sub_le_two_of_mem_subset_spaceI hA_subset (ha_mem m) hcA⟩

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

lemma map_nat_succ_atTop :
    Filter.map Nat.succ Filter.atTop = (Filter.atTop : Filter ℕ) := by
  apply le_antisymm
  · have hsucc : StrictMono Nat.succ := fun _ _ h => Nat.succ_lt_succ h
    exact hsucc.tendsto_atTop
  · intro s hs
    rw [Filter.mem_map] at hs
    rcases Filter.eventually_atTop.mp hs with ⟨N, hN⟩
    refine Filter.eventually_atTop.mpr ⟨N.succ, ?_⟩
    intro n hn
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero N hn)
    | succ n => exact hN n (Nat.succ_le_succ_iff.mp hn)

lemma clusterSet_succ_eq (u : ℕ → ℝ) :
    clusterSet (fun n : ℕ => u n.succ) = clusterSet u := by
  ext y
  change ClusterPt y (Filter.map (fun n : ℕ => u n.succ) Filter.atTop) ↔
    ClusterPt y (Filter.map u Filter.atTop)
  have hmap :
      Filter.map (fun n : ℕ => u n.succ) Filter.atTop =
        Filter.map u Filter.atTop := by
    change Filter.map (u ∘ Nat.succ) Filter.atTop = Filter.map u Filter.atTop
    rw [← Filter.map_map, map_nat_succ_atTop]
  rw [hmap]

lemma mapClusterPt_eq_of_tendsto
    {u : ℕ → ℝ} {l : Filter ℕ} {c y : ℝ}
    (hu : Tendsto u l (nhds c))
    (hy : MapClusterPt y l u) :
    y = c := by
  rcases mapClusterPt_iff_ultrafilter.mp hy with ⟨U, hU_le, hUy⟩
  have hUc : Tendsto u (U : Filter ℕ) (nhds c) := hu.mono_left hU_le
  exact (tendsto_nhds_unique hUc hUy).symm

lemma map_strictMono_atTop_eq_atTop_inf_principal_range
    {nSeq : ℕ → ℕ} (hnSeq : StrictMono nSeq) :
    Filter.map nSeq Filter.atTop =
      Filter.atTop ⊓ Filter.principal (Set.range nSeq) := by
  apply le_antisymm
  · refine le_inf_iff.mpr ⟨hnSeq.tendsto_atTop, ?_⟩
    refine Filter.le_principal_iff.mpr ?_
    rw [Filter.mem_map]
    exact Filter.Eventually.of_forall fun m => ⟨m, rfl⟩
  · intro s hs
    rw [Filter.mem_map] at hs
    rcases Filter.eventually_atTop.mp hs with ⟨M, hM⟩
    rw [Filter.mem_inf_principal]
    refine Filter.eventually_atTop.mpr ⟨nSeq M, ?_⟩
    intro x hx hxrange
    rcases hxrange with ⟨m, rfl⟩
    exact hM m ((hnSeq.le_iff_le).mp hx)

lemma mapClusterPt_selected_range_of_strictMono
    {u : ℕ → ℝ} {nSeq : ℕ → ℕ} {y : ℝ}
    (hnSeq : StrictMono nSeq)
    (hy : MapClusterPt y
      (Filter.atTop ⊓ Filter.principal (Set.range nSeq)) u) :
    MapClusterPt y Filter.atTop (fun m : ℕ => u (nSeq m)) := by
  rw [MapClusterPt] at hy ⊢
  change ClusterPt y
    (Filter.map u (Filter.atTop ⊓ Filter.principal (Set.range nSeq))) at hy
  rw [← map_strictMono_atTop_eq_atTop_inf_principal_range hnSeq] at hy
  simpa [Function.comp_def, Filter.map_map] using hy

lemma mapClusterPt_atTop_split_principal
    {u : ℕ → ℝ} {S : Set ℕ} {y : ℝ}
    (hy : MapClusterPt y Filter.atTop u) :
    MapClusterPt y (Filter.atTop ⊓ Filter.principal S) u ∨
      MapClusterPt y (Filter.atTop ⊓ Filter.principal Sᶜ) u := by
  rcases mapClusterPt_iff_ultrafilter.mp hy with ⟨U, hU_atTop, hUy⟩
  rcases U.mem_or_compl_mem S with hUS | hUSc
  · left
    refine mapClusterPt_iff_ultrafilter.mpr ⟨U, ?_, hUy⟩
    exact le_inf_iff.mpr ⟨hU_atTop, Filter.le_principal_iff.mpr hUS⟩
  · right
    refine mapClusterPt_iff_ultrafilter.mpr ⟨U, ?_, hUy⟩
    exact le_inf_iff.mpr ⟨hU_atTop, Filter.le_principal_iff.mpr hUSc⟩

lemma clusterSet_of_selected_rows_and_complement_tendsto
    {u a : ℕ → ℝ} {nSeq : ℕ → ℕ} {A : Set ℝ} {c : ℝ}
    (hnSeq : StrictMono nSeq)
    (hselected : ∀ m : ℕ, u (nSeq m) = a m)
    (ha_cluster : clusterSet a = A)
    (hcA : c ∈ A)
    (hcomp : Tendsto u
      (Filter.atTop ⊓ Filter.principal (Set.range nSeq)ᶜ) (nhds c)) :
    clusterSet u = A := by
  apply Set.Subset.antisymm
  · intro y hy
    rcases mapClusterPt_atTop_split_principal
      (S := Set.range nSeq) (u := u) hy with hsel | hcomp_cluster
    · have hyseq :
          MapClusterPt y Filter.atTop (fun m : ℕ => u (nSeq m)) :=
        mapClusterPt_selected_range_of_strictMono hnSeq hsel
      have hya : y ∈ clusterSet a := by
        simpa [clusterSet, hselected] using hyseq
      simpa [ha_cluster] using hya
    · have hyc : y = c := mapClusterPt_eq_of_tendsto hcomp hcomp_cluster
      simpa [hyc] using hcA
  · rw [← ha_cluster]
    exact clusterSet_subset_of_selected_subsequence hnSeq.tendsto_atTop hselected

end Erdos1151Formalization

end
