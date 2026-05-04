import Erdos330Formalization.Stage

/-!
# Local reservoir lemmas for Erdős Problem 330

These lemmas are the first stage-construction bridge between the finite CRT
gadget and the stored reservoir invariant.  They show how `D + T = univ`
and the two-helper reservoir multiplicity produce actual old helpers from
the finite set `S`.
-/

namespace Erdos330Formalization

open scoped Pointwise

lemma nat_eq_of_zmod_eq_of_le_lt {p X u v : ℕ}
    (huX : u ≤ X) (hvX : v ≤ X) (hXp : X < p)
    (huv : (u : ZMod p) = (v : ZMod p)) : u = v := by
  have hmod : u ≡ v [MOD p] := (ZMod.natCast_eq_natCast_iff u v p).mp huv
  exact hmod.eq_of_lt_of_lt (lt_of_le_of_lt huX hXp) (lt_of_le_of_lt hvX hXp)

lemma exists_reservoir_helper_avoiding_zmod (st : StageState)
    {Jlo p : ℕ} [NeZero p] {ρ : ZMod st.M} (hρ : ρ ∈ st.D)
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X)
    (hpX : st.X < p) (forbidden : ZMod p) :
    ∃ u : ℕ,
      u ∈ residueBlockFinset st.M ({ρ} : Finset (ZMod st.M)) Jlo (Jlo + 3 * st.M) ∧
      u ∈ st.S ∧ (u : ZMod p) ≠ forbidden := by
  obtain ⟨u, huBlock, v, hvBlock, huv_ne, huS, hvS⟩ :=
    st.reservoir_multiplicity Jlo hJlo hJhi ρ hρ
  have huX : u ≤ st.X := by
    rw [mem_residueBlockFinset] at huBlock
    exact huBlock.2.1.trans hJhi
  have hvX : v ≤ st.X := by
    rw [mem_residueBlockFinset] at hvBlock
    exact hvBlock.2.1.trans hJhi
  by_cases hu_forbid : (u : ZMod p) = forbidden
  · refine ⟨v, hvBlock, hvS, ?_⟩
    intro hv_forbid
    apply huv_ne
    exact nat_eq_of_zmod_eq_of_le_lt huX hvX hpX (hu_forbid.trans hv_forbid.symm)
  · exact ⟨u, huBlock, huS, hu_forbid⟩

theorem exists_reservoir_helper_for_gadget (st : StageState) {a : ℕ}
    (G : CRTGadget st.P st.m st.M a st.D) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ γ - (u : ZMod st.M) ∈ G.T := by
  classical
  have hγ : γ ∈ (st.D : Set (ZMod st.M)) + (G.T : Set (ZMod st.M)) := by
    rw [G.D_add_T_full]
    exact Set.mem_univ γ
  rcases hγ with ⟨ρ, hρ, t, ht, hsum⟩
  obtain ⟨u, huBlock, _v, _hvBlock, _hne, huS, _hvS⟩ :=
    st.reservoir_multiplicity st.H (le_rfl) st.reservoir_long ρ hρ
  refine ⟨u, huS, ?_⟩
  rw [mem_residueBlockFinset] at huBlock
  have huρ : (u : ZMod st.M) = ρ := by simpa using huBlock.2.2
  have hdiff : γ - (u : ZMod st.M) = t := by
    rw [huρ, ← hsum]
    ring
  rwa [hdiff]

theorem exists_reservoir_helper_for_gadget_avoiding (st : StageState) {a p : ℕ}
    [NeZero p] (G : CRTGadget st.P st.m st.M a st.D)
    (hpX : st.X < p) (forbidden : ZMod p) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ γ - (u : ZMod st.M) ∈ G.T ∧
      (u : ZMod p) ≠ forbidden := by
  classical
  have hγ : γ ∈ (st.D : Set (ZMod st.M)) + (G.T : Set (ZMod st.M)) := by
    rw [G.D_add_T_full]
    exact Set.mem_univ γ
  rcases hγ with ⟨ρ, hρ, t, ht, hsum⟩
  obtain ⟨u, huBlock, huS, hup⟩ :=
    exists_reservoir_helper_avoiding_zmod st hρ (Jlo := st.H) (le_rfl) st.reservoir_long
      hpX forbidden
  refine ⟨u, huS, ?_, hup⟩
  rw [mem_residueBlockFinset] at huBlock
  have huρ : (u : ZMod st.M) = ρ := by simpa using huBlock.2.2
  have hdiff : γ - (u : ZMod st.M) = t := by
    rw [huρ, ← hsum]
    ring
  rwa [hdiff]

end Erdos330Formalization
