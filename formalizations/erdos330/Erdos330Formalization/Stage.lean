import Erdos330Formalization.Basic
import Erdos330Formalization.ResidueBlock

/-!
# Abstract stage data for Erdős Problem 330

This file records the finite state and CRT gadget interfaces used by the
priority construction.  The hard quadratic-residue and CRT proofs can later
instantiate these interfaces without changing the global construction layer.
-/

namespace Erdos330Formalization

open scoped Pointwise

/-- A finite protected block produced when servicing an active element. -/
structure ProtectedBlockCertificate (S : Finset ℕ) (a endpoint : ℕ) where
  block : Finset ℕ
  block_subset_private :
    ∀ n ∈ block, n ∈ privateSet {x : ℕ | x ∈ S} a
  block_le_endpoint : ∀ n ∈ block, n ≤ endpoint
  densityNumerator : ℕ
  densityDenominator : ℕ
  densityDenominator_pos : 0 < densityDenominator
  block_density_lower :
    densityNumerator * endpoint ≤ densityDenominator * block.card

/--
The bounded-resource CRT gadget used by one stage of the construction.

The selected-coordinate and base-projection fields from the roadmap will be
added once the concrete CRT representation is fixed.  The fields here are the
parts already needed by the abstract coverage and privacy arguments.
-/
structure CRTGadget (P : Finset ℕ) (m : ℕ → ℕ) (M a : ℕ)
    (D : Finset (ZMod M)) where
  T : Finset (ZMod M)
  Pstar : Finset (ZMod M)
  Tbase : Finset (ZMod M)
  Tbase_subset_T : Tbase ⊆ T
  T_subset_D : T ⊆ D
  Pstar_subset_D : Pstar ⊆ D
  T_add_T_compl_private :
    ((T : Set (ZMod M)) + (T : Set (ZMod M))) =
      Set.univ \ ((fun x : ZMod M => (a : ZMod M) + x) '' (Pstar : Set (ZMod M)))
  D_add_T_full :
    ((D : Set (ZMod M)) + (T : Set (ZMod M))) = Set.univ
  Pstar_card_formula :
    (Pstar.card : ℝ) / (M : ℝ) =
      (1 : ℝ) / (m a : ℝ) *
        (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ))

/--
Finite state at one stage of the priority construction.

The state stores a full-residue reservoir and coverage up to `R`; later stage
lemmas extend this state while preserving isolation of active elements.
-/
structure StageState where
  S : Finset ℕ
  P : Finset ℕ
  m : ℕ → ℕ
  M : ℕ
  D : Finset (ZMod M)
  H : ℕ
  X : ℕ
  R : ℕ
  coverStart : ℕ
  P_subset_S : P ⊆ S
  S_le_X : ∀ s ∈ S, s ≤ X
  m_prime : ∀ a ∈ P, Nat.Prime (m a)
  m_ge23 : ∀ a ∈ P, 23 ≤ m a
  m_mod4 : ∀ a ∈ P, m a % 4 = 3
  m_pairwise_coprime :
    ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → Nat.Coprime (m a) (m b)
  M_def : M = P.prod m
  isolated :
    ∀ a ∈ P, ∀ s ∈ S, (s : ZMod (m a)) = (a : ZMod (m a)) → s = a
  reservoir_subset :
    residueBlockFinset M D H X ⊆ S
  reservoir_multiplicity :
    ∀ Jlo, H ≤ Jlo → Jlo + 3 * M ≤ X →
      ∀ ρ ∈ D,
        ∃ u ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) Jlo (Jlo + 3 * M),
        ∃ v ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) Jlo (Jlo + 3 * M),
          u ≠ v ∧ u ∈ S ∧ v ∈ S
  reservoir_long : H + 3 * M ≤ X
  headroom : H + X + 3 * M ≤ R
  coverage : ∀ n, coverStart ≤ n → n ≤ R → n ∈ twoFoldFinset S
  exists_dormant : ∃ b ∈ S, b ∉ P

namespace StageState

theorem active_mem_state (st : StageState) {a : ℕ} (ha : a ∈ st.P) : a ∈ st.S :=
  st.P_subset_S ha

theorem active_le_X (st : StageState) {a : ℕ} (ha : a ∈ st.P) : a ≤ st.X :=
  st.S_le_X a (st.active_mem_state ha)

theorem modulus_pos (st : StageState) {a : ℕ} (ha : a ∈ st.P) : 0 < st.m a :=
  (st.m_prime a ha).pos

end StageState

/-- Abstract certificate that one finite stage extends another. -/
structure StageExtension (st st' : StageState) where
  S_subset : st.S ⊆ st'.S
  P_subset : st.P ⊆ st'.P
  m_eq_on_old : ∀ a ∈ st.P, st'.m a = st.m a
  coverStart_eq : st'.coverStart = st.coverStart
  X_mono : st.X ≤ st'.X
  R_mono : st.R ≤ st'.R
  new_elements_above_old_X :
    ∀ n ∈ st'.S, n ∉ st.S → st.X < n

namespace StageExtension

theorem old_coverage {st st' : StageState} (h : StageExtension st st')
    {n : ℕ} (hn_start : st.coverStart ≤ n) (hn_R : n ≤ st.R) :
    n ∈ twoFoldFinset st'.S :=
  twoFoldFinset_mono h.S_subset (st.coverage n hn_start hn_R)

end StageExtension

/-- A stage extension that services one active element and records a protected block. -/
structure ServiceExtension (st st' : StageState) (a : ℕ) where
  toStageExtension : StageExtension st st'
  served_active : a ∈ st.P
  protectedBlock : ProtectedBlockCertificate st'.S a st'.R

end Erdos330Formalization
