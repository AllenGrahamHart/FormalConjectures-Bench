import FormalConjectures.Util.ProblemImports

/-!
# Residue blocks for Erdős Problem 330

The stage construction repeatedly adds long intervals restricted to a finite
set of residue classes modulo a modulus `M`.
-/

namespace Erdos330Formalization

/--
The natural numbers in `[lo, hi]` whose residue modulo `M` belongs to `Ω`.
For `M = 0`, `ZMod M` is still a Lean type; stage lemmas should carry
separate positivity hypotheses when they need genuine modular arithmetic.
-/
def residueBlock (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) : Set ℕ :=
  {n | lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω}

/-- A residue block parameterized by its lower endpoint and length. -/
def residueBlockLen (M : ℕ) (Ω : Finset (ZMod M)) (lo len : ℕ) : Set ℕ :=
  residueBlock M Ω lo (lo + len)

/-- Finite version of `residueBlock`, used for cardinality estimates. -/
def residueBlockFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter fun n => (n : ZMod M) ∈ Ω

/-- Finite version of `residueBlockLen`. -/
def residueBlockLenFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo len : ℕ) : Finset ℕ :=
  residueBlockFinset M Ω lo (lo + len)

theorem mem_residueBlock {M : ℕ} {Ω : Finset (ZMod M)} {lo hi n : ℕ} :
    n ∈ residueBlock M Ω lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω := by
  rfl

theorem mem_residueBlockLen {M : ℕ} {Ω : Finset (ZMod M)} {lo len n : ℕ} :
    n ∈ residueBlockLen M Ω lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ (n : ZMod M) ∈ Ω := by
  rfl

theorem mem_residueBlockFinset {M : ℕ} {Ω : Finset (ZMod M)} {lo hi n : ℕ} :
    n ∈ residueBlockFinset M Ω lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω := by
  simp only [residueBlockFinset, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem mem_residueBlockLenFinset {M : ℕ} {Ω : Finset (ZMod M)} {lo len n : ℕ} :
    n ∈ residueBlockLenFinset M Ω lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ (n : ZMod M) ∈ Ω := by
  simp only [residueBlockLenFinset, mem_residueBlockFinset]

theorem mem_residueBlockFinset_singleton {M : ℕ} [NeZero M] {ρ : ZMod M}
    {lo hi n : ℕ} :
    n ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) lo hi ↔
      lo ≤ n ∧ n ≤ hi ∧ n ≡ ρ.val [MOD M] := by
  rw [mem_residueBlockFinset]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hlo, hhi, heq⟩
    have hcast : (n : ZMod M) = (ρ.val : ZMod M) := by
      simpa [ZMod.natCast_zmod_val ρ] using heq
    exact ⟨hlo, hhi, (ZMod.natCast_eq_natCast_iff n ρ.val M).mp hcast⟩
  · rintro ⟨hlo, hhi, hmod⟩
    have hcast : (n : ZMod M) = (ρ.val : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff n ρ.val M).mpr hmod
    exact ⟨hlo, hhi, by simpa [ZMod.natCast_zmod_val ρ] using hcast⟩

theorem mem_residueBlockLenFinset_singleton {M : ℕ} [NeZero M] {ρ : ZMod M}
    {lo len n : ℕ} :
    n ∈ residueBlockLenFinset M ({ρ} : Finset (ZMod M)) lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ n ≡ ρ.val [MOD M] := by
  simp only [residueBlockLenFinset, mem_residueBlockFinset_singleton]

theorem coe_residueBlockFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) :
    (residueBlockFinset M Ω lo hi : Set ℕ) = residueBlock M Ω lo hi := by
  ext n
  simp [mem_residueBlockFinset, residueBlock]

theorem coe_residueBlockLenFinset (M : ℕ) (Ω : Finset (ZMod M)) (lo len : ℕ) :
    (residueBlockLenFinset M Ω lo len : Set ℕ) = residueBlockLen M Ω lo len := by
  ext n
  simp [mem_residueBlockLenFinset, residueBlockLen, residueBlock]

theorem residueBlock_subset_Icc {M : ℕ} {Ω : Finset (ZMod M)} {lo hi : ℕ} :
    residueBlock M Ω lo hi ⊆ Set.Icc lo hi := by
  intro n hn
  exact ⟨hn.1, hn.2.1⟩

theorem residueBlockLen_subset_Icc {M : ℕ} {Ω : Finset (ZMod M)} {lo len : ℕ} :
    residueBlockLen M Ω lo len ⊆ Set.Icc lo (lo + len) :=
  residueBlock_subset_Icc

theorem residueBlock_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo hi : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlock M Ω lo hi ⊆ residueBlock M Ω' lo hi := by
  intro n hn
  exact ⟨hn.1, hn.2.1, hΩ hn.2.2⟩

theorem residueBlockLen_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo len : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlockLen M Ω lo len ⊆ residueBlockLen M Ω' lo len :=
  residueBlock_mono_residues hΩ

theorem residueBlockFinset_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo hi : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlockFinset M Ω lo hi ⊆ residueBlockFinset M Ω' lo hi := by
  intro n hn
  rw [mem_residueBlockFinset] at hn ⊢
  exact ⟨hn.1, hn.2.1, hΩ hn.2.2⟩

theorem residueBlockLenFinset_mono_residues {M : ℕ} {Ω Ω' : Finset (ZMod M)} {lo len : ℕ}
    (hΩ : Ω ⊆ Ω') :
    residueBlockLenFinset M Ω lo len ⊆ residueBlockLenFinset M Ω' lo len :=
  residueBlockFinset_mono_residues hΩ

theorem residueBlockFinset_card_le_interval (M : ℕ) (Ω : Finset (ZMod M)) (lo hi : ℕ) :
    (residueBlockFinset M Ω lo hi).card ≤ (Finset.Icc lo hi).card := by
  exact Finset.card_filter_le _ _

theorem residueBlockLenFinset_card_le_interval (M : ℕ) (Ω : Finset (ZMod M))
    (lo len : ℕ) :
    (residueBlockLenFinset M Ω lo len).card ≤ (Finset.Icc lo (lo + len)).card :=
  residueBlockFinset_card_le_interval M Ω lo (lo + len)

end Erdos330Formalization
