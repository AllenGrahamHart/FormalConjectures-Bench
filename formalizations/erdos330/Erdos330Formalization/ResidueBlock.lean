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

theorem mem_residueBlock {M : ℕ} {Ω : Finset (ZMod M)} {lo hi n : ℕ} :
    n ∈ residueBlock M Ω lo hi ↔ lo ≤ n ∧ n ≤ hi ∧ (n : ZMod M) ∈ Ω := by
  rfl

theorem mem_residueBlockLen {M : ℕ} {Ω : Finset (ZMod M)} {lo len n : ℕ} :
    n ∈ residueBlockLen M Ω lo len ↔
      lo ≤ n ∧ n ≤ lo + len ∧ (n : ZMod M) ∈ Ω := by
  rfl

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

end Erdos330Formalization
