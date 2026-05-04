import Mathlib.NumberTheory.LegendreSymbol.Basic
import Erdos330Formalization.PrimeSupply

/-!
# Quadratic-residue lemmas for Erdős Problem 330

This file contains the finite-field lemmas used by the selected coordinate of
the CRT gadget.
-/

namespace Erdos330Formalization

/-- Nonzero quadratic residues in `ZMod p`. -/
noncomputable def QR (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun x => x ≠ 0 ∧ IsSquare x

theorem mem_QR {p : ℕ} [NeZero p] {x : ZMod p} :
    x ∈ QR p ↔ x ≠ 0 ∧ IsSquare x := by
  classical
  simp [QR]

theorem qr_neg_disjoint (p : ℕ) [Fact p.Prime] [NeZero p] (hp3 : p % 4 = 3) :
    ∀ x : ZMod p, x ∈ QR p → -x ∉ QR p := by
  classical
  intro x hx hxneg
  rw [mem_QR] at hx hxneg
  have hx0 : x ≠ 0 := hx.1
  have hxsq : IsSquare x := hx.2
  have hnegsq : IsSquare (-x) := hxneg.2
  have hdiv : IsSquare ((-x) / x) := hnegsq.div hxsq
  have hquot : (-x) / x = (-1 : ZMod p) := by
    field_simp [hx0]
  have hsqnegone : IsSquare (-1 : ZMod p) := by
    simpa [hquot] using hdiv
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsqnegone) hp3

end Erdos330Formalization
