import Erdos330Formalization.Stage

/-!
# Abstract global construction for Erdős Problem 330

This file proves consequences of an infinite chain of finite stage states.
The concrete stage construction will later supply such a chain.
-/

namespace Erdos330Formalization

/-- The final set produced by an infinite sequence of finite stages. -/
def finalSet (st : ℕ → StageState) : Set ℕ :=
  {n | ∃ k : ℕ, n ∈ (st k).S}

/-- A sequence of stages where each stage extends the previous one. -/
structure StageChain (st : ℕ → StageState) where
  step : ∀ k : ℕ, StageExtension (st k) (st (k + 1))

namespace StageChain

theorem S_subset_of_le {st : ℕ → StageState} (chain : StageChain st)
    {i j : ℕ} (hij : i ≤ j) :
    (st i).S ⊆ (st j).S := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      intro n hn
      exact hn
  | succ j ih =>
      by_cases hle : i ≤ j
      · intro n hn
        exact (chain.step j).S_subset ((ih hle) hn)
      · have hi : i = j + 1 := by omega
        subst hi
        intro n hn
        exact hn

theorem coverStart_eq_of_le {st : ℕ → StageState} (chain : StageChain st)
    {i j : ℕ} (hij : i ≤ j) :
    (st j).coverStart = (st i).coverStart := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
  | succ j ih =>
      by_cases hle : i ≤ j
      · calc
          (st (j + 1)).coverStart = (st j).coverStart := (chain.step j).coverStart_eq
          _ = (st i).coverStart := ih hle
      · have hi : i = j + 1 := by omega
        subst hi
        rfl

theorem coverStart_eq_zero {st : ℕ → StageState} (chain : StageChain st) (j : ℕ) :
    (st j).coverStart = (st 0).coverStart :=
  chain.coverStart_eq_of_le (Nat.zero_le j)

end StageChain

theorem mem_finalSet_of_mem_stage {st : ℕ → StageState} {k n : ℕ}
    (hn : n ∈ (st k).S) :
    n ∈ finalSet st :=
  ⟨k, hn⟩

theorem stage_subset_finalSet {st : ℕ → StageState} (k : ℕ) :
    {n : ℕ | n ∈ (st k).S} ⊆ finalSet st := by
  intro n hn
  exact mem_finalSet_of_mem_stage hn

theorem twoFoldFinset_subset_finalSet {st : ℕ → StageState} (k : ℕ) :
    twoFoldFinset (st k).S ⊆ twoFold (finalSet st) := by
  intro n hn
  rcases hn with ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, mem_finalSet_of_mem_stage hx, y, mem_finalSet_of_mem_stage hy, hxy⟩

/--
If the finite-stage coverage endpoints are unbounded, the final union is an
asymptotic basis of order two.
-/
theorem finalSet_isAsymptoticBasisTwo {st : ℕ → StageState} (chain : StageChain st)
    (hR_unbounded : ∀ n : ℕ, ∃ k : ℕ, n ≤ (st k).R) :
    IsAsymptoticBasisTwo (finalSet st) := by
  refine ⟨(st 0).coverStart, ?_⟩
  intro n hn_start
  obtain ⟨k, hkR⟩ := hR_unbounded n
  have hstage_start : (st k).coverStart ≤ n := by
    rw [chain.coverStart_eq_zero k]
    exact hn_start
  exact twoFoldFinset_subset_finalSet k ((st k).coverage n hstage_start hkR)

theorem mainTarget_of_finalSet_certificates {st : ℕ → StageState} (chain : StageChain st)
    (hR_unbounded : ∀ n : ℕ, ∃ k : ℕ, n ≤ (st k).R)
    (hA_density : HasPositiveUpperDensity (finalSet st))
    (hprivate_density :
      ∀ a ∈ finalSet st, HasPositiveUpperDensity (privateSet (finalSet st) a)) :
    MainTarget := by
  exact ⟨finalSet st, finalSet_isAsymptoticBasisTwo chain hR_unbounded, hA_density,
    hprivate_density⟩

end Erdos330Formalization
