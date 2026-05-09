import FormalConjectures.OpenQuantumProblems.«35»

open scoped BigOperators

namespace OpenQuantumProblem35

noncomputable section

abbrev Pair3 := Fin 3 × Fin 3

def omega43Word (i j : Fin 3) : Config 4 3 :=
  fun k =>
    if k = 0 then i
    else if k = 1 then j
    else if k = 2 then i + j
    else i + j + j

def projectWordPair (a b : Fin 4) (w : Config 4 3) : Pair3 :=
  (w a, w b)

def omega43ParamFromPair (a b : Fin 4) (y : Pair3) : Pair3 :=
  match a.1, b.1 with
  | 0, 1 => (y.1, y.2)
  | 1, 0 => (y.2, y.1)
  | 0, 2 => (y.1, y.2 - y.1)
  | 2, 0 => (y.2, y.1 - y.2)
  | 0, 3 => (y.1, (y.2 - y.1) + (y.2 - y.1))
  | 3, 0 => (y.2, (y.1 - y.2) + (y.1 - y.2))
  | 1, 2 => (y.2 - y.1, y.1)
  | 2, 1 => (y.1 - y.2, y.2)
  | 1, 3 => (y.2 - (y.1 + y.1), y.1)
  | 3, 1 => (y.1 - (y.2 + y.2), y.2)
  | 2, 3 => (y.1 + y.1 - y.2, y.2 - y.1)
  | 3, 2 => (y.2 + y.2 - y.1, y.1 - y.2)
  | _, _ => (0, 0)

def omega43Support : Finset (Config 4 3) :=
  Finset.image (fun p : Pair3 => omega43Word p.1 p.2) Finset.univ

noncomputable def omega43Coeff : ℂ :=
  (3 : ℂ)⁻¹

noncomputable def omega43State : StateVector 4 3 :=
  mkStateVector fun w => if w ∈ omega43Support then omega43Coeff else 0

lemma omega43_projection_injective {a b : Fin 4} (hab : a ≠ b) :
    Function.Injective
      (fun p : Pair3 => projectWordPair a b (omega43Word p.1 p.2)) := by
  intro p q hpq
  fin_cases a <;> fin_cases b <;> simp at hab hpq ⊢
  all_goals
    rcases p with ⟨p0, p1⟩
    rcases q with ⟨q0, q1⟩
    fin_cases p0 <;> fin_cases p1 <;> fin_cases q0 <;> fin_cases q1 <;>
      first | rfl | cases hpq

lemma omega43ParamFromPair_spec {a b : Fin 4} (hab : a ≠ b) (y : Pair3) :
    projectWordPair a b
        (omega43Word (omega43ParamFromPair a b y).1 (omega43ParamFromPair a b y).2) =
      y := by
  fin_cases a <;> fin_cases b <;> simp at hab ⊢
  all_goals
    rcases y with ⟨y0, y1⟩
    fin_cases y0 <;> fin_cases y1 <;>
      rfl

def sourceLeftIndex (π : Equiv.Perm (Fin 4)) (i : Fin 2) : Fin 4 :=
  π.symm (leftIndex (m := 2) (n := 4) (by decide) i)

def sourceRightIndex (π : Equiv.Perm (Fin 4)) (i : Fin 2) : Fin 4 :=
  π.symm (rightIndex (m := 2) (n := 4) (by decide) i)

lemma sourceLeftIndex_ne (π : Equiv.Perm (Fin 4)) :
    sourceLeftIndex π 0 ≠ sourceLeftIndex π 1 := by
  intro h
  have h' := congrArg π h
  simp [sourceLeftIndex, leftIndex] at h'

def omega43ParamForLeft (π : Equiv.Perm (Fin 4)) (x : Config 2 3) : Pair3 :=
  omega43ParamFromPair (sourceLeftIndex π 0) (sourceLeftIndex π 1) (x 0, x 1)

def omega43Completion (π : Equiv.Perm (Fin 4)) (x : Config 2 3) : Config 2 3 :=
  fun r =>
    omega43Word (omega43ParamForLeft π x).1 (omega43ParamForLeft π x).2
      (sourceRightIndex π r)

lemma config2_ext {x y : Config 2 3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) :
    x = y := by
  ext i
  fin_cases i
  · exact congrArg Fin.val h0
  · exact congrArg Fin.val h1

lemma sourceRightIndex_ne (π : Equiv.Perm (Fin 4)) :
    sourceRightIndex π 0 ≠ sourceRightIndex π 1 := by
  intro h
  have h' := congrArg π h
  simp [sourceRightIndex, rightIndex] at h'

lemma permuteConfig_combine_sourceLeft
    (π : Equiv.Perm (Fin 4)) (x z : Config 2 3) (i : Fin 2) :
    permuteConfig π (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
        (sourceLeftIndex π i) = x i := by
  simp [permuteConfig, sourceLeftIndex]

lemma permuteConfig_combine_sourceRight
    (π : Equiv.Perm (Fin 4)) (x z : Config 2 3) (i : Fin 2) :
    permuteConfig π (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
        (sourceRightIndex π i) = z i := by
  simp [permuteConfig, sourceRightIndex]

lemma omega43ParamForLeft_spec (π : Equiv.Perm (Fin 4)) (x : Config 2 3) :
    projectWordPair (sourceLeftIndex π 0) (sourceLeftIndex π 1)
        (omega43Word (omega43ParamForLeft π x).1 (omega43ParamForLeft π x).2) =
      (x 0, x 1) := by
  exact omega43ParamFromPair_spec (sourceLeftIndex_ne π) (x 0, x 1)

lemma omega43ParamForLeft_left
    (π : Equiv.Perm (Fin 4)) (x : Config 2 3) (i : Fin 2) :
    omega43Word (omega43ParamForLeft π x).1 (omega43ParamForLeft π x).2
        (sourceLeftIndex π i) = x i := by
  have h := omega43ParamForLeft_spec π x
  fin_cases i
  · simpa [projectWordPair] using congrArg Prod.fst h
  · simpa [projectWordPair] using congrArg Prod.snd h

lemma omega43ParamForLeft_eq_of_project
    (π : Equiv.Perm (Fin 4)) (x : Config 2 3) (p : Pair3)
    (h :
      projectWordPair (sourceLeftIndex π 0) (sourceLeftIndex π 1)
        (omega43Word p.1 p.2) = (x 0, x 1)) :
    p = omega43ParamForLeft π x := by
  exact omega43_projection_injective (sourceLeftIndex_ne π)
    (by
      calc
        projectWordPair (sourceLeftIndex π 0) (sourceLeftIndex π 1)
            (omega43Word p.1 p.2) = (x 0, x 1) := h
        _ = projectWordPair (sourceLeftIndex π 0) (sourceLeftIndex π 1)
            (omega43Word (omega43ParamForLeft π x).1
              (omega43ParamForLeft π x).2) := by
              exact (omega43ParamForLeft_spec π x).symm)

lemma omega43Support_mem_iff (w : Config 4 3) :
    w ∈ omega43Support ↔ ∃ p : Pair3, w = omega43Word p.1 p.2 := by
  simp [omega43Support, eq_comm]

lemma sourceIndex_cases (π : Equiv.Perm (Fin 4)) (a : Fin 4) :
    (∃ i : Fin 2, a = sourceLeftIndex π i) ∨
      ∃ i : Fin 2, a = sourceRightIndex π i := by
  by_cases hleft : (π a).1 < 2
  · left
    let i : Fin 2 := ⟨(π a).1, hleft⟩
    refine ⟨i, ?_⟩
    apply π.injective
    apply Fin.ext
    simp [sourceLeftIndex, leftIndex, i]
  · right
    have hge : 2 ≤ (π a).1 := Nat.le_of_not_gt hleft
    let i : Fin 2 := ⟨(π a).1 - 2, by omega⟩
    refine ⟨i, ?_⟩
    apply π.injective
    apply Fin.ext
    simp [sourceRightIndex, rightIndex, i]
    omega

lemma omega43Coeff_norm_sq :
    ‖omega43Coeff‖ ^ 2 = (9 : ℝ)⁻¹ := by
  norm_num [omega43Coeff]

lemma omega43Coeff_mul_star :
    omega43Coeff * star omega43Coeff =
      ((Fintype.card (Config 2 3) : ℂ)⁻¹) := by
  norm_num [omega43Coeff, card_config]

lemma omega43Support_card :
    omega43Support.card = 9 := by
  rw [omega43Support, Finset.card_image_of_injective]
  · simp [Pair3]
  · intro p q hpq
    exact omega43_projection_injective (a := 0) (b := 1) (by decide)
      (by simpa [projectWordPair] using congrArg (projectWordPair 0 1) hpq)

lemma omega43State_isNormalized : IsNormalized omega43State := by
  rw [isNormalized_iff_norm_sq_eq_one]
  calc
    ‖omega43State‖ ^ 2
        = ∑ w : Config 4 3, ‖omega43State w‖ ^ 2 := by
            simpa using (EuclideanSpace.norm_sq_eq omega43State)
    _ = ∑ w : Config 4 3,
          if w ∈ omega43Support then ‖omega43Coeff‖ ^ 2 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            by_cases h : w ∈ omega43Support
            · simp [omega43State, h]
            · simp [omega43State, h]
    _ = (omega43Support.card : ℝ) * ‖omega43Coeff‖ ^ 2 := by
            rw [← Finset.sum_filter
              (s := Finset.univ)
              (p := fun w : Config 4 3 => w ∈ omega43Support)
              (f := fun _ => ‖omega43Coeff‖ ^ 2)]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
            rw [omega43Support_card, omega43Coeff_norm_sq]
            norm_num

lemma omega43Completion_injective (π : Equiv.Perm (Fin 4)) :
    Function.Injective (omega43Completion π) := by
  intro x y hxy
  let px := omega43ParamForLeft π x
  let py := omega43ParamForLeft π y
  have hproj :
      projectWordPair (sourceRightIndex π 0) (sourceRightIndex π 1)
          (omega43Word px.1 px.2) =
        projectWordPair (sourceRightIndex π 0) (sourceRightIndex π 1)
          (omega43Word py.1 py.2) := by
    apply Prod.ext
    · simpa [projectWordPair, omega43Completion, px, py] using congrFun hxy 0
    · simpa [projectWordPair, omega43Completion, px, py] using congrFun hxy 1
  have hparam : px = py :=
    omega43_projection_injective (sourceRightIndex_ne π) hproj
  apply config2_ext
  · calc
      x 0 = omega43Word px.1 px.2 (sourceLeftIndex π 0) := by
        simpa [px] using (omega43ParamForLeft_left π x 0).symm
      _ = omega43Word py.1 py.2 (sourceLeftIndex π 0) := by rw [hparam]
      _ = y 0 := by
        simpa [py] using omega43ParamForLeft_left π y 0
  · calc
      x 1 = omega43Word px.1 px.2 (sourceLeftIndex π 1) := by
        simpa [px] using (omega43ParamForLeft_left π x 1).symm
      _ = omega43Word py.1 py.2 (sourceLeftIndex π 1) := by rw [hparam]
      _ = y 1 := by
        simpa [py] using omega43ParamForLeft_left π y 1

lemma omega43Support_permuted_iff
    (π : Equiv.Perm (Fin 4)) (x z : Config 2 3) :
    permuteConfig π (combineFirst (n := 4) (d := 3) 2 (by decide) x z) ∈
        omega43Support ↔
      z = omega43Completion π x := by
  constructor
  · intro hmem
    rcases (omega43Support_mem_iff _).1 hmem with ⟨p, hp⟩
    have hleft :
        projectWordPair (sourceLeftIndex π 0) (sourceLeftIndex π 1)
            (omega43Word p.1 p.2) = (x 0, x 1) := by
      apply Prod.ext
      · calc
          omega43Word p.1 p.2 (sourceLeftIndex π 0)
              = permuteConfig π
                  (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
                  (sourceLeftIndex π 0) := by
                    rw [hp]
          _ = x 0 := permuteConfig_combine_sourceLeft π x z 0
      · calc
          omega43Word p.1 p.2 (sourceLeftIndex π 1)
              = permuteConfig π
                  (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
                  (sourceLeftIndex π 1) := by
                    rw [hp]
          _ = x 1 := permuteConfig_combine_sourceLeft π x z 1
    have hp_param : p = omega43ParamForLeft π x :=
      omega43ParamForLeft_eq_of_project π x p hleft
    apply config2_ext
    · calc
        z 0 = permuteConfig π
            (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
            (sourceRightIndex π 0) := by
              exact (permuteConfig_combine_sourceRight π x z 0).symm
        _ = omega43Word p.1 p.2 (sourceRightIndex π 0) := by
              rw [hp]
        _ = omega43Completion π x 0 := by
              rw [hp_param]
              rfl
    · calc
        z 1 = permuteConfig π
            (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
            (sourceRightIndex π 1) := by
              exact (permuteConfig_combine_sourceRight π x z 1).symm
        _ = omega43Word p.1 p.2 (sourceRightIndex π 1) := by
              rw [hp]
        _ = omega43Completion π x 1 := by
              rw [hp_param]
              rfl
  · intro hz
    let p := omega43ParamForLeft π x
    rw [omega43Support_mem_iff]
    refine ⟨p, ?_⟩
    ext a
    rcases sourceIndex_cases π a with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact congrArg Fin.val <| by
        calc
          permuteConfig π (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
              (sourceLeftIndex π i)
              = x i := permuteConfig_combine_sourceLeft π x z i
          _ = omega43Word p.1 p.2 (sourceLeftIndex π i) := by
              simpa [p] using (omega43ParamForLeft_left π x i).symm
    · exact congrArg Fin.val <| by
        calc
          permuteConfig π (combineFirst (n := 4) (d := 3) 2 (by decide) x z)
              (sourceRightIndex π i)
              = z i := permuteConfig_combine_sourceRight π x z i
          _ = omega43Completion π x i := by rw [hz]
          _ = omega43Word p.1 p.2 (sourceRightIndex π i) := rfl

lemma omega43State_permuted_graph (π : Equiv.Perm (Fin 4)) :
    ∀ x z,
      permuteState π omega43State
          (combineFirst (n := 4) (d := 3) 2 (by decide) x z) =
        if z = omega43Completion π x then omega43Coeff else 0 := by
  intro x z
  rw [permuteState_apply, omega43State, mkStateVector_apply]
  by_cases h : z = omega43Completion π x
  · have hmem := (omega43Support_permuted_iff π x z).2 h
    rw [if_pos hmem, if_pos h]
  · have hmem : permuteConfig π
        (combineFirst (n := 4) (d := 3) 2 (by decide) x z) ∉ omega43Support := by
      intro hsupp
      exact h ((omega43Support_permuted_iff π x z).1 hsupp)
    rw [if_neg hmem, if_neg h]

lemma omega43_hasMaximallyMixedFirstReduction (π : Equiv.Perm (Fin 4)) :
    HasMaximallyMixedFirstReduction (n := 4) (d := 3)
      2 (by decide) (permuteState π omega43State) := by
  apply hasMaximallyMixedFirstReduction_of_completion
    (n := 4) (d := 3) (m := 2) (hm := by decide)
    (ψ := permuteState π omega43State)
    (completion := omega43Completion π)
    (coeff := omega43Coeff)
  · exact omega43State_permuted_graph π
  · exact omega43Completion_injective π
  · exact omega43Coeff_mul_star

theorem ame_4_3_exists_formal : ExistsAME 4 3 := by
  refine ⟨omega43State, ?_⟩
  refine ⟨omega43State_isNormalized, ?_⟩
  intro π
  simpa using omega43_hasMaximallyMixedFirstReduction π

end

end OpenQuantumProblem35
