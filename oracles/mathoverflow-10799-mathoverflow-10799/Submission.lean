import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace Mathoverflow10799

open Finset Real

noncomputable def muBench {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  p ^ #S * (1 - p) ^ (n - #S)

noncomputable def muFamilyBench {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S ∈ F, muBench p S

def boundaryCountBench (n : ℕ) (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ Xor' (S ∈ F) (symmDiff S {i} ∈ F)).card

noncomputable def edgeBoundaryBench (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S : Finset (Fin n), muBench p S * boundaryCountBench n F S

abbrev IsMonotoneIncreasingBench {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  IsUpperSet (↑F : Set (Finset (Fin n)))

noncomputable def IsOptimalBench {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : Prop :=
  let m := muFamilyBench p F
  edgeBoundaryBench n p F ≤ 1000 * Real.log (1 / p) * (m * Real.logb p m / p)

def perlesFamily (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.erase ∅

lemma perlesFamily_monotone (n : ℕ) : IsMonotoneIncreasingBench (perlesFamily n) := by
  intro S T hST hS
  simp only [perlesFamily, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true] at hS ⊢
  exact fun h => hS (Finset.subset_empty.mp (h ▸ hST))

lemma perlesFamily_measure {n : ℕ} (p : ℝ) :
    muFamilyBench p (perlesFamily n) = 1 - (1 - p) ^ n := by
  unfold muFamilyBench perlesFamily
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  have hsum : ∑ S : Finset (Fin n), muBench p S = 1 := by
    unfold muBench
    have h := Fintype.sum_pow_mul_eq_add_pow (Fin n) p (1 - p)
    rw [Fintype.card_fin] at h
    rw [h]
    simp
  rw [hsum]
  simp [muBench, Finset.card_empty]

lemma perlesFamily_boundary_empty (n : ℕ) :
    boundaryCountBench n (perlesFamily n) (∅ : Finset (Fin n)) = n := by
  simp [boundaryCountBench, perlesFamily]

lemma perlesFamily_edgeBoundary_lower {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (n : ℝ) * (1 - p) ^ n ≤ edgeBoundaryBench n p (perlesFamily n) := by
  unfold edgeBoundaryBench
  let S0 : Finset (Fin n) := ∅
  have hmem : S0 ∈ (Finset.univ : Finset (Finset (Fin n))) := by simp [S0]
  have hnonneg : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      0 ≤ muBench p S * boundaryCountBench n (perlesFamily n) S := by
    intro S _
    have h1mp : 0 ≤ 1 - p := by linarith
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hp.le _) (pow_nonneg h1mp _))
      (Nat.cast_nonneg _)
  have hsingle := Finset.single_le_sum hnonneg hmem
  convert hsingle using 1
  simp [S0, muBench, perlesFamily_boundary_empty, mul_comm]

lemma log_one_sub_inv_le {q : ℝ} (_hq : 0 < q) (hq' : q < 1) :
    Real.log (1 / (1 - q)) ≤ q / (1 - q) := by
  have h1mq : 0 < 1 - q := by linarith
  rw [one_div]
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr h1mq)
  have hid : (1 - q)⁻¹ - 1 = q / (1 - q) := by
    rw [inv_eq_one_div, div_sub_one h1mq.ne', sub_sub_cancel]
  linarith

lemma log_inv_mul_logb_eq_log_inv {p m : ℝ} (hp : 0 < p) (hp' : p < 1) (hm : 0 < m) :
    Real.log (1 / p) * Real.logb p m = Real.log (1 / m) := by
  have hp_ne : p ≠ 0 := hp.ne'
  have hm_ne : m ≠ 0 := hm.ne'
  have hlogp : Real.log p ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hp (ne_of_lt hp')
  rw [← Real.log_div_log, Real.log_div one_ne_zero hp_ne, Real.log_div one_ne_zero hm_ne,
    Real.log_one]
  field_simp [hlogp]
  ring

lemma perlesFamily_not_optimal {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hn : 0 < n) (hbig : (1000 : ℝ) < n * p) :
    ¬ IsOptimalBench p (perlesFamily n) := by
  unfold IsOptimalBench
  simp only [not_le]
  rw [perlesFamily_measure]
  set q := (1 - p) ^ n with hq_def
  have h1mp : 0 < 1 - p := by linarith
  have hq_pos : 0 < q := by simpa [hq_def] using pow_pos h1mp n
  have hq_lt_one : q < 1 := by
    have h1p_lt : 1 - p < 1 := by linarith
    rw [hq_def]
    exact pow_lt_one₀ h1mp.le h1p_lt hn.ne'
  have h1mq : 0 < 1 - q := by linarith
  have hlog :
      Real.log (1 / p) * Real.logb p (1 - q) = Real.log (1 / (1 - q)) :=
    log_inv_mul_logb_eq_log_inv hp hp' h1mq
  have hrhs_eq :
      1000 * Real.log (1 / p) * ((1 - q) * Real.logb p (1 - q) / p) =
        1000 * ((1 - q) * Real.log (1 / (1 - q)) / p) := by
    rw [← hlog]
    ring
  rw [hrhs_eq]
  have hrhs_le : 1000 * ((1 - q) * Real.log (1 / (1 - q)) / p) ≤ 1000 * (q / p) := by
    have hlog_le := log_one_sub_inv_le hq_pos hq_lt_one
    calc
      1000 * ((1 - q) * Real.log (1 / (1 - q)) / p)
          ≤ 1000 * ((1 - q) * (q / (1 - q)) / p) := by
            gcongr
      _ = 1000 * (q / p) := by field_simp [h1mq.ne']
  have hrhs_lt : 1000 * (q / p) < (n : ℝ) * q := by
    have hmul : 1000 * q < ((n : ℝ) * p) * q := by
      exact mul_lt_mul_of_pos_right hbig hq_pos
    calc
      1000 * (q / p) = (1000 * q) / p := by ring
      _ < (((n : ℝ) * p) * q) / p := div_lt_div_of_pos_right hmul hp
      _ = (n : ℝ) * q := by field_simp [hp.ne']
  have hlower := perlesFamily_edgeBoundary_lower (n := n) hp hp'
  exact (lt_of_le_of_lt hrhs_le hrhs_lt).trans_le hlower

lemma exists_large_simple :
    ∃ n : ℕ, 2002 < n ∧ (n : ℝ) / 2002 > 1000 * Real.log n := by
  obtain ⟨n, hn_small, hn_ge⟩ :
      ∃ n : ℕ, (1000 * (2002 * Real.log n)) / (n : ℝ) < 1 ∧ 2003 ≤ n := by
    exact ((((Real.isLittleO_log_id_atTop.natCast_atTop.const_mul_left 2002).const_mul_left 1000).tendsto_div_nhds_zero.eventually_lt_const one_pos).and
      (Filter.mem_atTop (2003))).exists
  have hn_large : 2002 < n := by omega
  refine ⟨n, hn_large, ?_⟩
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn_large)
  have hlt : 1000 * (2002 * Real.log n) < (n : ℝ) := by
    exact (div_lt_one hn_pos).mp hn_small
  calc
    1000 * Real.log n = (1000 * (2002 * Real.log n)) / 2002 := by ring
    _ < (n : ℝ) / 2002 := div_lt_div_of_pos_right hlt (by norm_num)

theorem perles_counterexample_simple :
    ∃ (n : ℕ), 2 ≤ n ∧ ∃ (F : Finset (Finset (Fin n))),
    IsMonotoneIncreasingBench F ∧
    ∃ (s t : ℝ), 0 < s ∧ s ≤ t ∧ t < 1 ∧
    t / s > 1000 * Real.log n ∧
    ∀ p, s ≤ p → p ≤ t → ¬ IsOptimalBench p F := by
  obtain ⟨n, hn_large, hn_log⟩ := exists_large_simple
  have hn_pos_nat : 0 < n := Nat.zero_lt_of_lt (by omega)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  refine ⟨n, by omega, perlesFamily n, perlesFamily_monotone n,
    (1001 : ℝ) / n, 1 / 2, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · rw [div_le_iff₀ hn_pos]
    have hn2002 : (2002 : ℝ) ≤ n := by exact_mod_cast (le_of_lt hn_large)
    linarith
  · norm_num
  · calc
      (1 / 2 : ℝ) / (1001 / (n : ℝ)) = (n : ℝ) / 2002 := by
        field_simp [hn_pos.ne']
        ring
      _ > 1000 * Real.log n := hn_log
  · intro p hsp hpt
    have hp : 0 < p := by
      exact (div_pos (by norm_num) hn_pos).trans_le hsp
    have hp' : p < 1 := hpt.trans_lt (by norm_num)
    apply perlesFamily_not_optimal hp hp' hn_pos_nat
    have hnp : (1001 : ℝ) ≤ (n : ℝ) * p := by
      have hmul := mul_le_mul_of_nonneg_left hsp (le_of_lt hn_pos)
      have hleft : (n : ℝ) * ((1001 : ℝ) / n) = 1001 := by field_simp [hn_pos.ne']
      rwa [hleft] at hmul
    exact lt_of_lt_of_le (by norm_num) hnp

end Mathoverflow10799
