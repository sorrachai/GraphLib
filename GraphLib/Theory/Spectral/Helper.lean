import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

import Mathlib.Data.Real.Basic

import GraphLib.Graph.Basic
import GraphLib.Graph.Finite
import GraphLib.Theory.Spectral.Cuts

namespace GraphLib

open Finset
open ProbabilityTheory MeasureTheory
open Cuts

variable {α : Type*} [DecidableEq α]

lemma sum_sq_pos (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ)
    (h_x_ne : ∃ v ∈ G.vertexFinset, x v ≠ 0) : 0 < ∑ i ∈ G.vertexFinset, x i ^ 2 := by
  have h_nonneg : 0 ≤ ∑ i ∈ G.vertexFinset, x i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  apply lt_of_le_of_ne h_nonneg
  intro h_sum_zero
  have h_all_zero : ∀ i ∈ G.vertexFinset, x i = 0 := by
    intro i hi
    have h_sq_zero : x i ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg _).mp h_sum_zero.symm i hi
      intro j hj
      apply sq_nonneg
    exact eq_zero_of_pow_eq_zero h_sq_zero
  grind

lemma pos_neg_sq_add (a : ℝ) :
    max a 0 ^ 2 + max (-a) 0 ^ 2 = a ^ 2 := by grind

lemma pos_neg_sub_sq_add_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤
      (a - b) ^ 2 := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · simp [max_eq_left ha, max_eq_left hb,
      max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr hb)]
  · have hb' : b < 0 := lt_of_not_ge hb
    simp [max_eq_left ha, max_eq_right hb'.le,
      max_eq_right (neg_nonpos.mpr ha), max_eq_left (neg_nonneg.mpr hb'.le)]
    nlinarith [ha, hb']
  · have ha' : a < 0 := lt_of_not_ge ha
    simp [max_eq_right ha'.le, max_eq_left hb,
      max_eq_left (neg_nonneg.mpr ha'.le), max_eq_right (neg_nonpos.mpr hb)]
    nlinarith [ha', hb]
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge hb
    simp [max_eq_right ha'.le, max_eq_right hb'.le,
      max_eq_left (neg_nonneg.mpr ha'.le), max_eq_left (neg_nonneg.mpr hb'.le)]
    nlinarith


lemma exists_ratio_le_of_sum_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (R : ℝ)
    (hs : s.Nonempty)
    (hb_pos : ∀ i ∈ s, 0 < b i)
    (h_sum : ∑ i ∈ s, a i ≤ R * ∑ i ∈ s, b i) :
    ∃ i ∈ s, 0 < b i ∧ a i / b i ≤ R := by
  by_contra h_no
  push Not at h_no
  have h_each_gt : ∀ i ∈ s, R * b i < a i := by
    intro i hi
    have hratio_not := h_no i hi (hb_pos i hi)
    have hratio_gt : R < a i / b i := hratio_not
    exact (lt_div_iff₀ (hb_pos i hi)).1 hratio_gt
  have h_total_gt : R * ∑ i ∈ s, b i < ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hs h_each_gt
  nlinarith

lemma sum_le_sqrt_mul_sqrt_of_le_mul {ι : Type*} (s : Finset ι)
    (w A B : ι → ℝ)
    (hw_le : ∀ i ∈ s, w i ≤ A i * B i) :
    ∑ i ∈ s, w i ≤
      Real.sqrt (∑ i ∈ s, A i ^ 2) * Real.sqrt (∑ i ∈ s, B i ^ 2) := by
  calc
    ∑ i ∈ s, w i
        ≤ ∑ i ∈ s, A i * B i := Finset.sum_le_sum hw_le
    _ ≤ Real.sqrt (∑ i ∈ s, A i ^ 2) * Real.sqrt (∑ i ∈ s, B i ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt s A B

lemma abs_sq_sub_sq_le_abs_sub_mul_add_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ 2 - b ^ 2| ≤ |a - b| * (a + b) := by
  have hab_nonneg : 0 ≤ a + b := add_nonneg ha hb
  calc
    |a ^ 2 - b ^ 2| = |(a - b) * (a + b)| := by ring_nf
    _ = |a - b| * |a + b| := abs_mul _ _
    _ ≤ |a - b| * (a + b) := by rw [abs_of_nonneg hab_nonneg]

lemma positive_value_levels_nonempty (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    (h_y_pos : ∃ v ∈ G.vertexFinset, 0 < y v) :
    ((G.vertexFinset.image y).filter (fun t => 0 < t)).Nonempty := by
  rcases h_y_pos with ⟨v, hv, hv_pos⟩
  exact ⟨y v, by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hv_pos⟩⟩

lemma positive_value_level_pos (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ) :
    ∀ t ∈ (G.vertexFinset.image y).filter (fun t => 0 < t), 0 < t := by
  intro t ht
  exact (Finset.mem_filter.mp ht).2

lemma positive_value_level_set_nonempty (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ) :
    ∀ t ∈ (G.vertexFinset.image y).filter (fun t => 0 < t),
      (G.vertexFinset.filter (fun v => y v ≥ t)).Nonempty := by
  intro t ht
  rcases Finset.mem_image.mp (Finset.mem_filter.mp ht).1 with ⟨v, hv, rfl⟩
  exact ⟨v, by simp [hv]⟩

lemma positive_value_level_mem_image {G : SimpleGraph α} [Finite G.vertexSet] {y : α → ℝ} {t : ℝ}
    (ht : t ∈ (G.vertexFinset.image y).filter (fun t => 0 < t)) :
    t ∈ G.vertexFinset.image y := (Finset.mem_filter.mp ht).1


end GraphLib
