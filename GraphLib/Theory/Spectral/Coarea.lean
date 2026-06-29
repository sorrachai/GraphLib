import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Chain

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

import GraphLib.Graph.Basic
import GraphLib.Graph.Finite
import GraphLib.Graph.Degree
import GraphLib.Theory.Spectral.Cuts
import GraphLib.Theory.Spectral.Helper
import GraphLib.Theory.Spectral.Expansion

open Finset
open Cuts
open ProbabilityTheory MeasureTheory

namespace GraphLib

variable {α : Type*} [DecidableEq α]


noncomputable def previousLevel (levels : Finset ℝ) (t : ℝ) : ℝ :=
  if h : (levels.filter (fun s => s < t)).Nonempty then
    (levels.filter (fun s => s < t)).max' h
  else 0

noncomputable def coareaWeight (levels : Finset ℝ) (t : ℝ) : ℝ :=
  t ^ 2 - (previousLevel levels t) ^ 2

lemma previousLevel_lt_of_pos_mem {levels : Finset ℝ} {t : ℝ}
    (ht_pos : 0 < t) :
    previousLevel levels t < t := by
  unfold previousLevel
  by_cases h : (levels.filter (fun s => s < t)).Nonempty
  · rw [dif_pos h]
    exact (Finset.max'_lt_iff (levels.filter (fun s => s < t)) h).mpr (by
      intro s hs
      exact (Finset.mem_filter.mp hs).2)
  · rw [dif_neg h]
    exact ht_pos

lemma previousLevel_nonneg_of_positive_levels {levels : Finset ℝ} {t : ℝ}
    (hlevels_pos : ∀ s ∈ levels, 0 < s) :
    0 ≤ previousLevel levels t := by
  unfold previousLevel
  by_cases h : (levels.filter (fun s => s < t)).Nonempty
  · rw [dif_pos h]
    have hmem : (levels.filter (fun s => s < t)).max' h ∈
        levels.filter (fun s => s < t) := Finset.max'_mem _ _
    exact le_of_lt (hlevels_pos _ (Finset.mem_filter.mp hmem).1)
  · rw [dif_neg h]

lemma coareaWeight_pos_of_pos_mem {levels : Finset ℝ} {t : ℝ}
    (hlevels_pos : ∀ s ∈ levels, 0 < s)
    (ht_pos : 0 < t) :
    0 < coareaWeight levels t := by
  unfold coareaWeight
  have hpred_nonneg : 0 ≤ previousLevel levels t :=
    previousLevel_nonneg_of_positive_levels hlevels_pos
  have hpred_lt : previousLevel levels t < t :=
    previousLevel_lt_of_pos_mem ht_pos
  have hsq_lt : (previousLevel levels t) ^ 2 < t ^ 2 := by
    nlinarith
  nlinarith

lemma previousLevel_insert_of_lt {levels : Finset ℝ} {a t : ℝ}
    (ht_lt_a : t < a) :
    previousLevel (insert a levels) t = previousLevel levels t := by
  unfold previousLevel
  have hfilter :
      (insert a levels).filter (fun s => s < t) = levels.filter (fun s => s < t) := by
    ext s
    by_cases hsa : s = a
    · subst hsa
      simp [not_lt_of_ge (le_of_lt ht_lt_a)]
    · simp [hsa]
  rw [hfilter]

lemma previousLevel_insert_top {levels : Finset ℝ} {a : ℝ}
    (h_all_lt : ∀ s ∈ levels, s < a) :
    previousLevel (insert a levels) a = if h : levels.Nonempty then levels.max' h else 0 := by
  unfold previousLevel
  have hfilter : (insert a levels).filter (fun s => s < a) = levels := by
    ext s
    by_cases hsa : s = a
    · subst hsa
      simp only [Finset.mem_filter, Finset.mem_insert, lt_self_iff_false, and_false, false_iff]
      intro ha
      exact (lt_irrefl _) (h_all_lt _ ha)
    · constructor
      · intro hs
        rcases Finset.mem_insert.mp (Finset.mem_filter.mp hs).1 with rfl | hs_mem
        · exact (hsa rfl).elim
        · exact hs_mem
      · intro hs
        exact Finset.mem_filter.mpr ⟨by simp [hs], h_all_lt s hs⟩
  rw [hfilter]

lemma sum_coareaWeight_eq_max_sq_or_zero (levels : Finset ℝ) :
    ∑ t ∈ levels, coareaWeight levels t =
      if h : levels.Nonempty then (levels.max' h) ^ 2 else 0 := by
  classical
  refine Finset.induction_on_max levels ?_ ?_
  · simp
  · intro a s h_all_lt ih
    have ha_not_mem : a ∉ s := by
      intro ha
      exact (lt_irrefl a) (h_all_lt a ha)
    rw [Finset.sum_insert ha_not_mem]
    have h_weight_a :
        coareaWeight (insert a s) a =
          a ^ 2 - (if h : s.Nonempty then (s.max' h) ^ 2 else 0) := by
      unfold coareaWeight
      rw [previousLevel_insert_top h_all_lt]
      by_cases hs : s.Nonempty
      · simp [hs]
      · simp [hs]
    have h_sum_s :
        ∑ x ∈ s, coareaWeight (insert a s) x = ∑ x ∈ s, coareaWeight s x := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold coareaWeight
      rw [previousLevel_insert_of_lt (h_all_lt x hx)]
    rw [h_sum_s, ih, h_weight_a]
    have h_insert_ne : (insert a s).Nonempty := Finset.insert_nonempty a s
    have h_max_insert : (insert a s).max' h_insert_ne = a := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (by
          intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact le_rfl
          · exact le_of_lt (h_all_lt x hx))
      · exact Finset.le_max' _ a (by simp)
    rw [dif_pos h_insert_ne, h_max_insert]
    by_cases hs : s.Nonempty
    · rw [dif_pos hs]
      ring
    · rw [dif_neg hs]
      ring

lemma sum_coareaWeight_le_value_sq {levels : Finset ℝ} {a : ℝ} :
    ∑ t ∈ levels.filter (fun t => t ≤ a), coareaWeight (levels.filter (fun t => t ≤ a)) t =
      if h : (levels.filter (fun t => t ≤ a)).Nonempty then
        ((levels.filter (fun t => t ≤ a)).max' h) ^ 2
      else 0 := by
  exact sum_coareaWeight_eq_max_sq_or_zero _

lemma previousLevel_filter_le_eq {levels : Finset ℝ} {a t : ℝ}
    (ht_le : t ≤ a) :
    previousLevel (levels.filter (fun s => s ≤ a)) t = previousLevel levels t := by
  unfold previousLevel
  have hfilter :
      ((levels.filter (fun s => s ≤ a)).filter (fun s => s < t)) =
        levels.filter (fun s => s < t) := by
    ext s
    constructor
    · intro hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1,
        (Finset.mem_filter.mp hs).2⟩
    · intro hs
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hs).1, le_trans (le_of_lt (Finset.mem_filter.mp hs).2) ht_le⟩,
        (Finset.mem_filter.mp hs).2⟩
  rw [hfilter]

lemma coareaWeight_filter_le_eq {levels : Finset ℝ} {a t : ℝ}
    (ht_le : t ≤ a) :
    coareaWeight (levels.filter (fun s => s ≤ a)) t = coareaWeight levels t := by
  unfold coareaWeight
  rw [previousLevel_filter_le_eq ht_le]

lemma sum_coareaWeight_initial_segment_eq_max_sq {levels : Finset ℝ} {a : ℝ}
    (ha_mem : a ∈ levels) :
    ∑ t ∈ levels.filter (fun t => t ≤ a), coareaWeight levels t = a ^ 2 := by
  classical
  have hsum_filter :
      ∑ t ∈ levels.filter (fun t => t ≤ a), coareaWeight levels t =
        ∑ t ∈ levels.filter (fun t => t ≤ a),
          coareaWeight (levels.filter (fun s => s ≤ a)) t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [coareaWeight_filter_le_eq (Finset.mem_filter.mp ht).2]
  rw [hsum_filter, sum_coareaWeight_eq_max_sq_or_zero]
  have hne : (levels.filter (fun t => t ≤ a)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha_mem, le_rfl⟩⟩
  have hmax : (levels.filter (fun t => t ≤ a)).max' hne = a := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (by
        intro t ht
        exact (Finset.mem_filter.mp ht).2)
    · exact Finset.le_max' (levels.filter (fun t => t ≤ a)) a
        (Finset.mem_filter.mpr ⟨ha_mem, le_rfl⟩)
  rw [dif_pos hne, hmax]

lemma sum_coareaWeight_initial_segment_eq_value_sq (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) (v : α) (hv : v ∈ G.vertexFinset) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t = y v ^ 2 := by
  classical
  intro levels
  by_cases hv_pos : 0 < y v
  · have hy_mem : y v ∈ levels := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hv_pos⟩
    exact sum_coareaWeight_initial_segment_eq_max_sq hy_mem
  · have hy_zero : y v = 0 := by
      have hy_nonneg := h_pos v
      linarith
    have hfilter_empty : levels.filter (fun t => t ≤ 0) = ∅ := by
      ext t
      simp [levels]
    rw [hy_zero]
    simp [hfilter_empty]

lemma sum_coareaWeight_between_vertex_values_eq_sq_sub
    (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ) (h_pos : ∀ v, 0 ≤ y v)
    {u v : α} (huV : u ∈ G.vertexFinset) (hvV : v ∈ G.vertexFinset)
    (huv : y u ≤ y v) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
        coareaWeight levels t = y v ^ 2 - y u ^ 2 := by
  classical
  intro levels
  have hv_sum :=
    sum_coareaWeight_initial_segment_eq_value_sq G y h_pos v hvV
  have hu_sum :=
    sum_coareaWeight_initial_segment_eq_value_sq G y h_pos u huV
  dsimp [levels] at hv_sum hu_sum
  have hsplit :
      ∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t =
        ∑ t ∈ levels.filter (fun t => t ≤ y u), coareaWeight levels t +
          ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
            coareaWeight levels t := by
    have hpartition :
        levels.filter (fun t => t ≤ y v) =
          (levels.filter (fun t => t ≤ y u)) ∪
            (levels.filter (fun t => y u < t ∧ t ≤ y v)) := by
      ext t
      by_cases hleu : t ≤ y u
      · simp [hleu, le_trans hleu huv]
      · have hltu : y u < t := lt_of_not_ge hleu
        simp [hleu, hltu]
    have hdisjoint :
        Disjoint (levels.filter (fun t => t ≤ y u))
          (levels.filter (fun t => y u < t ∧ t ≤ y v)) := by
      rw [Finset.disjoint_left]
      intro t ht_left ht_right
      have hleu : t ≤ y u := (Finset.mem_filter.mp ht_left).2
      have hltu : y u < t := (Finset.mem_filter.mp ht_right).2.1
      linarith
    rw [hpartition, Finset.sum_union hdisjoint]
  linarith

lemma regular_level_volume_as_vertex_sum (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (y : α → ℝ)
    (t : ℝ) :
    (((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ)) =
      ∑ v ∈ G.vertexFinset, if t ≤ y v then (d : ℝ) else 0 := by
  calc
    (((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ))
        = (d : ℝ) * ((G.vertexFinset.filter (fun v => y v ≥ t)).card : ℝ) := by
          norm_num [Nat.cast_mul]
    _ = (d : ℝ) * ∑ v ∈ G.vertexFinset.filter (fun v => y v ≥ t), (1 : ℝ) := by
          rw [Finset.card_eq_sum_ones]
          norm_num
    _ = ∑ v ∈ G.vertexFinset.filter (fun v => y v ≥ t), (d : ℝ) := by
          rw [Finset.mul_sum]
          simp
    _ = ∑ v ∈ G.vertexFinset, if t ≤ y v then (d : ℝ) else 0 := by
          rw [Finset.sum_filter]

lemma cut_card_eq_edge_indicator_sum (G : SimpleGraph α) [Finite G.vertexSet] (U : Finset α) :
    ((Cut G U).card : ℝ) =
      ∑ e ∈ G.edgeFinset, if e ∈ Cut G U then (1 : ℝ) else 0 := by
  have hfilter : {e ∈ G.edgeFinset | e ∈ Cut G U} = Cut G U := by
    ext e
    simp [Cut]
  calc
    ((Cut G U).card : ℝ) = ∑ e ∈ Cut G U, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]
      norm_num
    _ = ∑ e ∈ G.edgeFinset, if e ∈ Cut G U then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter, hfilter]

lemma edge_mem_level_cut_of_ge_lt (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    {u v : α} {t : ℝ} (he : s(u, v) ∈ G.edgeFinset)
    (hu : t ≤ y u) (hv : y v < t) :
    s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) := by
  have huV : u ∈ G.vertexFinset := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
  have hvV : v ∈ G.vertexFinset := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
  rw [Cut, Finset.mem_filter]
  refine ⟨he, ?_⟩
  refine ⟨u, ?_, Sym2.mem_mk_left u v, v, ?_, Sym2.mem_mk_right u v⟩
  · exact Finset.mem_filter.mpr ⟨huV, hu⟩
  · exact Finset.mem_sdiff.mpr ⟨hvV, by
      intro hv_mem
      have hv_ge : t ≤ y v := (Finset.mem_filter.mp hv_mem).2
      linarith⟩

lemma edge_mem_level_cut_of_lt_ge (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    {u v : α} {t : ℝ} (he : s(u, v) ∈ G.edgeFinset)
    (hu : y u < t) (hv : t ≤ y v) :
    s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) := by
  have hcut :
      s(v, u) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) :=
    edge_mem_level_cut_of_ge_lt G y (SimpleGraph.edgeSet_sym G u v he) hv hu
  simpa [Sym2.eq_swap] using hcut

lemma level_cut_edge_between_endpoints (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    {u v : α} {t : ℝ} (he : s(u, v) ∈ G.edgeFinset)
    (hcut : s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))) :
    (t ≤ y u ∧ y v < t) ∨ (t ≤ y v ∧ y u < t) := by
  rw [Cut, Finset.mem_filter] at hcut
  rcases hcut.2 with ⟨a, haU, ha_edge, b, hbNot, hb_edge⟩
  have ha_cases : a = u ∨ a = v := Sym2.mem_iff.mp ha_edge
  have hb_cases : b = u ∨ b = v := Sym2.mem_iff.mp hb_edge
  have ha_ge : t ≤ y a := (Finset.mem_filter.mp haU).2
  have hb_lt : y b < t := by
    have hb_not_mem : b ∉ G.vertexFinset.filter (fun w => y w ≥ t) :=
      (Finset.mem_sdiff.mp hbNot).2
    by_contra hnot
    have hb_ge : t ≤ y b := le_of_not_gt hnot
    have hbV : b ∈ G.vertexFinset := (Finset.mem_sdiff.mp hbNot).1
    exact hb_not_mem (Finset.mem_filter.mpr ⟨hbV, hb_ge⟩)
  rcases ha_cases with rfl | rfl <;> rcases hb_cases with rfl | rfl
  · linarith
  · exact Or.inl ⟨ha_ge, hb_lt⟩
  · exact Or.inr ⟨ha_ge, hb_lt⟩
  · linarith

lemma edge_level_cut_weight_sum_le_abs_sq_sub (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) {u v : α} (he : s(u, v) ∈ G.edgeFinset) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (if s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
      ≤ |y u ^ 2 - y v ^ 2| := by
  classical
  intro levels
  have huV : u ∈ G.vertexFinset := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
  have hvV : v ∈ G.vertexFinset := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
  have hleft :
      ∑ t ∈ levels,
          coareaWeight levels t *
            (if s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
        =
      ∑ t ∈ levels.filter
          (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))),
        coareaWeight levels t := by
    calc
      ∑ t ∈ levels,
          coareaWeight levels t *
            (if s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) then (1 : ℝ) else 0)
          = ∑ t ∈ levels,
              if s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) then
                coareaWeight levels t else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases hcut : s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))
            · simp [hcut]
            · simp [hcut]
      _ = ∑ t ∈ levels.filter
              (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))),
            coareaWeight levels t := by
            rw [← Finset.sum_filter]
  rw [hleft]
  by_cases huv : y u ≤ y v
  · have hsubset :
        levels.filter
            (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))) ⊆
          levels.filter (fun t => y u < t ∧ t ≤ y v) := by
      intro t ht
      have ht_levels : t ∈ levels := (Finset.mem_filter.mp ht).1
      have hcut : s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) :=
        (Finset.mem_filter.mp ht).2
      rcases level_cut_edge_between_endpoints G y he hcut with hbad | hgood
      · linarith
      · exact Finset.mem_filter.mpr ⟨ht_levels, hgood.symm⟩
    have hle_sum :
        ∑ t ∈ levels.filter
            (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))),
          coareaWeight levels t ≤
        ∑ t ∈ levels.filter (fun t => y u < t ∧ t ≤ y v),
          coareaWeight levels t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro t ht_big ht_not_small
      have ht_level : t ∈ levels := (Finset.mem_filter.mp ht_big).1
      exact le_of_lt (coareaWeight_pos_of_pos_mem
        (positive_value_level_pos G y) ((Finset.mem_filter.mp ht_level).2))
    have hinterval :=
      sum_coareaWeight_between_vertex_values_eq_sq_sub G y h_pos huV hvV huv
    dsimp [levels] at hinterval
    rw [hinterval] at hle_sum
    have habs : |y u ^ 2 - y v ^ 2| = y v ^ 2 - y u ^ 2 := by
      rw [abs_of_nonpos (show y u ^ 2 - y v ^ 2 ≤ 0 by
        have hsq : y u ^ 2 ≤ y v ^ 2 := by
          have hmul : y u * y u ≤ y v * y v :=
            mul_le_mul huv huv (h_pos u) (h_pos v)
          nlinarith
        linarith)]
      ring
    rw [habs]
    exact hle_sum
  · have hvu : y v ≤ y u := le_of_not_ge huv
    have hsubset :
        levels.filter
            (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))) ⊆
          levels.filter (fun t => y v < t ∧ t ≤ y u) := by
      intro t ht
      have ht_levels : t ∈ levels := (Finset.mem_filter.mp ht).1
      have hcut : s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t)) :=
        (Finset.mem_filter.mp ht).2
      rcases level_cut_edge_between_endpoints G y he hcut with hgood | hbad
      · exact Finset.mem_filter.mpr ⟨ht_levels, hgood.symm⟩
      · linarith
    have hle_sum :
        ∑ t ∈ levels.filter
            (fun t => s(u, v) ∈ Cut G (G.vertexFinset.filter (fun w => y w ≥ t))),
          coareaWeight levels t ≤
        ∑ t ∈ levels.filter (fun t => y v < t ∧ t ≤ y u),
          coareaWeight levels t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro t ht_big ht_not_small
      have ht_level : t ∈ levels := (Finset.mem_filter.mp ht_big).1
      exact le_of_lt (coareaWeight_pos_of_pos_mem
        (positive_value_level_pos G y) ((Finset.mem_filter.mp ht_level).2))
    have hinterval :=
      sum_coareaWeight_between_vertex_values_eq_sq_sub G y h_pos hvV huV hvu
    dsimp [levels] at hinterval
    rw [hinterval] at hle_sum
    have habs : |y u ^ 2 - y v ^ 2| = y u ^ 2 - y v ^ 2 := by
      rw [abs_of_nonneg (show 0 ≤ y u ^ 2 - y v ^ 2 by
        have hsq : y v ^ 2 ≤ y u ^ 2 := by
          have hmul : y v * y v ≤ y u * y u :=
            mul_le_mul hvu hvu (h_pos v) (h_pos u)
          nlinarith
        exact sub_nonneg.mpr hsq)]
    rw [habs]
    exact hle_sum

noncomputable def edgeAbsSqDiff (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => |y u ^ 2 - y v ^ 2|, by
    intro u v
    dsimp
    rw [abs_sub_comm]
  ⟩

noncomputable def edgeEndpointSqSum (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => y u ^ 2 + y v ^ 2, by
    intro u v
    dsimp
    ring
  ⟩

noncomputable def edgeAbsDiff (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => |y u - y v|, by
    intro u v
    dsimp
    rw [abs_sub_comm]
  ⟩

noncomputable def edgeEndpointSum (y : α → ℝ) : Edge α → ℝ :=
  Sym2.lift ⟨fun u v => y u + y v, by
    intro u v
    dsimp
    ring
  ⟩

lemma edge_vertex_indicator_sum_eq_endpoint_sq_sum (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    {u v : α} (he : s(u, v) ∈ G.edgeFinset) :
    ∑ x ∈ G.vertexFinset, (if x ∈ s(u, v) then y x ^ 2 else 0) =
      y u ^ 2 + y v ^ 2 := by
  classical
  have huv_ne : u ≠ v := SimpleGraph.ne_of_mem_edgeSet G u v he
  have huV : u ∈ G.vertexFinset := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
  have hvV : v ∈ G.vertexFinset := G.incidence s(u, v) he v (Sym2.mem_mk_right u v)
  calc
    ∑ x ∈ G.vertexFinset, (if x ∈ s(u, v) then y x ^ 2 else 0)
        = ∑ x ∈ G.vertexFinset.filter (fun x => x ∈ s(u, v)), y x ^ 2 := by
          rw [← Finset.sum_filter]
    _ = ∑ x ∈ ({u, v} : Finset α), y x ^ 2 := by
          have hfilter : G.vertexFinset.filter (fun x => x ∈ s(u, v)) = ({u, v} : Finset α) := by
            ext x
            constructor
            · intro hx
              have hcases : x = u ∨ x = v := Sym2.mem_iff.mp (Finset.mem_filter.mp hx).2
              simpa using hcases
            · intro hx
              have hx_edge : x ∈ s(u, v) := by
                simpa [Sym2.mem_iff] using hx
              have hxV : x ∈ G.vertexFinset := by
                rcases Sym2.mem_iff.mp hx_edge with rfl | rfl
                · exact huV
                · exact hvV
              exact Finset.mem_filter.mpr ⟨hxV, hx_edge⟩
          rw [hfilter]
    _ = y u ^ 2 + y v ^ 2 := by
          rw [Finset.sum_pair huv_ne]

lemma edge_endpoint_sq_sum_eq_deg_norm (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ) :
    ∑ e ∈ G.edgeFinset, edgeEndpointSqSum y e = G.deg_norm y := by
  classical
  calc
    ∑ e ∈ G.edgeFinset, edgeEndpointSqSum y e
        = ∑ e ∈ G.edgeFinset, ∑ v ∈ G.vertexFinset, (if v ∈ e then y v ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          induction e using Sym2.ind
          case h u v =>
            simpa [edgeEndpointSqSum] using
              (edge_vertex_indicator_sum_eq_endpoint_sq_sum G y he).symm
    _ = ∑ v ∈ G.vertexFinset, ∑ e ∈ G.edgeFinset, (if v ∈ e then y v ^ 2 else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ v ∈ G.vertexFinset, ((#δ(G, v) : ℕ) : ℝ) * y v ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          calc
            ∑ e ∈ G.edgeFinset, (if v ∈ e then y v ^ 2 else 0)
                = ∑ e ∈ δ(G, v), y v ^ 2 := by
                  rw [← Finset.sum_filter]
            _ = ((#δ(G, v) : ℕ) : ℝ) * y v ^ 2 := by
                  rw [Finset.sum_const]
                  simp [nsmul_eq_mul]
    _ = G.deg_norm y := by
          rfl

lemma level_cut_sum_le_edge_abs_sq_diff_sum (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card ≤
      ∑ e ∈ G.edgeFinset, edgeAbsSqDiff y e := by
  classical
  intro levels
  calc
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card
        = ∑ t ∈ levels,
            coareaWeight levels t *
              (∑ e ∈ G.edgeFinset,
                if e ∈ Cut G (G.vertexFinset.filter (fun v => y v ≥ t)) then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [cut_card_eq_edge_indicator_sum]
    _ = ∑ t ∈ levels, ∑ e ∈ G.edgeFinset,
          coareaWeight levels t *
            (if e ∈ Cut G (G.vertexFinset.filter (fun v => y v ≥ t)) then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = ∑ e ∈ G.edgeFinset, ∑ t ∈ levels,
          coareaWeight levels t *
            (if e ∈ Cut G (G.vertexFinset.filter (fun v => y v ≥ t)) then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ G.edgeFinset, edgeAbsSqDiff y e := by
          apply Finset.sum_le_sum
          intro e he
          induction e using Sym2.ind
          case h u v =>
            simpa [edgeAbsSqDiff, levels] using
              edge_level_cut_weight_sum_le_abs_sq_sub G y h_pos he

lemma edge_abs_diff_sq_sum_eq_energy (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ) :
    ∑ e ∈ G.edgeFinset, (edgeAbsDiff y e) ^ 2 = G.energy y := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h u v =>
    simp [edgeAbsDiff, sq_abs]

lemma edge_endpoint_sum_sq_le_two_deg_norm (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ) :
    ∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2 ≤ 2 * G.deg_norm y := by
  calc
    ∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2
        ≤ ∑ e ∈ G.edgeFinset, 2 * edgeEndpointSqSum y e := by
          apply Finset.sum_le_sum
          intro e he
          induction e using Sym2.ind
          case h u v =>
            have hsq : (y u + y v) ^ 2 ≤ 2 * (y u ^ 2 + y v ^ 2) := by
              nlinarith [sq_nonneg (y u - y v)]
            simpa [edgeEndpointSum, edgeEndpointSqSum] using hsq
    _ = 2 * G.deg_norm y := by
          rw [← Finset.mul_sum, edge_endpoint_sq_sum_eq_deg_norm]

lemma edge_abs_sq_diff_sum_le_sqrt_energy_deg_norm (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    ∑ e ∈ G.edgeFinset, edgeAbsSqDiff y e ≤
      Real.sqrt (2 * G.energy y * G.deg_norm y) := by
  have hpoint :
      ∀ e ∈ G.edgeFinset, edgeAbsSqDiff y e ≤ edgeAbsDiff y e * edgeEndpointSum y e := by
    intro e he
    induction e using Sym2.ind
    case h u v =>
      simpa [edgeAbsSqDiff, edgeAbsDiff, edgeEndpointSum] using
        abs_sq_sub_sq_le_abs_sub_mul_add_of_nonneg (h_pos u) (h_pos v)
  have hcs :=
    sum_le_sqrt_mul_sqrt_of_le_mul (G.edgeFinset) (edgeAbsSqDiff y)
      (edgeAbsDiff y) (edgeEndpointSum y) hpoint
  have hA : ∑ e ∈ G.edgeFinset, (edgeAbsDiff y e) ^ 2 = G.energy y :=
    edge_abs_diff_sq_sum_eq_energy G y
  have hB : ∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2 ≤ 2 * G.deg_norm y :=
    edge_endpoint_sum_sq_le_two_deg_norm G y
  have hB_nonneg : 0 ≤ ∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2 := by
    exact Finset.sum_nonneg (by intro e he; exact sq_nonneg _)
  have hmul_sqrt :
      Real.sqrt (∑ e ∈ G.edgeFinset, (edgeAbsDiff y e) ^ 2) *
          Real.sqrt (∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2)
        ≤ Real.sqrt (2 * G.energy y * G.deg_norm y) := by
    rw [hA]
    have hB_sqrt :
        Real.sqrt (∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2) ≤
          Real.sqrt (2 * G.deg_norm y) :=
      Real.sqrt_le_sqrt hB
    have henergy_nonneg : 0 ≤ G.energy y := energy_nonneg G y
    have hsqrt_energy_nonneg : 0 ≤ Real.sqrt (G.energy y) := Real.sqrt_nonneg _
    calc
      Real.sqrt (G.energy y) *
          Real.sqrt (∑ e ∈ G.edgeFinset, (edgeEndpointSum y e) ^ 2)
          ≤ Real.sqrt (G.energy y) * Real.sqrt (2 * G.deg_norm y) := by
            exact mul_le_mul_of_nonneg_left hB_sqrt hsqrt_energy_nonneg
      _ = Real.sqrt (G.energy y * (2 * G.deg_norm y)) := by
            rw [Real.sqrt_mul henergy_nonneg]
      _ = Real.sqrt (2 * G.energy y * G.deg_norm y) := by
            ring_nf
  exact le_trans hcs hmul_sqrt

/-- Vertex-side layer-cake formula for the canonical positive levels of `y`.
With `w t = t^2 - pred(t)^2`, summing the level volumes recovers the
degree norm. -/
lemma level_coarea_volume_identity (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
      G.deg_norm y := by
  classical
  intro levels
  calc
    ∑ t ∈ levels,
        coareaWeight levels t *
          ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ)
        = ∑ t ∈ levels,
            coareaWeight levels t *
              (∑ v ∈ G.vertexFinset, if t ≤ y v then (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [regular_level_volume_as_vertex_sum]
    _ = ∑ t ∈ levels, ∑ v ∈ G.vertexFinset,
            coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = ∑ v ∈ G.vertexFinset, ∑ t ∈ levels,
            coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ v ∈ G.vertexFinset, (d : ℝ) * y v ^ 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          have hpoint :=
            sum_coareaWeight_initial_segment_eq_value_sq G y h_pos v hv
          dsimp [levels] at hpoint
          calc
            ∑ t ∈ levels, coareaWeight levels t * (if t ≤ y v then (d : ℝ) else 0)
                = ∑ t ∈ levels, if t ≤ y v then coareaWeight levels t * (d : ℝ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  by_cases hle : t ≤ y v
                  · simp [hle]
                  · simp [hle]
            _ = ∑ t ∈ levels.filter (fun t => t ≤ y v),
                    coareaWeight levels t * (d : ℝ) := by
                  rw [← Finset.sum_filter]
            _ = (∑ t ∈ levels.filter (fun t => t ≤ y v), coareaWeight levels t) * (d : ℝ) := by
                  rw [Finset.sum_mul]
            _ = (d : ℝ) * y v ^ 2 := by
                  rw [hpoint]
                  ring
    _ = G.deg_norm y := by
          rw [deg_norm_eq_sum_reg G y d h_reg]

/-- Edge-side coarea estimate for the canonical positive levels of `y`.
The weighted count of threshold cuts is bounded by the Cauchy-Schwarz
quantity `sqrt (2 * energy * deg_norm)`. -/
lemma level_coarea_cut_bound (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (y : α → ℝ)
    (h_pos : ∀ v, 0 ≤ y v) :
    let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
    ∑ t ∈ levels,
        coareaWeight levels t *
          (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card ≤
      Real.sqrt (2 * G.energy y * G.deg_norm y) := by
  intro levels
  exact
    (level_cut_sum_le_edge_abs_sq_diff_sum G y h_pos).trans
      (edge_abs_sq_diff_sum_le_sqrt_energy_deg_norm G y h_pos)

noncomputable def normalizedSupportedOrthogonal (G : SimpleGraph α) [Finite G.vertexSet] : Set (α → ℝ) :=
  {x | (∀ v, v ∉ G.vertexFinset → x v = 0) ∧
    x ∈ orthogonalVectors G ∧
    G.deg_norm x = 1}

lemma edgeSet_empty_of_regular_zero (G : SimpleGraph α) [Finite G.vertexSet]
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = 0) :
    G.edgeFinset = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.ind
  case h u v =>
    have huV : u ∈ G.vertexFinset := G.incidence s(u, v) he u (Sym2.mem_mk_left u v)
    have hinc : s(u, v) ∈ δ(G,u) := by
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_mk_left u v⟩
    have hcard_pos : 0 < #δ(G,u) := Finset.card_pos.mpr ⟨s(u, v), hinc⟩
    have hzero : #δ(G,u) = 0 := h_reg u huV
    omega

lemma R_values_eq_singleton_zero_of_regular_zero (G : SimpleGraph α) [Finite G.vertexSet] [Finite α]
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = 0) (hV : 2 ≤ #G.vertexFinset) :
    R_values G = {0} := by
  classical
  have hE : G.edgeFinset = ∅ := edgeSet_empty_of_regular_zero G h_reg
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hx, rfl⟩
    simp [rayleighQuotient, hE]
  · intro hr
    simp only [Set.mem_singleton_iff] at hr
    subst r
    have hcard : 1 < (G.vertexFinset).card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    let x : α → ℝ := fun v => if v = a then (1 : ℝ) else if v = b then (-1 : ℝ) else 0
    refine ⟨x, ?_, ?_⟩
    · constructor
      · rw [show G.vertexFinset.sum (fun v => (deg(G,v) : ℝ) * x v) =
            ∑ v ∈ G.vertexFinset, (0 : ℝ) * x v by
          apply Finset.sum_congr rfl
          intro v hv
          rw [h_reg v hv]
          norm_num]
        simp
      · exact ⟨a, ha, by simp [x]⟩
    · simp [rayleighQuotient, hE]

lemma deg_norm_pos_of_supported_orthogonal_of_regular_pos (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ)
    (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    {x : α → ℝ} (hx : x ∈ orthogonalVectors G) :
    0 < G.deg_norm (restrictToVertexSet G x) := by
  classical
  have hy : restrictToVertexSet G x ∈ orthogonalVectors G :=
    orthogonalVectors_restrictToVertexSet G x hx
  rcases hy with ⟨_, hy_ne⟩
  rw [deg_norm_eq_sum_reg G (restrictToVertexSet G x) d h_reg, ← Finset.mul_sum]
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero h_d_pos
  · exact sum_sq_pos G (restrictToVertexSet G x) hy_ne

lemma normalizedSupportedOrthogonal_isCompact (G : SimpleGraph α) [Finite G.vertexSet] [Finite α] (d : ℕ)
    (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    IsCompact (normalizedSupportedOrthogonal G) := by
  classical
  haveI := Fintype.ofFinite α
  haveI : ProperSpace (α → ℝ) := FiniteDimensional.proper ℝ (α → ℝ)
  let K : Set (α → ℝ) := normalizedSupportedOrthogonal G
  have hsupport : IsClosed {x : α → ℝ | ∀ v, v ∉ G.vertexFinset → x v = 0} := by
    let Z : Set (α → ℝ) := ⋂ v : α, ⋂ (_ : v ∉ G.vertexFinset), {x : α → ℝ | x v = 0}
    have hZ : IsClosed Z := by
      apply isClosed_iInter
      intro v
      apply isClosed_iInter
      intro hv
      exact isClosed_eq (continuous_apply v) continuous_const
    have hZE : Z = {x : α → ℝ | ∀ v, v ∉ G.vertexFinset → x v = 0} := by
      ext x
      simp [Z]
    simpa [hZE] using hZ
  have horthClosed :
      IsClosed {x : α → ℝ | G.vertexFinset.sum (fun v => (deg(G,v) : ℝ) * x v) = 0} := by
    apply isClosed_eq _ continuous_const
    apply continuous_finset_sum
    intro v hv
    exact continuous_const.mul (continuous_apply v)
  have hnormClosed : IsClosed {x : α → ℝ | G.deg_norm x = 1} := by
    apply isClosed_eq _ continuous_const
    unfold deg_norm
    apply continuous_finset_sum
    intro v hv
    exact continuous_const.mul ((continuous_apply v).pow 2)
  have hclosed : IsClosed K := by
    have hK_eq : K = {x : α → ℝ | (∀ v, v ∉ G.vertexFinset → x v = 0)} ∩
        {x : α → ℝ | G.vertexFinset.sum (fun v => (deg(G,v) : ℝ) * x v) = 0} ∩
        {x : α → ℝ | G.deg_norm x = 1} := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hsupp, ⟨horth, hne⟩, hnorm⟩
        exact ⟨⟨hsupp, horth⟩, hnorm⟩
      · intro hx
        rcases hx with ⟨⟨hsupp, horth⟩, hnorm⟩
        refine ⟨hsupp, ⟨horth, ?_⟩, hnorm⟩
        by_contra hnone
        push Not at hnone
        have hzero_norm : G.deg_norm x = 0 := by
          unfold deg_norm
          apply Finset.sum_eq_zero
          intro v hv
          simp [hnone v hv]
        have hnorm_eq : G.deg_norm x = 1 := hnorm
        linarith
    rw [hK_eq]
    exact (hsupport.inter horthClosed).inter hnormClosed
  have hbounded : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : α → ℝ)]
    refine ⟨1, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Pi.norm_def]
    change (Finset.univ.sup fun b => ‖x b‖₊) ≤ (1 : NNReal)
    apply Finset.sup_le_iff.mpr
    intro v hv
    by_cases hvV : v ∈ G.vertexFinset
    · have hdeg : G.deg_norm x = ∑ u ∈ G.vertexFinset, (d : ℝ) * x u ^ 2 :=
        deg_norm_eq_sum_reg G x d h_reg
      have hnorm : G.deg_norm x = 1 := hx.2.2
      have hsum_eq : (d : ℝ) * ∑ u ∈ G.vertexFinset, x u ^ 2 = 1 := by
        rw [Finset.mul_sum]
        exact hdeg.symm.trans hnorm
      have hterm_le_sum : x v ^ 2 ≤ ∑ u ∈ G.vertexFinset, x u ^ 2 := by
        exact Finset.single_le_sum (fun u hu => sq_nonneg (x u)) hvV
      have hd_ge_one : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_d_pos)
      have hsum_nonneg : 0 ≤ ∑ u ∈ G.vertexFinset, x u ^ 2 :=
        Finset.sum_nonneg (by intro u hu; exact sq_nonneg _)
      have hsum_le_one : ∑ u ∈ G.vertexFinset, x u ^ 2 ≤ 1 := by
        have hd_nonneg : (0 : ℝ) ≤ d := by positivity
        nlinarith
      have hsq_le : x v ^ 2 ≤ 1 := le_trans hterm_le_sum hsum_le_one
      have habs_le : |x v| ≤ 1 := by
        rw [← sq_le_sq₀ (abs_nonneg _) zero_le_one]
        simpa [sq_abs] using hsq_le
      exact NNReal.coe_le_coe.mp (by simpa [Real.norm_eq_abs] using habs_le)
    · have hxv : x v = 0 := hx.1 v hvV
      exact NNReal.coe_le_coe.mp (by simp [hxv])
  exact hbounded.isCompact_closure.of_isClosed_subset hclosed subset_closure

lemma continuous_rayleighQuotient_on_normalizedSupportedOrthogonal (G : SimpleGraph α) [Finite G.vertexSet] :
    ContinuousOn (fun x : α → ℝ => G.rayleighQuotient x)
      (normalizedSupportedOrthogonal G) := by
  classical
  unfold SimpleGraph.rayleighQuotient
  apply ContinuousOn.div
  · apply Continuous.continuousOn
    apply continuous_finset_sum
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      simpa using ((continuous_apply u).sub (continuous_apply v)).pow 2
  · apply Continuous.continuousOn
    apply continuous_finset_sum
    intro v hv
    exact continuous_const.mul ((continuous_apply v).pow 2)
  · intro x hx
    have hnorm : G.deg_norm x = 1 := hx.2.2
    unfold SimpleGraph.deg_norm at hnorm
    rw [hnorm]
    norm_num

lemma R_values_eq_rayleigh_image_normalizedSupportedOrthogonal (G : SimpleGraph α) [Finite G.vertexSet] [Finite α]
    (d : ℕ) (h_d_pos : d ≠ 0) (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    R_values G =
      (fun x : α → ℝ => G.rayleighQuotient x) '' normalizedSupportedOrthogonal G := by
  classical
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hxorth, rfl⟩
    let y0 := restrictToVertexSet G x
    let n := G.deg_norm y0
    let c : ℝ := (Real.sqrt n)⁻¹
    let y : α → ℝ := fun v => c * y0 v
    have hn_pos : 0 < n := by
      exact deg_norm_pos_of_supported_orthogonal_of_regular_pos G d h_d_pos h_reg hxorth
    have hc_ne : c ≠ 0 := by
      unfold c
      exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hn_pos))
    have hy0orth : y0 ∈ orthogonalVectors G :=
      orthogonalVectors_restrictToVertexSet G x hxorth
    refine ⟨y, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro v hv
        simp [y, y0, restrictToVertexSet, hv]
      · rcases hy0orth with ⟨hy0_sum, hy0_ne⟩
        constructor
        · unfold y
          calc
            ∑ v ∈ G.vertexFinset, (deg(G,v) : ℝ) * (c * y0 v)
                = c * ∑ v ∈ G.vertexFinset, (deg(G,v) : ℝ) * y0 v := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro v hv
                  ring
            _ = 0 := by rw [hy0_sum, mul_zero]
        · rcases hy0_ne with ⟨v, hv, hyv⟩
          exact ⟨v, hv, by simp [y, hc_ne, hyv]⟩
      · have hnorm_mul := deg_norm_mul G y0 c
        have hcn : c ^ 2 * n = 1 := by
          unfold c
          have hs_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
          field_simp [hs_ne]
          rw [Real.sq_sqrt (le_of_lt hn_pos)]
        calc
          G.deg_norm y = G.deg_norm (fun v => c * y0 v) := rfl
          _ = c ^ 2 * G.deg_norm y0 := hnorm_mul
          _ = c ^ 2 * n := rfl
          _ = 1 := hcn
    · have hy_rq : G.rayleighQuotient y = G.rayleighQuotient x := by
        calc
          G.rayleighQuotient y = G.rayleighQuotient (fun v => c * y0 v) := rfl
          _ = G.rayleighQuotient y0 := rayleighQuotient_mul G y0 hc_ne
          _ = G.rayleighQuotient x := rayleighQuotient_restrictToVertexSet G x
      exact hy_rq
  · intro hr
    rcases hr with ⟨x, hxK, rfl⟩
    exact ⟨x, hxK.2.1, rfl⟩

/-- Level-set coarea counting for the sweep proof.  The finite set `levels`
and positive weights `w` are shared with `volume_coarea_counting` below. -/
lemma level_coarea_counting (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (y : α → ℝ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d)
    (h_pos : ∀ v, 0 ≤ y v)
    (h_y_pos : ∃ v ∈ G.vertexFinset, 0 < y v) :
    ∃ levels : Finset ℝ, ∃ w : ℝ → ℝ,
      levels.Nonempty ∧
      (∀ t ∈ levels, 0 < t) ∧
      (∀ t ∈ levels, 0 < w t) ∧
      (∀ t ∈ levels, (G.vertexFinset.filter (fun v => y v ≥ t)).Nonempty) ∧
      (∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card ≤
        Real.sqrt (2 * G.energy y * G.deg_norm y)) ∧
      (∑ t ∈ levels, w t * ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
        G.deg_norm y) := by
  classical
  let levels := (G.vertexFinset.image y).filter (fun t => 0 < t)
  let w := coareaWeight levels
  refine ⟨levels, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact positive_value_levels_nonempty G y h_y_pos
  · exact positive_value_level_pos G y
  · intro t ht
    exact coareaWeight_pos_of_pos_mem (positive_value_level_pos G y) ((Finset.mem_filter.mp ht).2)
  · exact positive_value_level_set_nonempty G y
  · simpa [levels, w] using level_coarea_cut_bound G d y h_pos
  · simpa [levels, w] using level_coarea_volume_identity G d y h_reg h_pos

/-- Cauchy-Schwarz step in the sweep proof, converting the coarea numerator
bound into a Rayleigh-quotient bound. -/
lemma coarea_bound_to_rayleigh (G : SimpleGraph α) [Finite G.vertexSet] (y : α → ℝ)
    (d : ℕ) (levels : Finset ℝ) (w : ℝ → ℝ)
    (h_norm_pos : 0 < G.deg_norm y)
    (h_level_bound :
      ∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card ≤
        Real.sqrt (2 * G.energy y * G.deg_norm y))
    (h_volume :
      ∑ t ∈ levels, w t * ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) =
        G.deg_norm y) :
    ∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card ≤
      Real.sqrt (2 * G.rayleighQuotient y) *
        ∑ t ∈ levels, w t * ((d * (G.vertexFinset.filter (fun v => y v ≥ t)).card : ℕ) : ℝ) := by
  rw [h_volume, rQ_eq_energy_div_norm]
  have h_norm_nonneg : 0 ≤ G.deg_norm y := le_of_lt h_norm_pos
  have h_energy_nonneg : 0 ≤ G.energy y := energy_nonneg G y
  have h_norm_ne : G.deg_norm y ≠ 0 := ne_of_gt h_norm_pos
  have h_sqrt_eq :
      Real.sqrt (2 * G.energy y * G.deg_norm y) =
        Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := by
    have h_factor_nonneg : 0 ≤ 2 * (G.energy y / G.deg_norm y) := by
      exact mul_nonneg (by norm_num) (div_nonneg h_energy_nonneg h_norm_nonneg)
    calc
      Real.sqrt (2 * G.energy y * G.deg_norm y)
          = Real.sqrt ((2 * (G.energy y / G.deg_norm y)) *
              (G.deg_norm y * G.deg_norm y)) := by
            congr 1
            field_simp [h_norm_ne]
      _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) *
            Real.sqrt (G.deg_norm y * G.deg_norm y) := by
            exact Real.sqrt_mul h_factor_nonneg (G.deg_norm y * G.deg_norm y)
      _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := by
            rw [Real.sqrt_mul_self h_norm_nonneg]
  calc
    ∑ t ∈ levels, w t * (Cut G (G.vertexFinset.filter (fun v => y v ≥ t))).card
        ≤ Real.sqrt (2 * G.energy y * G.deg_norm y) := h_level_bound
    _ = Real.sqrt (2 * (G.energy y / G.deg_norm y)) * G.deg_norm y := h_sqrt_eq


end GraphLib
