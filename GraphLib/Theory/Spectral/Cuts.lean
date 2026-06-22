import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

import GraphLib.Graph.Basic
import GraphLib.Graph.Finite


-- Cuts (undirected simple)
-- Authors: Weixuan Yuan

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

open GraphLib

noncomputable def Cut (G : SimpleGraph α) (U : Finset α) [Finite G.vertexSet] :
  Finset (Sym2 α) := {e ∈ G.edgeFinset | ∃ u ∈ U, u ∈ e ∧ ∃ v ∈ G.vertexFinset \ U, v ∈ e}

--Weight function
class LinearOrderedAddCommMonoid (R : Type*) extends
  LinearOrder R, -- total order
  AddCommMonoid R, -- commutative addition
  IsOrderedAddMonoid R -- addition is monotone

variable {R : Type*} [LinearOrderedAddCommMonoid R]

open Finset BigOperators

namespace Cuts


noncomputable def weight (G : SimpleGraph α) (U : Finset α) (w : Sym2 α → R) [Finite G.vertexSet] : R :=
  Finset.sum (Cut G U) w


lemma cut_submodular (G : SimpleGraph α) (U W : Finset α)
    (w : Sym2 α → R) (w_pos : ∀ e, 0 ≤ w e) [Finite G.vertexSet] :
  weight G (U ∩ W) w + weight G (U ∪ W) w ≤ weight G U w + weight G W w := by
  have h1 : Cut G (U ∩ W) ⊆ Cut G U ∪ Cut G W := by grind [Cut]
  have h2 : Cut G (U ∪ W) ⊆ Cut G U ∪ Cut G W := by grind [Cut]
  have h3 : Cut G (U ∩ W) ∩ Cut G (U ∪ W) ⊆ Cut G U ∩ Cut G W := by grind [Cut]
  have h4 : (Cut G (U ∩ W)) ∪ (Cut G (U ∪ W)) ⊆ (Cut G U) ∪ (Cut G W) := by apply union_subset h1 h2
  clear h1 h2
  repeat unfold weight
  rw[<-Finset.sum_union_inter]
  nth_rw 2 [<-Finset.sum_union_inter]
  have h1 : Finset.sum (Cut G (U ∩ W) ∪ Cut G (U ∪ W)) w ≤ Finset.sum (Cut G U ∪ Cut G W) w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h4
    grind [Cut]
  have h2 : Finset.sum (Cut G (U ∩ W) ∩ Cut G (U ∪ W)) w ≤ Finset.sum (Cut G U ∩ Cut G W) w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h3
    grind [Cut]
  apply add_le_add h1 h2


def is_st_cut (G : SimpleGraph α) (U : Finset α) (s t : α) [Finite G.vertexSet] : Prop :=
  s ∈ U ∧ t ∉ U ∧ U.Nonempty ∧ U ⊂ G.vertexFinset

def is_st_mincut (G : SimpleGraph α) (U : Finset α) (s t : α) (w : Sym2 α → R)
    [Finite G.vertexSet] : Prop :=
  is_st_cut G U s t ∧ ∀ W : Finset α, is_st_cut G W s t → weight G U w ≤ weight G W w

noncomputable instance (G : SimpleGraph α) (s t : α) [Finite G.vertexSet] :
    DecidablePred (fun U : Finset α => is_st_cut G U s t) := by
  intro U; unfold is_st_cut; infer_instance

noncomputable def st_cuts (G : SimpleGraph α) (s t : α) [Finite G.vertexSet] : Finset (Finset α) :=
  G.vertexFinset.powerset.filter (fun U => is_st_cut G U s t)

noncomputable def st_mincut_value (G : SimpleGraph α) [Finite G.vertexSet]
    (s t : α) (w : Sym2 α → R) (h : (st_cuts G s t).Nonempty) : R := by
  classical
  apply Finset.nonempty_def.1 at h;
  refine ((st_cuts G s t).image (fun U => weight G U w)).min' ?_
  rcases h with ⟨U, hU⟩
  exact ⟨weight G U w, by
    exact Finset.mem_image_of_mem (fun X => weight G X w) hU⟩

lemma st_min_cut {G : SimpleGraph α} [Finite G.vertexSet]
    {U : Finset α} {s t : α} {w : Sym2 α → R} (h : (st_cuts G s t).Nonempty) :
  is_st_mincut G U s t w ↔ is_st_cut G U s t ∧ weight G U w = st_mincut_value G s t w h := by
  constructor
  · intro hmin;  simp_all only [is_st_mincut, true_and]
    apply le_antisymm
    · apply le_min'; grind [st_cuts]
    · apply min'_le; grind [st_cuts, is_st_cut]
  · rintro ⟨h1,h2⟩
    unfold is_st_mincut; simp_all only [true_and]
    rintro W hW; rw[<-h2]
    unfold st_mincut_value at h2; simp_all only; apply min'_le
    grind [st_cuts, is_st_cut]


end Cuts
