import GraphAlgorithms.SimpleGraphs.WeightedGraphs.WeightedSimpleGraphs
import GraphAlgorithms.SimpleGraphs.WeightedGraphs.Walk
import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

open Finset WeightedSimpleGraph Sym2

def is_connected (G : WeightedSimpleGraph α) : Prop :=
  ∀ u v: α , u ≠ v →  ∃ p: Walk α, Path.IsPathIn G p


@[simp, grind] def crossingEdges
    (G : WeightedSimpleGraph α)
    (frontier visited : Finset α) :
    Finset (Edge α) :=
  frontier.biUnion fun x =>
    G.edgeSet.filter fun e =>
      x ∈ e ∧ ∃ y ∈ visited, y ∈ e

@[simp] noncomputable def minimumWeightEdges
    (G : WeightedSimpleGraph α)
    (edges : Finset (Edge α))
    (h : edges.Nonempty) :
    Finset (Edge α) :=
  let minW :=
    (edges.image G.edgeWeight).min'
      (h.image G.edgeWeight)
  edges.filter fun e => G.edgeWeight e = minW


lemma crossing_to_min_weight_edges {α: Type* }(G : WeightedSimpleGraph α) (A : Finset (Edge α))
    (hA : A.Nonempty) : (minimumWeightEdges G A hA).Nonempty := by
  simp only [minimumWeightEdges, filter_nonempty_iff]
  have hmem := min'_mem (A.image G.edgeWeight) (hA.image G.edgeWeight)
  rw [mem_image] at hmem
  obtain ⟨e, he, hew⟩ := hmem
  exact ⟨e, he, hew⟩

noncomputable def disjointEdges'
    (edges : Finset (Edge α)) (acc : Finset (Edge α)) :
    Finset (Edge α) :=
  if h: edges.Nonempty then
    let x := h.choose
    if ∀ y ∈ acc, x.toFinset ∩ y.toFinset = ∅ then 
      disjointEdges' (edges \ {x}) (acc ∪ {x})
    else 
      acc
  else
    acc
  termination_by edges.card
  decreasing_by
    simp [Finset.Nonempty] at h
    have h1 : (edges \ {x}).card = edges.card - 1 := by grind
    have h2 : (edges).card ≥ 1 := by grind
    rw [h1]
    omega

inductive IsDisjointEdgeSet : Finset (Edge α) → Prop
  | empty
    : IsDisjointEdgeSet ∅
  | cons (A : Finset (Edge α)) (e : Edge α)
      (hw   : IsDisjointEdgeSet A)
      (hedg : ∀ y ∈ A, e.toFinset ∩ y.toFinset = ∅)
    : IsDisjointEdgeSet ({e} ∪ A)

lemma IsDisjointEdgeSet.nonempty {A : Finset (Edge α)} (h : IsDisjointEdgeSet A)
  (hne : A ≠ ∅) : A.Nonempty := by
  cases h with
  | empty => contradiction
  | cons A e hw hedg => exact ⟨e, Finset.mem_union_left _ (Finset.mem_singleton_self e)⟩

@[simp] noncomputable def disjointEdges
    (edges : Finset (Edge α)) :
    Finset (Edge α) :=
  disjointEdges' edges ∅

lemma disjoint_helper_inductive' (A : Finset (Edge α)) (acc : Finset (Edge α))
    (hacc : IsDisjointEdgeSet acc) :
    IsDisjointEdgeSet (disjointEdges' A acc) := by
  induction A, acc using disjointEdges'.induct with
  | case1 edges acc hne e h1 h2 =>
    rw [disjointEdges', dif_pos hne]
    unfold e at *
    simp only [union_singleton]
    split_ifs with hif
    · -- h1 holds
      have hm : IsDisjointEdgeSet ({e} ∪ acc) := IsDisjointEdgeSet.cons acc e hacc hif
      rw [Finset.union_comm] at hm
      have hp := h2 hm
      unfold e at *
      rwa [Finset.insert_eq, Finset.union_comm]
    ·  -- neg h1
      exact absurd h1 hif
  | case2 edges acc hne e h1 =>
    -- hempty : ¬edges.Nonempty
    rw [disjointEdges',dif_pos hne]
    unfold e at *
    grind
  | case3 edges acc hempty =>
    -- hempty : ¬edges.Nonempty
    rw [disjointEdges', dif_neg hempty]
    exact hacc

lemma disjointEdges_disjoint (A : Finset (Edge α)) :
    IsDisjointEdgeSet (disjointEdges A) := by
      rw [disjointEdges]
      exact disjoint_helper_inductive' A ∅ (IsDisjointEdgeSet.empty)
  
lemma disjoint_nonempty_imp_nonempty (A acc : Finset (Edge α)) (hA : A.Nonempty) :
    (disjointEdges' A acc).Nonempty := by
  induction A, acc using disjointEdges'.induct with
  | case1 edges acc hne e h1 h2 =>
    rw [disjointEdges', dif_pos hne]
    simp only [union_singleton]
    unfold e at *
    split_ifs with hcond
    · -- Positive branch 
      by_cases h_edge_single : edges = {e} 
      · -- Is Singleton
        have h_edge_choose : edges \ {e} = ∅ := by grind
        unfold e at *
        rw [h_edge_choose, disjointEdges']
        simp
      · -- Is not singleton
        have h_edge_card_gt2 : edges.card ≥ 2 := by
          by_contra hcontra
          push Not at  hcontra
          apply Nat.lt_succ_iff.mp at hcontra
          apply Nat.le_one_iff_eq_zero_or_eq_one.mp at hcontra
          cases hcontra
          · grind
          · have he : ∃ p : Edge α, edges = {p} := Finset.card_eq_one.mp h
            obtain ⟨p, hp⟩ := he
            have hpe : p = e := by grind
            rw [hpe] at hp
            exact h_edge_single hp
        grind
    · -- Neg case
      unfold e at *
      grind
  | case2 edges acc hne e h1 =>
    rw [disjointEdges', dif_pos hne]
    simp only [union_singleton]
    unfold e at *
    grind
  | case3 edges acc hne =>
    exact absurd hA hne

lemma sub_disjoint' (A : Finset (Edge α)) (acc : Finset (Edge α)):
  acc ⊆ disjointEdges' A acc := by
  induction A, acc using disjointEdges'.induct with
    | case1 edges acc hne e h1 =>
      rw [disjointEdges', dif_pos hne]
      unfold e at *
      simp only [union_singleton]
      rw [if_pos h1]
      grind
    | case2 edges acc hne e =>
      rw [disjointEdges', dif_pos hne]
      unfold e at *
      simp only [union_singleton]
      rw [if_neg h]
    | case3 edges acc hne =>
      rw [disjointEdges', dif_neg hne]
 

lemma disjoint'_sub (A : Finset (Edge α)) (acc : Finset (Edge α))
  : disjointEdges' A acc ⊆ A ∪ acc := by
  induction A, acc using disjointEdges'.induct with
    | case1 edges acc hne e h1 =>
      rw [disjointEdges', dif_pos hne]
      unfold e at *
      simp only [union_singleton]
      rw [if_pos h1]
      grind
    | case2 edges acc hne e =>
      rw [disjointEdges', dif_pos hne]
      unfold e at *
      simp only [union_singleton]
      grind
    | case3 edges acc hne =>
      rw [disjointEdges', dif_neg hne]
      grind

noncomputable def prim
    (G : WeightedSimpleGraph α)
    (edgeSet : Finset (Edge α))
    (frontier visited : Finset α)
    (hfront_sub : frontier ⊆  V(G))
    (hvisited_sub : visited ⊆  V(G))
    (h_disj : frontier ∩ visited = ∅)
    : Finset (Edge α) :=
  if frontier = ∅ then
    edgeSet
  else
    let crossing := crossingEdges G frontier visited

    if h : crossing.Nonempty then
      let chosen :=
        disjointEdges <|
          minimumWeightEdges G crossing h

      let newNodes :=
        chosen.biUnion fun e =>
          e.toFinset.filter (· ∉ visited)

      let visited' := visited ∪ newNodes

      let frontier' :=
        (frontier ∪ newNodes.biUnion (fun v => N(G, v))) \ visited'

      prim G (edgeSet ∪ chosen) frontier' visited' (by grind) (by
        set min_edges := minimumWeightEdges G crossing h with hmin
        have hmin_sub_crossing: min_edges ⊆ crossing := by
          simp [min_edges, crossing]
        have hchosen_sub_min: chosen ⊆ min_edges := by
          simp only [disjointEdges, chosen]
          have h := disjoint'_sub min_edges ∅
          simp only [union_empty] at h
          exact h
        have htrans := hchosen_sub_min.trans hmin_sub_crossing
        have hnew_nodes : newNodes ⊆ V(G) := by 
              simp only [biUnion_subset_iff_forall_subset, newNodes]
              intro e hedge
              have hvv := htrans hedge
              simp only [crossingEdges, mem_biUnion, mem_filter, crossing] at hvv
              obtain ⟨u, hx⟩ := hvv
              intro m hm
              simp at hm
              exact G.incidence e hx.right.left m hm.left
        grind
      ) (by grind)
    else
      edgeSet
termination_by (V(G) \ visited).card
decreasing_by
  set min_edges := minimumWeightEdges G crossing h
  have hmin_edge_ne: min_edges.Nonempty := crossing_to_min_weight_edges G crossing h
  have hchosen_ne: chosen.Nonempty := disjoint_nonempty_imp_nonempty min_edges ∅ hmin_edge_ne
  have hmin_sub_crossing: min_edges ⊆ crossing := by
    simp [min_edges, crossing]
  have hchosen_sub_min: chosen ⊆ min_edges := by
    simp only [disjointEdges, chosen]
    have h := disjoint'_sub min_edges ∅
    simp only [union_empty] at h
    exact h
  have htrans := hchosen_sub_min.trans hmin_sub_crossing
  have hnew_nodes : newNodes ⊆ V(G) := by 
    simp only [biUnion_subset_iff_forall_subset, newNodes]
    intro e hedge
    have hvv := htrans hedge
    simp only [crossingEdges, mem_biUnion, mem_filter, crossing] at hvv
    obtain ⟨u, hx⟩ := hvv
    intro m hm
    simp at hm
    exact G.incidence e hx.right.left m hm.left

  have hnew_node: ¬ newNodes ⊆ visited  := by
    intro h_contra
    obtain ⟨e', he⟩ := hchosen_ne
    simp only [biUnion_subset_iff_forall_subset, newNodes] at h_contra
    have h_crossing := htrans he
    simp only [crossingEdges, mem_biUnion, mem_filter, crossing] at h_crossing
    obtain ⟨m, hm⟩ := h_crossing
    have h_contra' : ∀ u, u ∈ {x ∈ toFinset e' | x ∉ visited} → u ∈ visited := (h_contra e' he)
    simp only [mem_filter, mem_toFinset, and_imp, _root_.not_imp_self] at h_contra'
    have hsimp := h_contra' m hm.right.right.left
    have hinter := Finset.mem_inter.mpr ⟨hm.left, hsimp⟩
    grind
  apply Finset.card_lt_card
  constructor
  ·  grind
  · intro hv
    have htwo_u := Finset.union_subset hvisited_sub hnew_nodes
    have hs_hs := (sdiff_subset_sdiff_iff_subset hvisited_sub htwo_u).mp hv
    grind


