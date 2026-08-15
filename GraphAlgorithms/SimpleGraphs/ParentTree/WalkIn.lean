import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Tree.Basic
import GraphAlgorithms.SimpleGraphs.Walk
import GraphAlgorithms.SimpleGraphs.ParentTree.Basic

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]


open Finset Walk VertexSeq ParentTree

inductive IsWalkIn (G : ParentTree α) : Walk α → Prop
  | singleton (v : α) (hv : v ∈ G.vertexSet)
    : IsWalkIn G ⟨.singleton v, .singleton v⟩
  | cons (w : Walk α) (u : α)
      (hw   : IsWalkIn G w)
      (hedg : u ∈ Nₚ(G, w.tail))
    : IsWalkIn G (w.append_single u (by grind))

lemma is_walk_in_tree_last (G : ParentTree α) (w : Walk α) (h : IsWalkIn G w) : 
       w.tail ∈ Vₚ(G) := by
        induction h with
          | singleton => 
            grind
          | cons => 
            simp at hedg
            simp [Walk.append_single] at *
            simp [Walk.tail]
            have hinc := G.incidence
            grind

@[grind →] lemma is_walk_in_tree_support (G : ParentTree α) (w : Walk α) (h : IsWalkIn G w) : 
    ∀ u ∈ w.support, u ∈ Vₚ(G) := by
        induction h with
          | singleton => 
            grind
          | cons => 
            intro u hu
            simp at hedg
            simp [Walk.append_single] at *
            have hinc := G.incidence
            grind

lemma is_walk_in_tree_last_semilast (G : ParentTree α) (w : Walk α) (h : IsWalkIn G w)
    (hlen : w.length > 0) : 
    w.tail ∈ Nₚ(G, w.dropTail.tail) ∧  w.dropTail.tail ∈ Nₚ(G, w.tail) := by
        cases h with
          | singleton => 
            grind
          | cons => 
            constructor
            · simp [Walk.append_single, Walk.tail, ] at *
              simp at hedg
              grind
            · simp only [append_single, gt_iff_lt, Walk.tail, con_tail_eq, VertexSeq.dropTail,
              ] at *
              simp only [Walk.tail, mem_sdiff, union_singleton, mem_insert, mem_filter,
                mem_singleton] at hedg
              obtain ⟨ha , hb ⟩ := hedg
              simp only [Walk.tail] at hedg
              have hin := is_walk_in_tree_last G w_1 hw
              simp only [Walk.tail] at hin
              exact edge_antisymm G w_1.seq.tail u hin hedg

@[grind →, grind ←] lemma IsWalkIn.cons_front (G : ParentTree α) (w : Walk α)
  (u : α) (hu : u ∈ Nₚ(G,w.head)) (h : IsWalkIn G w) : 
    IsWalkIn G (w.prepend_vertex u (by grind)) := by
    induction h with
      | singleton =>
        simp only [prepend_vertex, VertexSeq.append]
        let w_single : Walk α := ⟨.singleton u, .singleton u⟩
        have h_u_in : u ∈ Vₚ(G) := edge_imp_in_v G v u hv hu
        have h := IsWalkIn.singleton u h_u_in
        have h_v_neigh : v ∈ Nₚ(G, u) := edge_antisymm G v u hv hu
        exact IsWalkIn.cons w_single v h h_v_neigh
      | cons =>
          simp only [Walk.append_single, Walk.head, con_head_eq] at hu
          have hu_up : w_1.head ≠ u := by grind
          let w_1_app := w_1.prepend_vertex u hu_up
          rw [← prepend_append_eq_append_prepend]
          exact IsWalkIn.cons  w_1_app u_1 (hw_ih (by grind)) (by grind)

@[grind →] theorem IsWalkIn.flip (G : ParentTree α) (w : Walk α)
    (h : IsWalkIn G w) : IsWalkIn G w.reverse := by
      induction h with
      | singleton =>
        simp only [Walk.reverse, singleton_reverse_eq]
        exact  IsWalkIn.singleton v hv
      | cons =>
        rw [append_reverse_eq_reverse_prepend]
        grind

theorem IsWalkIn.dropTail (G : ParentTree α) (w : Walk α)
    (h : IsWalkIn G w) : IsWalkIn G w.dropTail := by
      induction h with
      | singleton =>
        rw [Walk.dropTail]
        exact  IsWalkIn.singleton v hv
      | cons =>
        rw [Walk.append_single,Walk.dropTail]
        grind


lemma is_walk_in_tree_first_second (G : ParentTree α) (w : Walk α) (h : IsWalkIn G w)
    (hlen : w.length > 0) : 
    w.head ∈ Nₚ(G, w.seq.dropHead.head) := by
        have h1 := h.flip
        have hs := is_walk_in_tree_last_semilast  G w.reverse h1 (by grind) 
        have := reverse_drop_head_head_eq_drop_tail_tail_reverse w.seq
        grind


