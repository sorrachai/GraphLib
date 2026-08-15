import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Tree.Basic
import GraphAlgorithms.SimpleGraphs.Walk


set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

structure ParentTree (α : Type*) where
  vertexSet : Finset α
  parent : α -> α
  level : α -> ℕ
  incidence : ∀ v ∈ vertexSet, parent v ∈ vertexSet
  ordering : ∀ v ∈ vertexSet, level v > 0 → level (parent v) < level v
  root : ∀  v ∈ vertexSet, level v = 0 ↔ v = parent v


open Finset Walk VertexSeq

namespace ParentTree 
abbrev Edge := Sym2

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "Vₚ(" G ")" => vertexSet G

abbrev EdgeSet (G : ParentTree α) : Finset (Edge α) := 
   G.vertexSet |> .image (fun p => s(p, G.parent p)) 
   |> .filter (fun e => ¬ e.IsDiag)

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "Eₚ(" G ")" => EdgeSet G


abbrev NeighbourSet (G : ParentTree α) (v : α) : Finset α := 
   (Vₚ(G).filter (fun p => G.parent p = v)  ∪ {G.parent v}) \ {v}


/-- `Nₚ(G,v)` denotes the neighbours of a vertex `v` in graph `G`. -/
scoped notation "Nₚ(" G "," v ")" => NeighbourSet G v

abbrev IncidentEdgeSet (G : ParentTree α) (s : α) [DecidableEq α] :
  Finset (Edge α) := Nₚ(G,s) |> .image (fun p => s(p, s))

/-- `δₚ(G,v)` denotes the `edge-incident-set` of a vertex `v` in graph `G`. -/
scoped notation "δₚ(" G "," v ")" => IncidentEdgeSet G v

/-- `degree(G,v)` denotes the degree of `v` in graph `G`. -/
scoped notation "degₚ(" G "," v ")" => #δₚ(G, v)


abbrev appendNodes (G : ParentTree α) (new_nodes : Finset α)
  (edges : α → α) (h : ∀ v ∈ new_nodes, edges v ∈ Vₚ(G)) : ParentTree α :=
    {
      vertexSet := G.vertexSet ∪ new_nodes,
      parent :=  fun v => if v ∈ G.vertexSet then G.parent v else edges v,
      level :=  fun v => if v ∈ G.vertexSet then G.level v else (G.level (edges v) + 1),
      incidence := by have := G.incidence; grind,
      root := by have := G.root; grind,
      ordering := by  have := G.ordering; have := G.incidence; grind
    }


section ParentTreeLemmas

lemma edge_inclusion (G : ParentTree α) (u v : α) (hv : v ∈ Nₚ(G,u)) :
   u = G.parent v ∨ v = G.parent u := by grind


@[grind →] lemma edge_parent (G : ParentTree α) (u v : α) (hv : v ∈ Nₚ(G,u)) : 
    G.level v < G.level u → v = G.parent u := by
      intro hq
      simp only [mem_sdiff, union_singleton, mem_insert, mem_filter, mem_singleton] at hv
      obtain ⟨ha , hb⟩ := hv
      rcases ha with hl | hr
      · exact hl
      · by_cases hlvl : G.level u = 0
        · grind
        · have hord := G.ordering v hr.left (by have := G.root v hr.left; grind)
          grind

@[grind →] lemma edge_antisymm_iff (G : ParentTree α) (u v : α) (hu : u ∈ Vₚ(G)) (hv :v ∈ Vₚ(G)):
    u ∈ Nₚ(G, v) ↔  u ∈ Nₚ(G, v) := by 
    simp only [mem_sdiff, union_singleton, mem_insert, mem_filter, mem_singleton] at *

@[grind →] lemma edge_antisymm (G : ParentTree α) (u v : α) (hu : u ∈ Vₚ(G))  (hv : v ∈ Nₚ(G,u)):
     u ∈ Nₚ(G, v) := by
    simp only [mem_sdiff, union_singleton, mem_insert, mem_filter, mem_singleton] at *
    grind


@[grind →] lemma edge_imp_in_v (G : ParentTree α) (u v : α) (hu : u ∈ Vₚ(G))  (hv : v ∈ Nₚ(G,u)):
      v ∈ Vₚ(G):= by
    simp only [mem_sdiff, union_singleton, mem_insert, mem_filter, mem_singleton] at *
    obtain ⟨ha, hb⟩ := hv
    rcases ha
    · have := G.incidence u hu  
      grind
    · grind



lemma reverse_list_iff_reverse {α : Type*} (sq : VertexSeq α) :
    sq.toList.reverse = sq.reverse.toList := by
      induction sq with 
        | singleton =>
          simp [VertexSeq.toList]
        | cons =>
          simp [VertexSeq.toList, w_ih]
          grind

lemma inverse_of_path_is_still_Path {α : Type*} (w : Walk α)
  (hw : IsPath w) : w.reverse.IsPath := by 
  simp [Walk.IsPath] at hw
  simp only [IsPath, support, Walk.reverse]
  rw [← reverse_list_iff_reverse]
  have h := hw.reverse
  grind

lemma prepend_append_eq_append_prepend {α : Type*} (w : Walk α) (u v : α)
  (hu : w.head ≠ u) (hv : v ≠ w.tail) :
    (w.prepend_vertex u hu).append_single v (by grind) = 
      (w.append_single v hv).prepend_vertex u (by simp [append_single]; grind) := by 
    simp only [append_single, prepend_vertex]
    haveI := con_tail_eq w.seq
    grind
  



lemma append_reverse_eq_reverse_prepend {α : Type*} (w : Walk α) (u : α)
  (h : u ≠ w.tail) :
    (w.append_single u h).reverse =  w.reverse.prepend_vertex u (by grind) := by
      simp only [Walk.reverse, append_single, prepend_vertex]
      grind




@[simp, grind →] lemma walk_cons_is_walk {α : Type*} (w : Walk α)
  (s : VertexSeq α) (v : α) (hp : IsPath w)
  (hw : w.seq = s.cons v) : IsWalk s := by 
  revert w hw
  induction s with
    | singleton => grind
    | cons =>
      intro w_1 h_w_1 heq
      have h : IsWalk (w.cons v) := by 
        simp [IsPath, heq, VertexSeq.toList] at h_w_1
        exact IsWalk.cons w v (by have h := w_1.valid ; simp [heq] at h; grind) (by grind)
      have := w_ih 
      exact IsWalk.cons w v_1 (by grind) (by grind)

@[grind ←] lemma prepend_dropHead {α : Type*} (vs : VertexSeq α) (u : α) :
    ((VertexSeq.singleton u).append vs).dropHead = vs := by
      induction vs with
        | singleton => simp [VertexSeq.append, VertexSeq.dropHead]
        | cons =>
          grind

@[grind =] lemma reverse_drop_head_eq_drop_tail_reverse {α : Type*} (vs : VertexSeq α) :
    vs.reverse.dropHead.head =  vs.dropTail.reverse.head := by
      induction vs with
        | singleton =>
          simp [dropHead,VertexSeq.dropTail]
        | cons =>
          simp [VertexSeq.dropTail, VertexSeq.reverse,
            prepend_dropHead]

@[grind =] lemma reverse_drop_head_head_eq_drop_tail_tail_reverse {α : Type*} (vs : VertexSeq α) :
    vs.reverse.dropHead.head = vs.dropTail.tail := by
      induction vs with
        | singleton =>
          simp [dropHead,VertexSeq.dropTail]
        | cons =>
          simp [VertexSeq.dropTail, VertexSeq.reverse,
            prepend_dropHead]

@[grind =] lemma reverse_support_ind_head {α : Type*} (vs : VertexSeq α) :
    vs.reverse.toList.get (⟨0, by grind⟩) = vs.head := by
      induction vs with
        | singleton =>
          simp [VertexSeq.toList]
        | cons =>
          simp [VertexSeq.toList,VertexSeq.reverse]
          grind

@[grind =] lemma reverse_length_eq_length {α : Type*} (vs : VertexSeq α) :
      vs.reverse.length = vs.length := by
        induction vs <;> grind



@[grind =] lemma reverse_support_ind_tail {α : Type*} (vs : VertexSeq α) :
    vs.reverse.toList.get 
      (⟨vs.length, by rw [toList_length_eq vs.reverse, reverse_length_eq_length]; omega⟩) 
        = vs.tail := by
      induction vs with
        | singleton =>
          simp [VertexSeq.toList]
        | cons =>
          have : 1 + w.length = (w.reverse.toList).length := by 
            simp [toList_length_eq w.reverse]
            grind
          simp only [VertexSeq.reverse, VertexSeq.length, List.get_eq_getElem, toList_append,
            VertexSeq.toList, con_tail_eq]
          rw [List.getElem_append_right]
          ·  grind
          ·  grind
          



@[grind =] lemma reverse_drop_head_head_eq_drop_tail {α : Type*} (vs : VertexSeq α) :
    vs.reverse.dropHead = vs.dropTail.reverse := by
      induction vs with
        | singleton =>
          simp [dropHead,VertexSeq.dropTail]
        | cons =>
          simp [VertexSeq.dropTail, VertexSeq.reverse, prepend_dropHead]
          

@[grind =] lemma droptail_drophead_head_eq_drophead_head {α : Type*} (vs : VertexSeq α) :
    vs.length ≥ 2 → vs.dropHead.head = vs.dropTail.dropHead.head := by
      induction vs with
        | singleton => grind
        | cons =>
          intro h
          simp [VertexSeq.dropTail]
          grind

@[grind =] lemma list_pos_tail_is_0 {α : Type*} (vs : VertexSeq α) :
     vs.toList.get (⟨0, by rw [toList_length_eq vs]; omega⟩) = vs.tail := by
      induction vs with
        | singleton => grind
        | cons => grind

@[grind =] lemma list_pos_head_is_n {α : Type*} (vs : VertexSeq α) :
     vs.toList.get (⟨vs.length, by rw [toList_length_eq vs]; omega⟩) = vs.head := by
      induction vs with
        | singleton => grind
        | cons => grind


@[grind =] lemma list_pos_drop_tail_is_1 {α : Type*} (vs : VertexSeq α)
    (h : vs.length ≥ 1) :
     vs.toList.get (⟨1, by rw [toList_length_eq vs]; omega⟩) = vs.dropTail.tail := by
      induction vs with
        | singleton => grind
        | cons =>
          simp [VertexSeq.dropTail]
          grind

@[grind =] lemma list_pos_drop_head_is_minus1 {α : Type*} (vs : VertexSeq α)
    (h : vs.length ≥ 1) :
     vs.toList.get (⟨vs.length - 1, by rw [toList_length_eq vs]; omega⟩) = vs.dropHead.head := by
      induction vs with
        | singleton => grind
        | cons =>
          by_cases he: w.length = 0
          · -- w is singleton
            have hsingle : ∃ u, w = VertexSeq.singleton u := by grind
            grind
          · -- w is not singleton
            have h2 : (w.cons v).length ≥ 2 := by grind
            have hdrop := droptail_drophead_head_eq_drophead_head (w.cons v) h2
            have happ := w_ih (by grind) 
            simp [VertexSeq.toList]
            have hsimp : (v :: w.toList).get (⟨(w.cons v).length - 1, by grind⟩) = 
              w.toList.get (⟨w.length - 1, by grind⟩) := by grind
            simp at hsimp
            simp at happ
            rw [hsimp, happ]
            grind

@[grind →, grind ←] lemma tail_nin_walk_nodup {α : Type*} (vs : Walk α) :
    vs.length >= 1 → vs.IsPath → vs.tail ∉ vs.dropTail.support := by
      simp only [Walk.length, ge_iff_le, IsPath, support, Walk.tail]
      induction vs.seq with
        | singleton => rw [VertexSeq.length] ; omega
        | cons => 
          intro hlen hcons
          grind


@[grind ←] lemma prepend_vertex_seq {α : Type*} (vs : VertexSeq α) (v: α):
     (vs.cons v).reverse = (VertexSeq.singleton v).append vs.reverse := by
      induction vs with
        | singleton => grind
        | cons => grind

@[grind ←] lemma prepend_vertex_dropTail {α : Type*} (vs : VertexSeq α) (v: α):
     vs.length ≥ 1 → ((VertexSeq.singleton v).append vs).dropTail = 
      (VertexSeq.singleton v).append vs.dropTail := by
      induction vs with
        | singleton => grind
        | cons => grind

@[grind =] lemma dropTail_rev_cons_head_eq_reverse {α : Type*} (vs : VertexSeq α):
     vs.length ≥ 1 → vs.reverse.dropTail.cons vs.head = vs.reverse := by
      induction vs with
        | singleton => grind
        | cons => grind

@[grind →, grind ←] lemma remove_head_or_tail_invariance {α : Type*} (vs : Walk α) :
    vs.length >= 2 →  vs.dropTail.reverse.dropTail.reverse = vs.reverse.dropTail.reverse.dropTail := by
      simp only [Walk.length, ge_iff_le, Walk.reverse, Walk.ext_iff]
      induction vs.seq with
        | singleton => rw [VertexSeq.length] ; omega
        | cons => 
          intro hlen
          rw [VertexSeq.length] at hlen
          replace hlen : 1 ≤ w.length := by omega
          cases Nat.le_iff_lt_or_eq.mp hlen with
          | inl => 
            have w_ih_app :=  w_ih (by omega)
            rw [VertexSeq.dropTail, prepend_vertex_seq w v, 
              prepend_vertex_dropTail w.reverse v (by grind), ]
            have := prepend_vertex_seq w.reverse.dropTail v
            grind
          | inr => 
            have hdc : ∃ a,  ∃ b, (VertexSeq.singleton a).cons b = w := by grind
            obtain ⟨a,b,hab⟩ := hdc
            grind

end ParentTreeLemmas
end ParentTree 



