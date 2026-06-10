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

abbrev Edge := Sym2

open Finset Walk VertexSeq

namespace ParentTree 

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


inductive IsWalkIn (G : ParentTree α) : Walk α → Prop
  | singleton (v : α) (hv : v ∈ G.vertexSet)
    : IsWalkIn G ⟨.singleton v, .singleton v⟩
  | cons (w : Walk α) (u : α)
      (hw   : IsWalkIn G w)
      (hedg : u ∈ Nₚ(G, w.tail))
    : IsWalkIn G (w.append_single u (by grind))

section ParentTreeLemmas

lemma edge_inclusion (G : ParentTree α) (u v : α) (hv : v ∈ Nₚ(G,u)) :
   u = G.parent v ∨ v = G.parent u := by grind


inductive Direction
  | Increasing
  | Decreasing

def Direction.opposite : Direction -> Direction 
  | .Increasing => Direction.Decreasing
  | .Decreasing => Direction.Increasing
  

inductive IsMonotonePathInG (G : ParentTree α) (dir : Direction) : Walk α → Prop
  | singleton (v : α) (hv: v ∈ G.vertexSet)
    : IsMonotonePathInG G dir ⟨.singleton v, .singleton v⟩
  | cons (w : Walk α) (u : α) 
      (hw   : IsWalkIn G w)
      (hedg : u ∈ Nₚ(G, w.tail))
      (hdir : match dir with
        | Direction.Increasing => G.level w.tail <  G.level u
        | Direction.Decreasing => G.level u <  G.level w.tail
        )
      (h_mono_w : IsMonotonePathInG G dir w)
    : IsMonotonePathInG G dir (w.append_single u (by 
      simp at hedg 
      exact hedg.right
      ))

lemma cons_trail_inG (G : ParentTree α) (w w' : Walk α) (u : α) (hu : u ≠ w'.tail)
  (hw : IsWalkIn G w) (hw_eq : w = w'.append_single u hu) : IsWalkIn G w' := by
    cases hw   with
      | singleton v hv =>
        simp [Walk.append_single] at hw_eq
      | cons s v hwalk hv =>
        simp [Walk.append_single] at hw_eq
        have h1 := Walk.ext_iff.mpr hw_eq.left
        rw [h1] at hwalk
        exact hwalk

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

lemma is_walk_in_tree_support (G : ParentTree α) (w : Walk α) (h : IsWalkIn G w) : 
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

lemma increasing_monotone_path_tail_semilast (G : ParentTree α) (w : Walk α)
  (hw : IsMonotonePathInG G (Direction.Increasing) w) (hlen : w.length > 0) :
    G.level w.dropTail.tail < G.level w.tail := by
      induction hw with
        | singleton =>
          simp [Walk.tail, VertexSeq.dropTail] at hlen
        | cons =>
          simp only at hdir
          simp only [Walk.tail, VertexSeq.dropTail, append_single, con_tail_eq]
          exact hdir



lemma increasing_monotone_path_tail_semilast_parent (G : ParentTree α) (w : Walk α)
  (hw : IsMonotonePathInG G (Direction.Increasing) w) (hlen : w.length > 0) :
     w.dropTail.tail = G.parent w.tail := by
      induction hw with
        | singleton =>
          simp [Walk.tail, VertexSeq.dropTail] at hlen
        | cons =>
          simp only at hdir
          simp only [Walk.tail, VertexSeq.dropTail, append_single, con_tail_eq]
          have hin := is_walk_in_tree_last G w_1 hw_1
          have h_parent := edge_parent G u w_1.tail
           (edge_antisymm G w_1.tail u hin hedg)
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



lemma IsMonotonePathInG.from_head_imp_increasing (G : ParentTree α) (w : Walk α)
  (hw : IsWalkIn G w) (hp : w.IsPath) (hlen : w.length ≥ 1)
  (h_head : G.parent (w.seq.dropHead.head) = w.seq.head) : 
    IsMonotonePathInG G Direction.Increasing w
    := by
    induction hw with
    | singleton v hv => 
      exact IsMonotonePathInG.singleton v hv
    | cons w' u hw hedge hind => 
        by_cases hlen' : w'.length = 0
        · -- Single elment is trivial case
          have h_single : ∃ u, w'.seq = VertexSeq.singleton u := by
            simp [Walk.length] at hlen'
            have heq := VertexSeq.toList_length_eq w'.seq
            simp [hlen'] at heq
            apply List.length_eq_one_iff.mp at heq
            obtain ⟨a, ha⟩ := heq
            use a
            cases hP: w'.seq with 
              | singleton v => 
                simp [hP] at ha
                simp [VertexSeq.toList] at ha
                simp [ha]
              | cons v hv => 
                grind
          obtain ⟨s, hs⟩ := h_single
          simp [Walk.append_single, hs, VertexSeq.dropHead] at h_head 
          have hs_in : s ∈ Vₚ(G) := by
              rcases hw
              · simp at hs
                grind
              . simp [Walk.append_single] at hs
          exact IsMonotonePathInG.cons  (G := G) (dir := Direction.Increasing) w' u
            hw hedge  (by 
            have heq : w' = ⟨.singleton s, .singleton s⟩  := by 
              apply Walk.ext_iff.mpr
              simp [hs]
            simp
            cases hw with
              | singleton c => 
                simp [Walk.tail, VertexSeq.tail] at * 
                simp [Walk.tail] at hedge
                rcases hedge with hl | hr
                · have hlr : G.parent u = G.parent (G.parent c) := congrArg G.parent hl
                  simp [h_head] at hlr
                  by_cases hlvl : G.level c = 0
                  · apply (G.root c hv).mp at hlvl
                    grind
                  · 
                    simp [← hs] at h_head
                    have hord_app := G.ordering c hv (by omega)
                    have u_in:  u ∈ Vₚ(G):= (by 
                      have := G.incidence c hv
                      simp [hl]
                      grind
                      )
                    have v_level := (Iff.not (G.root u u_in)).mpr (by grind)
                    have hord_v_app := G.ordering u  u_in (by omega)
                    grind
                · -- righ branch
                  have v_level := (Iff.not (G.root u hr.left)).mpr (by grind)
                  have hord := G.ordering u hr.left (by omega)
                  grind
              | cons  => 
                simp [Walk.append_single] at heq
            ) (by 
                have := IsMonotonePathInG.singleton (dir := Direction.Increasing) s hs_in
                have heq : w' = ⟨.singleton s, .singleton s⟩  := by simp [Walk.ext_iff]; grind
                rw [heq]
                grind)
        · -- Gt one
          apply  Nat.ne_zero_iff_zero_lt.mp at hlen'
          apply  Nat.lt_iff_add_one_le.mp at hlen'
          simp at hlen'
          simp [VertexSeq.con_head_eq, Walk.append_single] at h_head
          have hseqhead : (w'.seq.cons u).dropHead.head = w'.seq.dropHead.head := by
            have hb := dropHead.eq_3 w'.seq u (by grind)
            grind
          simp [hseqhead] at h_head
          have hp' : w'.IsPath := by
            simp [Walk.IsPath]
            simp [Walk.append_single] at hp
            grind
          have happ := hind hp' hlen' h_head 
          have hdir := increasing_monotone_path_tail_semilast G w' happ hlen'
          have hin_semi := is_walk_in_tree_last_semilast G w' hw hlen' 
          have hdir_parent := edge_parent G w'.tail w'.dropTail.tail hin_semi.right hdir
          have hsemi_ne_next : w'.dropTail.tail ≠ u := by 
            simp [Walk.append_single, Walk.IsPath, VertexSeq.toList] at hp
            by_contra h_cc
            have := VertexSeq.dropTail_tail_mem_toList w'.seq
            grind

          -- Increasing step
          have hdir' : G.level w'.tail < G.level u := by 
            simp at hedge
            obtain ⟨ha, hb⟩ := hedge
            rcases ha with hl | hr
            · -- u parent tail (decreasing case)
              grind
            · --
              have h := G.ordering u hr.left (by grind)
              grind
          exact IsMonotonePathInG.cons (dir := Direction.Increasing) w' u hw hedge 
            (by grind) happ



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

@[grind →, grind ←] lemma IsMonotonePathInG.cons_front (G : ParentTree α) (w : Walk α) (dir : Direction)
    (u : α) (hu : u ∈ Nₚ(G,w.head))
    (huv : match dir with
        | Direction.Increasing => G.level w.head > G.level u
        | Direction.Decreasing => G.level u > G.level w.head)
    (h : IsMonotonePathInG G dir w) :
    IsMonotonePathInG G dir (w.prepend_vertex u (by grind)) := by
      induction h with
        | singleton =>
          simp only [prepend_vertex, VertexSeq.append]
          let w_single : Walk α := ⟨.singleton u, .singleton u⟩
          have h_u_in : u ∈ Vₚ(G) := edge_imp_in_v G v u hv hu
          have h := IsMonotonePathInG.singleton (dir := dir) u h_u_in
          have h_walk_single : IsWalkIn G w_single :=
            IsWalkIn.singleton u h_u_in
          simp only [Walk.head,VertexSeq.head] at hu
          have h_v_neigh : v ∈ Nₚ(G, u) := edge_antisymm G v u hv hu
          simp [Walk.head] at huv
          exact IsMonotonePathInG.cons (dir := dir) w_single v h_walk_single
            h_v_neigh (by grind) h
        | cons => 
          simp only [Walk.append_single, Walk.head, con_head_eq] at hu
          have hu_up : w_1.head ≠ u := by grind
          let w_1_app := w_1.prepend_vertex u hu_up
          rw [← prepend_append_eq_append_prepend]
          have hedg' : u_1 ∈ Nₚ(G, w_1_app.tail) := by grind
          have hw_tail : w_1.tail = w_1_app.tail := by grind
          have hw_head : (w_1.append_single u_1 (by grind)).head = w_1.head := by 
            simp [Walk.append_single]
            have := con_head_eq w_1.seq u_1
            grind
          rw [hw_tail] at hdir
          exact IsMonotonePathInG.cons w_1_app u_1 (by grind) hedg' hdir 
            (h_mono_w_ih  (by grind)  (by grind))



lemma append_reverse_eq_reverse_prepend {α : Type*} (w : Walk α) (u : α)
  (h : u ≠ w.tail) :
    (w.append_single u h).reverse =  w.reverse.prepend_vertex u (by grind) := by
      simp only [Walk.reverse, append_single, prepend_vertex]
      grind


theorem IsWathInG.flip (G : ParentTree α) (w : Walk α)
    (h : IsWalkIn G w) : IsWalkIn G w.reverse := by
      induction h with
      | singleton =>
        simp only [Walk.reverse, singleton_reverse_eq]
        exact  IsWalkIn.singleton v hv
      | cons =>
        rw [append_reverse_eq_reverse_prepend]
        grind


theorem IsMonotonePathInG.flip (G : ParentTree α) (w : Walk α) (dir : Direction)
    (h : IsMonotonePathInG G dir w) : IsMonotonePathInG G (dir.opposite) w.reverse := by
      induction h with
      | singleton =>
        simp only [Walk.reverse, singleton_reverse_eq]
        exact  IsMonotonePathInG.singleton (dir := dir.opposite) v hv
      | cons =>
        rw [append_reverse_eq_reverse_prepend]
        exact IsMonotonePathInG.cons_front G w_1.reverse dir.opposite u  (by grind)
          (by simp only [Walk.head_reverse, gt_iff_lt]; cases dir <;> exact hdir) h_mono_w_ih




lemma parent_tree_is_acyclic (G : ParentTree α) (w : Walk α)
  (hw : IsWalkIn G w) :
    ¬ IsCycle w := by
    intro hcontra
    obtain ⟨h_len, hse, hpath⟩ := hcontra
    let convPath := w.reverse.dropTail.reverse
    have h_convPath_isPath : convPath.IsPath :=  by
      simp [Walk.IsPath] at hpath
      simp [convPath, Walk.IsPath]




    sorry





end ParentTreeLemmas

end ParentTree 



