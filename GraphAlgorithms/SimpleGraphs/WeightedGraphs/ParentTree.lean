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
  

/-inductive IsMonotonePathInG (G : ParentTree α) (dir : Direction) : Walk α → Prop
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
      ))-/

@[grind, simp] def VertexSeq.IsMonotone (G : ParentTree α) (dir : Direction) : VertexSeq α → Prop
      | .singleton  _ => True
      | .cons w' u => 
          let ord := match dir with
            | Direction.Increasing =>  G.level w'.tail < G.level u
            | Direction.Decreasing =>  G.level w'.tail > G.level u
          ord ∧  VertexSeq.IsMonotone G dir w'

@[grind, simp] def Walk.IsMonotone (w : Walk α) (G : ParentTree α) (dir : Direction) : Prop :=
  VertexSeq.IsMonotone G dir w.seq



/-lemma cons_trail_inG (G : ParentTree α) (w w' : Walk α) (u : α) (hu : u ≠ w'.tail)
  (hw : IsWalkIn G w) (hw_eq : w = w'.append_single u hu) : IsWalkIn G w' := by
    cases hw   with
      | singleton v hv =>
        simp [Walk.append_single] at hw_eq
      | cons s v hwalk hv =>
        simp [Walk.append_single] at hw_eq
        have h1 := Walk.ext_iff.mpr hw_eq.left
        rw [h1] at hwalk
        exact hwalk-/

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

lemma increasing_monotone_path_tail_semilast (G : ParentTree α)
  (w : Walk α) (hw : IsWalkIn G w) (hmono : Walk.IsMonotone w G (Direction.Increasing))
  (hlen : w.length > 0) :
    G.level w.dropTail.tail < G.level w.tail := by
      induction hw with
        | singleton =>
          simp [Walk.tail, VertexSeq.dropTail] at hlen
        | cons =>
          simp [Walk.append_single] at hmono
          simp only [Walk.tail, VertexSeq.dropTail, append_single, con_tail_eq]
          grind



lemma increasing_monotone_path_tail_semilast_parent (G : ParentTree α) (w : Walk α)
  (hw : IsWalkIn G w) (hmono : Walk.IsMonotone w G (Direction.Increasing))
  (hlen : w.length > 0) :
     w.dropTail.tail = G.parent w.tail := by
      induction hw with
        | singleton =>
          simp [Walk.tail, VertexSeq.dropTail] at hlen
        | cons =>
          simp [Walk.append_single] at hmono
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
    Walk.IsMonotone w G Direction.Increasing := by
    induction hw with
    | singleton v hv => grind
    | cons w' u hw hedge hind => 
      simp [Walk.append_single]
      by_cases hln : w'.length = 0
      · --Eq 0
        cases hw with
          | singleton =>
            simp at *
            simp [Walk.append_single, VertexSeq.dropHead] at h_head
            simp only [Walk.tail, VertexSeq.tail] at hedge
            simp at hedge
            obtain ⟨hor, hand⟩  := hedge
            rcases hor with hl | hr
            · -- Levels will not match
              have v_level := (Iff.not (G.root v hv)).mpr (by grind)
              have u_level := (Iff.not (G.root u (by grind))).mpr (by grind)
              have hord_1 := G.ordering v hv (by grind) 
              rw [← hl] at hord_1
              have hord_2 := G.ordering u (by grind)  (by grind)
              rw [← h_head] at hord_1
              grind
            · -- Normal edge
              have u_level := (Iff.not (G.root u (by grind))).mpr (by grind)
              have hord_2 := G.ordering u (by grind)  (by grind)
              grind
          | cons => 
            simp [Walk.length, Walk.append_single] at hln
            grind

      · -- GT 0
        have hparent : G.parent w'.seq.dropHead.head = w'.head := by
          cases hw with 
            | singleton p => 
               grind
            | cons w' => 
              simp [Walk.append_single]
              simp [Walk.append_single] at h_head
              grind
        have h_app := hind (by
          simp [Walk.IsPath]; simp [Walk.append_single,Walk.IsPath] at hp; grind)
          (by omega) hparent
        rw [and_comm]
        constructor
        · exact h_app
        · -- Prove that must be increasing using uniquenss
          have h_semi := increasing_monotone_path_tail_semilast_parent G w' hw h_app (by omega)
          have h_inc := increasing_monotone_path_tail_semilast G w' hw h_app (by omega)
          simp at hedge
          obtain ⟨hor, hand⟩ := hedge
          rcases hor with hl | hr
          · -- Should be monotonic
            --have his_w_in : IsWalkIn G (w'.append_single u (by grind)) := sorry
            --have h_inc_t := increasing_monotone_path_tail_semilast G 
            --  (w'.append_single u (by grind)) his_w_in h_app (by omega)
            have he : w'.dropTail.tail = u :=  by grind
            simp [Walk.IsPath] at hp
            have hsemi_ne_next : w'.dropTail.tail ≠ u := by 
              simp [Walk.append_single, VertexSeq.toList] at hp
              by_contra h_cc
              have := VertexSeq.dropTail_tail_mem_toList w'.seq
              grind
            grind
          · -- Is monotonic
            have u_level := (Iff.not (G.root u (by grind))).mpr (by grind)
            have hord := G.ordering u (by grind) (by grind)
            grind


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

@[grind →, grind ←] lemma IsMonotonePathInG.cons_front (G : ParentTree α)
  (w : Walk α) (dir : Direction)
    (u : α) (hu : u ∈ Nₚ(G,w.head))
    (huv : match dir with
        | Direction.Increasing => G.level w.head > G.level u
        | Direction.Decreasing => G.level u > G.level w.head)
    (h : Walk.IsMonotone w G dir) (hw : IsWalkIn G w):
    Walk.IsMonotone (w.prepend_vertex u (by grind)) G dir  := by
      induction hw with
        | singleton =>
          simp only [prepend_vertex, VertexSeq.append]
          let w_single : Walk α := ⟨.singleton u, .singleton u⟩
          have h_u_in : u ∈ Vₚ(G) := edge_imp_in_v G v u hv hu
          have h_walk_single : IsWalkIn G w_single :=
            IsWalkIn.singleton u h_u_in
          simp only [Walk.head,VertexSeq.head] at hu
          have h_v_neigh : v ∈ Nₚ(G, u) := edge_antisymm G v u hv hu
          simp [Walk.head] at huv
          grind
        | cons => 
          simp only [Walk.append_single, Walk.head, con_head_eq] at hu
          have hu_up : w_1.head ≠ u := by grind
          let w_1_app := w_1.prepend_vertex u hu_up 
          rw [← prepend_append_eq_append_prepend w_1 u u_1 hu_up]
          have hedg' : u_1 ∈ Nₚ(G, w_1_app.tail) := by grind
          have hw_tail : w_1.tail = w_1_app.tail := by grind
          have hw_head : (w_1.append_single u_1 (by grind)).head = w_1.head := by 
            simp [Walk.append_single]
            have := con_head_eq w_1.seq u_1
            grind
          simp [Walk.append_single]
          simp only [Walk.head, append_single, con_head_eq, gt_iff_lt] at huv
          simp [Walk.append_single] at h
          have h_app := hw_ih (by grind) huv (by grind)
          grind
          


lemma append_reverse_eq_reverse_prepend {α : Type*} (w : Walk α) (u : α)
  (h : u ≠ w.tail) :
    (w.append_single u h).reverse =  w.reverse.prepend_vertex u (by grind) := by
      simp only [Walk.reverse, append_single, prepend_vertex]
      grind


theorem IsWalkInG.flip (G : ParentTree α) (w : Walk α)
    (h : IsWalkIn G w) : IsWalkIn G w.reverse := by
      induction h with
      | singleton =>
        simp only [Walk.reverse, singleton_reverse_eq]
        exact  IsWalkIn.singleton v hv
      | cons =>
        rw [append_reverse_eq_reverse_prepend]
        grind


theorem IsMonotonePathInG.flip (G : ParentTree α) (w : Walk α) (dir : Direction)
    (h : IsWalkIn G w)
    (hmono : Walk.IsMonotone w G dir) : Walk.IsMonotone w.reverse G (dir.opposite)  := by
      
      induction h with
      | singleton =>
        simp only [Walk.reverse, singleton_reverse_eq]
        grind
      | cons =>
        rw [append_reverse_eq_reverse_prepend]
        have hw_ih_app :=  hw_ih (by simp [Walk.IsMonotone, Walk.append_single] at hmono;grind)
        exact IsMonotonePathInG.cons_front G w_1.reverse dir.opposite u  (by grind)
          (by cases dir <;> 
              simp [Walk.IsMonotone, Walk.append_single] at hmono <;> 
              simp [Direction.opposite, Walk.tail] <;>
              grind)
           hw_ih_app (IsWalkInG.flip G w_1 hw)
        


@[simp, grind] def sequence_mono_decomp (G : ParentTree α) :
      VertexSeq α → VertexSeq α × VertexSeq α 
    | .singleton v =>  ⟨.singleton v, .singleton v⟩
    | .cons w' v =>  if G.level w'.tail < G.level v then -- Path is increasing
        (sequence_mono_decomp G w').map id (fun wl => wl.cons v)
      else -- If path stopped increasing
        ⟨w'.cons v, .singleton  v⟩

@[grind ←] lemma walk_ne_mem {α : Type*} (G : ParentTree α) (w : VertexSeq α) (v : α)
  (hn : v ∉ w.toList) :
    v ∉ (sequence_mono_decomp G w).fst.toList ∧ v ∉
      (sequence_mono_decomp G w).snd.toList := by
        induction w using sequence_mono_decomp.induct G with
        | case1  => grind
        | case2 => grind
        | case3 => grind
          


lemma walk_decomp_is_walk (G: ParentTree α) (w : Walk α) (hw : w.IsPath):
    IsWalk (sequence_mono_decomp G w.seq).fst
      ∧ IsWalk (sequence_mono_decomp G w.seq).snd := by
        set w_pair := sequence_mono_decomp G w.seq with hpair
        induction hc: w.seq generalizing w with
          | singleton =>
              simp [hc] at *
              grind
          | cons w' v =>
              have h_walk := w.valid
              simp [hc]  at h_walk
              cases h_walk with
                | cons =>
                  by_cases ht: G.level w'.tail <  G.level v
                  · -- Positive Branch
                    simp [hc, ht, Prod.map] at hpair
                    let wₚ : Walk α := (⟨w', hw_1⟩)
                    have hw_path : wₚ.IsPath := by
                      simp [Walk.IsPath, hc, VertexSeq.toList] at hw
                      simp [Walk.IsPath]
                      grind

                    have h_app := w_ih wₚ hw_path (by grind) (by grind)
                    constructor
                    · -- Decreasing sequence
                      grind
                    · --Increasing sequence
                      --simp [wₚ] at h_app
                      simp [hpair]
                      have hv : v ∉ w'.toList := by grind
                      have hv_ext : v ∉ w_pair.2.dropTail.toList := by 
                        simp [w_pair, hc, ht, VertexSeq.dropTail]
                        have h:= walk_ne_mem G w' v hv
                        grind
                      
                      exact IsWalk.cons (sequence_mono_decomp G w').snd v
                        (by grind) (by grind)
                  · -- Negative branch
                    simp [sequence_mono_decomp, hc, ht] at hpair
                    let wₚ : Walk α := (⟨w', hw_1⟩)
                    have hw_path : wₚ.IsPath := by
                      simp [Walk.IsPath, hc, VertexSeq.toList] at hw
                      simp [Walk.IsPath]
                      grind
                    have h_app := w_ih wₚ hw_path (by grind) (by grind)
                    grind







lemma IsMonotonePathInG.path_decomposition
  (G : ParentTree α) (w : Walk α) (hw : IsWalkIn G w) (hp : w.IsPath) :
      ∃ w1 w2 : Walk α, ∃ h , w = w1.append w2 h ∧ 
        Walk.IsMonotone w1 G Direction.Decreasing  ∧
          Walk.IsMonotone w2 G Direction.Increasing := by 
            let w1 := List.takeWhile₂ (fun x y => G.level x > G.level y) 
              (w.head :: w.seq.toList) (w.seq.toList)
            
            sorry
          
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



