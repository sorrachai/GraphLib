/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.VertexSeq

/-!
# Simple walks

A `SimpleWalk α` is a `VertexSeq α` whose consecutive vertices differ — i.e.
a non-stalling sequence. This file also provides the conversions to
`SimpleGraph` and `SimpleDiGraph` (the non-stalling property is exactly what
makes the resulting graph loopless).
-/

variable {α : Type*}

/-- A simple walk: a `VertexSeq` with no two consecutive vertices equal. -/
def SimpleWalk (α : Type*) := { w : VertexSeq α // w.nonstalling }

-- `VertexSeq.edges` and `VertexSeq.arcs` (the traversed edges/arcs) live in
-- `VertexSeq/Edges.lean`, since they are purely combinatorial.

namespace SimpleWalk

open GraphLib

/-! ## Basic accessors -/

/-- The underlying vertex sequence. -/
abbrev val (w : SimpleWalk α) : VertexSeq α := w.1

/-- The non-stalling proof. -/
@[simp, grind] lemma nonstalling (w : SimpleWalk α) : w.val.nonstalling := w.2

/-- The list of vertices visited by the walk. -/
abbrev support (w : SimpleWalk α) : List α := w.val.toList

/-- The unordered edges traversed by the walk. -/
abbrev edges (w : SimpleWalk α) : List (Sym2 α) := w.val.edges

/-- The directed arcs traversed by the walk. -/
abbrev arcs (w : SimpleWalk α) : List (α × α) := w.val.arcs

/-- The first vertex of the walk. -/
abbrev head (w : SimpleWalk α) : α := w.val.head

/-- The last vertex of the walk. -/
abbrev tail (w : SimpleWalk α) : α := w.val.tail

/-- The number of edges in the walk. -/
abbrev length (w : SimpleWalk α) : ℕ := w.val.length

/-- The walk has no repeated vertex (i.e. it is a path). -/
abbrev nodup (w : SimpleWalk α) : Prop := w.val.nodup

/-- The walk is closed: its first and last vertex coincide. -/
abbrev closed (w : SimpleWalk α) : Prop := w.val.closed

/-- A simple walk is, in particular, a vertex sequence. -/
instance : Coe (SimpleWalk α) (VertexSeq α) :=
  ⟨val⟩

/-! ## dropHead, dropTail -/

/-- Drop the first vertex of the simple walk (returns it unchanged when it is a
singleton). Removing an endpoint cannot introduce a stall. -/
def dropHead (w : SimpleWalk α) : SimpleWalk α :=
  ⟨w.val.dropHead, by have := w.nonstalling; grind⟩

/-- Drop the last vertex of the simple walk (returns it unchanged when it is a
singleton). Removing an endpoint cannot introduce a stall. -/
def dropTail (w : SimpleWalk α) : SimpleWalk α :=
  ⟨w.val.dropTail, by have := w.nonstalling; grind⟩

/-! ## append -/

/-- Concatenate two simple walks, keeping both joining vertices. The hypothesis
`p.tail ≠ q.head` ensures the junction does not create a stall. -/
def append (p q : SimpleWalk α) (h : p.val.tail ≠ q.val.head) : SimpleWalk α :=
  ⟨p.val.append q.val, by
    exact (VertexSeq.nonstalling_append p.val q.val).2
      ⟨p.nonstalling, q.nonstalling, h⟩⟩

/-- Concatenate two simple walks meeting at a shared vertex (`p.tail = q.head`),
dropping the duplicated joining vertex. -/
def glue (p q : SimpleWalk α) (h : p.val.tail = q.val.head) : SimpleWalk α :=
  if hp : p.val.length = 0 then
    q
  else
    ⟨p.val.dropTail.append q.val, by
      have hpns : p.val.dropTail.nonstalling :=
        VertexSeq.nonstalling_dropTail p.val p.nonstalling
      have hjoin : p.val.dropTail.tail ≠ q.val.head := by
        rw [← h]
        clear h q
        obtain ⟨s, hs⟩ := p
        induction s with
        | singleton v =>
            simp [VertexSeq.length] at hp
        | cons s v ih =>
            cases s with
            | singleton u =>
                simpa [VertexSeq.dropTail, VertexSeq.tail] using hs.2
            | cons t u =>
                simpa [VertexSeq.dropTail, VertexSeq.tail] using hs.2
      exact (VertexSeq.nonstalling_append p.val.dropTail q.val).2
        ⟨hpns, q.nonstalling, hjoin⟩⟩

/-! ## reverse -/

/-- Reverse a simple walk: the head becomes the tail and vice versa. Reversal
only swaps the order of the consecutive pairs, so non-stalling is preserved. -/
def reverse (w : SimpleWalk α) : SimpleWalk α :=
  ⟨w.val.reverse, by have := w.nonstalling; grind⟩

/-! ## prefixUntil, suffixFrom -/

/-- The prefix of `w` ending at the first occurrence of `v`, inclusive of that
vertex. The hypothesis guarantees such a vertex exists. A contiguous prefix of
a non-stalling walk is non-stalling. -/
def prefixUntil [DecidableEq α] (w : SimpleWalk α) (v : α) (h : v ∈ w.val) :
    SimpleWalk α :=
  ⟨w.val.prefixUntil v h, by grind⟩

/-- The suffix of `w` starting at the first occurrence of `v`, inclusive of that
vertex. The hypothesis guarantees such a vertex exists. A contiguous suffix of
a non-stalling walk is non-stalling. -/
def suffixFrom [DecidableEq α] (w : SimpleWalk α) (v : α) (h : v ∈ w.val) :
    SimpleWalk α :=
  ⟨w.val.suffixFrom v h, by grind⟩

/-! ## map -/

/-- Map a simple walk through an injective function. Injectivity ensures
distinct consecutive vertices stay distinct, so non-stalling is preserved. -/
def map {β : Type*} (f : α → β) (hf : Function.Injective f) (w : SimpleWalk α) :
    SimpleWalk β :=
  ⟨w.val.map f, by
    have hmap : ∀ s : VertexSeq α, s.nonstalling → (s.map f).nonstalling := by
      intro s hs
      induction s with
      | singleton v =>
          simp [VertexSeq.map, VertexSeq.nonstalling]
      | cons p v ih =>
          constructor
          · exact ih hs.1
          · intro h
            have hf_tail : f p.tail = f v := by
              simpa [VertexSeq.tail_map] using h
            exact hs.2 (hf hf_tail)
    exact hmap w.val w.nonstalling⟩

/-! ## takeWhile, dropWhile -/

/-- Take every vertex of `w` satisfying `p`, plus the first failure (if any).
The result is a contiguous prefix, hence non-stalling. -/
def takeWhile (w : SimpleWalk α) (p : α → Prop) [DecidablePred p] :
    SimpleWalk α :=
  ⟨w.val.takeWhile p, by grind⟩

/-- Drop the longest prefix of `w` on which `p` holds; the result starts at the
first failure. The hypothesis ensures a failure exists. The result is a
contiguous suffix, hence non-stalling. -/
def dropWhile (w : SimpleWalk α) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.val.toList, ¬ p v) : SimpleWalk α :=
  ⟨w.val.dropWhile p h, by grind⟩

/-! ## splitAt -/

/-- Split `w` into a list of pieces at every occurrence of the vertex `v`. Each
piece is a contiguous sub-walk of `w`, hence non-stalling. -/
def splitAt [DecidableEq α] (w : SimpleWalk α) (v : α) : List (SimpleWalk α) :=
  (w.val.splitAt v).pmap (fun p hp => ⟨p, hp⟩)
    (VertexSeq.nonstalling_splitAt w.val w.nonstalling v)

/-! ## zip -/

/-- Zip two simple walks into a simple walk of pairs. Consecutive pairs differ
in their first component (since `w` is non-stalling), so the result is
non-stalling. -/
def zip {β : Type*} (w : SimpleWalk α) (w' : SimpleWalk β) :
    SimpleWalk (α × β) :=
  ⟨w.val.zip w'.val, by grind⟩

/-! ## loopErase, cycleErase -/

/-- Remove immediate stalls. On a simple walk this is the identity, and the
result is non-stalling by construction. -/
def loopErase [DecidableEq α] (w : SimpleWalk α) : SimpleWalk α :=
  ⟨w.val.loopErase, w.val.loopErase_nonstalling⟩

/-- Cycle erasure: whenever a vertex repeats, drop the intermediate detour. The
result has no repeated vertex, and `nodup` implies `nonstalling`. -/
def cycleErase [DecidableEq α] (w : SimpleWalk α) : SimpleWalk α :=
  ⟨w.val.cycleErase, VertexSeq.nodup_nonstalling _ w.val.cycleErase_nodup⟩

/-! ## edges

The walk's traversed edges, lifted from the underlying vertex sequence. Most
lemmas are thin wrappers around the `VertexSeq` versions through `.val`. -/

/-- The number of traversed edges equals the walk's length. -/
@[simp] lemma length_edges (w : SimpleWalk α) : w.edges.length = w.length :=
  VertexSeq.length_edges w.val

/-- Reversal reverses the edge list. -/
@[simp] lemma edges_reverse (w : SimpleWalk α) :
    w.reverse.edges = w.edges.reverse :=
  VertexSeq.edges_reverse w.val

/-- The edges of an append are those of the operands plus the joining edge. -/
lemma edges_append (p q : SimpleWalk α) (h : p.val.tail ≠ q.val.head) :
    (p.append q h).edges = p.edges ++ [s(p.tail, q.head)] ++ q.edges :=
  VertexSeq.edges_append p.val q.val

/-- Gluing at a shared vertex concatenates the edge lists: the dropped duplicate
vertex carries no new edge beyond the one already ending `p`. -/
lemma edges_glue (p q : SimpleWalk α) (h : p.val.tail = q.val.head) :
    (p.glue q h).edges = p.edges ++ q.edges := by
  rw [SimpleWalk.glue]
  split
  · next hp => simp [edges, VertexSeq.edges_eq_nil_of_length_eq_zero p.val hp]
  · next hp =>
      change (p.val.dropTail.append q.val).edges = p.val.edges ++ q.val.edges
      rw [VertexSeq.edges_append,
        VertexSeq.edges_eq_dropTail_concat_of_length_ne_zero p.val hp, ← h,
        List.concat_eq_append]

/-- On a simple walk `loopErase` is the identity, so it leaves the edges
unchanged. -/
@[simp] lemma edges_loopErase [DecidableEq α] (w : SimpleWalk α) :
    w.loopErase.edges = w.edges := by
  change w.val.loopErase.edges = w.val.edges
  rw [VertexSeq.loopErase_eq_self_of_nonstalling w.val w.nonstalling]

/-- Cycle erasure cannot introduce new edges. -/
lemma edges_cycleErase_subset [DecidableEq α] (w : SimpleWalk α) :
    w.cycleErase.edges ⊆ w.edges :=
  VertexSeq.edges_cycleErase_subset w.val

/-- Dropping the last vertex cannot introduce new edges. -/
lemma edges_dropTail_subset (w : SimpleWalk α) : w.dropTail.edges ⊆ w.edges :=
  VertexSeq.edges_dropTail_subset w.val

/-- Dropping the first vertex cannot introduce new edges. -/
lemma edges_dropHead_subset (w : SimpleWalk α) : w.dropHead.edges ⊆ w.edges :=
  VertexSeq.edges_dropHead_subset w.val

/-- Taking a prefix cannot introduce new edges. -/
lemma edges_prefixUntil_subset [DecidableEq α] (w : SimpleWalk α) (v : α)
    (h : v ∈ w.val) : (w.prefixUntil v h).edges ⊆ w.edges :=
  VertexSeq.edges_prefixUntil_subset w.val v h

/-- Taking a suffix cannot introduce new edges. -/
lemma edges_suffixFrom_subset [DecidableEq α] (w : SimpleWalk α) (v : α)
    (h : v ∈ w.val) : (w.suffixFrom v h).edges ⊆ w.edges :=
  VertexSeq.edges_suffixFrom_subset w.val v h

/-- Any endpoint of a traversed edge is a vertex of the walk. -/
lemma mem_of_mem_edges {e : Sym2 α} {v : α} (w : SimpleWalk α)
    (he : e ∈ w.edges) (hv : v ∈ e) : v ∈ w.support :=
  VertexSeq.mem_of_mem_edges w.val he hv

/-! ## arcs

The walk's traversed arcs, lifted from the underlying vertex sequence. Most
lemmas are thin wrappers around the `VertexSeq` versions through `.val`. -/

/-- The number of traversed arcs equals the walk's length. -/
@[simp] lemma length_arcs (w : SimpleWalk α) : w.arcs.length = w.length :=
  VertexSeq.length_arcs w.val

/-- Reversal reverses the arc list and swaps every arc's endpoints. -/
@[simp] lemma arcs_reverse (w : SimpleWalk α) :
    w.reverse.arcs = w.arcs.reverse.map (fun a : α × α => (a.2, a.1)) :=
  VertexSeq.arcs_reverse w.val

/-- The arcs of an append are those of the operands plus the joining arc. -/
lemma arcs_append (p q : SimpleWalk α) (h : p.val.tail ≠ q.val.head) :
    (p.append q h).arcs = p.arcs ++ [(p.tail, q.head)] ++ q.arcs :=
  VertexSeq.arcs_append p.val q.val

/-- Gluing at a shared vertex concatenates the arc lists: the dropped duplicate
vertex carries no new arc beyond the one already ending `p`. -/
lemma arcs_glue (p q : SimpleWalk α) (h : p.val.tail = q.val.head) :
    (p.glue q h).arcs = p.arcs ++ q.arcs := by
  rw [SimpleWalk.glue]
  split
  · next hp => simp [arcs, VertexSeq.arcs_eq_nil_of_length_eq_zero p.val hp]
  · next hp =>
      change (p.val.dropTail.append q.val).arcs = p.val.arcs ++ q.val.arcs
      rw [VertexSeq.arcs_append,
        VertexSeq.arcs_eq_dropTail_concat_of_length_ne_zero p.val hp, ← h,
        List.concat_eq_append]

/-- On a simple walk `loopErase` is the identity, so it leaves the arcs
unchanged. -/
@[simp] lemma arcs_loopErase [DecidableEq α] (w : SimpleWalk α) :
    w.loopErase.arcs = w.arcs := by
  change w.val.loopErase.arcs = w.val.arcs
  rw [VertexSeq.loopErase_eq_self_of_nonstalling w.val w.nonstalling]

/-- Cycle erasure cannot introduce new arcs. -/
lemma arcs_cycleErase_subset [DecidableEq α] (w : SimpleWalk α) :
    w.cycleErase.arcs ⊆ w.arcs :=
  VertexSeq.arcs_cycleErase_subset w.val

/-- Dropping the last vertex cannot introduce new arcs. -/
lemma arcs_dropTail_subset (w : SimpleWalk α) : w.dropTail.arcs ⊆ w.arcs :=
  VertexSeq.arcs_dropTail_subset w.val

/-- Dropping the first vertex cannot introduce new arcs. -/
lemma arcs_dropHead_subset (w : SimpleWalk α) : w.dropHead.arcs ⊆ w.arcs :=
  VertexSeq.arcs_dropHead_subset w.val

/-- Taking a prefix cannot introduce new arcs. -/
lemma arcs_prefixUntil_subset [DecidableEq α] (w : SimpleWalk α) (v : α)
    (h : v ∈ w.val) : (w.prefixUntil v h).arcs ⊆ w.arcs :=
  VertexSeq.arcs_prefixUntil_subset w.val v h

/-- Taking a suffix cannot introduce new arcs. -/
lemma arcs_suffixFrom_subset [DecidableEq α] (w : SimpleWalk α) (v : α)
    (h : v ∈ w.val) : (w.suffixFrom v h).arcs ⊆ w.arcs :=
  VertexSeq.arcs_suffixFrom_subset w.val v h

/-- The source of a traversed arc is a vertex of the walk. -/
lemma fst_mem_of_mem_arcs {a : α × α} (w : SimpleWalk α)
    (ha : a ∈ w.arcs) : a.1 ∈ w.support :=
  VertexSeq.fst_mem_of_mem_arcs w.val ha

/-- The target of a traversed arc is a vertex of the walk. -/
lemma snd_mem_of_mem_arcs {a : α × α} (w : SimpleWalk α)
    (ha : a ∈ w.arcs) : a.2 ∈ w.support :=
  VertexSeq.snd_mem_of_mem_arcs w.val ha

/-- View a simple walk as a `SimpleGraph`. The non-stalling property
provides the looplessness axiom. -/
def toSimpleGraph (w : SimpleWalk α) : SimpleGraph α where
  vertexSet := { v | v ∈ w.val.toList }
  edgeSet := { e | e ∈ w.val.edges }
  incidence' := by
    intro e he v hv
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.edges] at he
    | cons w' u ih =>
      simp [VertexSeq.edges] at he
      rcases he with he_old | he_new
      · have hns : w'.nonstalling := hq.1
        have hv' : v ∈ w'.toList := ih hns he_old
        simp [VertexSeq.toList]
        exact Or.inl hv'
      · subst he_new
        simp [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · simp [VertexSeq.toList]
        · simp [VertexSeq.toList]
  loopless' := by
    intro e he
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.edges] at he
    | cons w' u ih =>
      simp [VertexSeq.edges] at he
      rcases he with he_old | he_new
      · exact ih hq.1 he_old
      · subst he_new
        simp [Sym2.mk_isDiag_iff]
        exact hq.2

/-- View a simple walk as a `SimpleDiGraph`. The non-stalling property
provides the looplessness axiom. -/
def toSimpleDiGraph (w : SimpleWalk α) : SimpleDiGraph α where
  vertexSet := { v | v ∈ w.val.toList }
  edgeSet := { a | a ∈ w.val.arcs }
  incidence' := by
    intro a ha
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.arcs] at ha
    | cons w' u ih =>
      simp [VertexSeq.arcs] at ha
      rcases ha with ha_old | ha_new
      · obtain ⟨h1, h2⟩ := ih hq.1 ha_old
        refine ⟨?_, ?_⟩
        · simp [VertexSeq.toList]; exact Or.inl h1
        · simp [VertexSeq.toList]; exact Or.inl h2
      · subst ha_new
        refine ⟨?_, ?_⟩
        · simp [VertexSeq.toList]
        · simp [VertexSeq.toList]
  loopless' := by
    intro a ha
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.arcs] at ha
    | cons w' u ih =>
      simp [VertexSeq.arcs] at ha
      rcases ha with ha_old | ha_new
      · exact ih hq.1 ha_old
      · subst ha_new; exact hq.2

/-- The edges of `w.toSimpleGraph` are exactly the edges traversed by `w`. -/
@[simp] lemma mem_edgeSet_toSimpleGraph (w : SimpleWalk α) {e : Sym2 α} :
    e ∈ w.toSimpleGraph.edgeSet ↔ e ∈ w.edges := Iff.rfl

/-- The vertices of `w.toSimpleGraph` are exactly the vertices visited by `w`. -/
@[simp] lemma mem_vertexSet_toSimpleGraph (w : SimpleWalk α) {v : α} :
    v ∈ w.toSimpleGraph.vertexSet ↔ v ∈ w.support := Iff.rfl

/-- The edges of `w.toSimpleDiGraph` are exactly the arcs traversed by `w`. -/
@[simp] lemma mem_edgeSet_toSimpleDiGraph (w : SimpleWalk α) {a : α × α} :
    a ∈ w.toSimpleDiGraph.edgeSet ↔ a ∈ w.arcs := Iff.rfl

/-- The vertices of `w.toSimpleDiGraph` are exactly the vertices visited by `w`. -/
@[simp] lemma mem_vertexSet_toSimpleDiGraph (w : SimpleWalk α) {v : α} :
    v ∈ w.toSimpleDiGraph.vertexSet ↔ v ∈ w.support := Iff.rfl

end SimpleWalk
