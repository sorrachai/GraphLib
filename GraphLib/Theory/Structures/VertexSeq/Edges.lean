/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.Sym.Sym2
import GraphLib.Theory.Structures.VertexSeq.Erase

/-!
# Vertex sequences: traversed edges

The edges and arcs traversed by a vertex sequence: the consecutive vertex pairs
of each `cons` step, viewed either as unordered `Sym2 α` edges or as ordered
`α × α` arcs.

These are purely combinatorial — they mention no graph. They are kept as lists,
mirroring how the vertex side uses `toList` rather than a `Set`: order and
multiplicity are retained (needed for trails/Eulerian walks), and a graph's
`edgeSet : Set (Sym2 α)` is reached on demand via `e ∈ w.edges` (see
`SimpleGraph.IsVertexSeqIn`).

## Main definitions

* `VertexSeq.edges` — the list of unordered edges traversed.
* `VertexSeq.arcs` — the list of directed arcs traversed.
-/

variable {α : Type*}

namespace VertexSeq

/-- The unordered edges traversed by a vertex sequence (the consecutive
pairs `s(w.tail, v)` for each `cons` step). -/
@[grind] def edges : VertexSeq α → List (Sym2 α)
  | .singleton _ => []
  | .cons w v   => w.edges.concat s(w.tail, v)

/-- The directed arcs traversed by a vertex sequence (the consecutive ordered
pairs `(w.tail, v)` for each `cons` step). -/
@[grind] def arcs : VertexSeq α → List (α × α)
  | .singleton _ => []
  | .cons w v   => w.arcs.concat (w.tail, v)

/-! ## Basic computation rules -/

@[simp, grind =] lemma edges_singleton (v : α) : (singleton v).edges = [] := rfl

@[simp, grind =] lemma edges_cons (w : VertexSeq α) (v : α) :
    (w :+ v).edges = w.edges.concat s(w.tail, v) := rfl

/-- Membership in the edges of a `cons`: an old edge or the new last edge. -/
@[simp] lemma mem_edges_cons {e : Sym2 α} (w : VertexSeq α) (v : α) :
    e ∈ (w :+ v).edges ↔ e ∈ w.edges ∨ e = s(w.tail, v) := by
  simp [edges, List.concat_eq_append]

@[simp, grind =] lemma arcs_singleton (v : α) : (singleton v).arcs = [] := rfl

@[simp, grind =] lemma arcs_cons (w : VertexSeq α) (v : α) :
    (w :+ v).arcs = w.arcs.concat (w.tail, v) := rfl

/-- Membership in the arcs of a `cons`: an old arc or the new last arc. -/
@[simp] lemma mem_arcs_cons {a : α × α} (w : VertexSeq α) (v : α) :
    a ∈ (w :+ v).arcs ↔ a ∈ w.arcs ∨ a = (w.tail, v) := by
  simp [arcs, List.concat_eq_append]

/-! ## Length and last edge -/

/-- The number of traversed edges equals `length` (one less than the number of
vertices). -/
@[simp, grind =] lemma length_edges (w : VertexSeq α) :
    w.edges.length = w.length := by
  induction w with
  | singleton v => rfl
  | cons w v ih => simp only [edges, length, List.length_concat, ih]; omega

/-- A length-zero sequence (a single vertex) traverses no edges. -/
@[simp, grind =] lemma edges_eq_nil_of_length_eq_zero (w : VertexSeq α)
    (h : w.length = 0) : w.edges = [] := by
  cases w with
  | singleton v => rfl
  | cons w v => simp [length] at h

/-- For a non-trivial sequence, the traversed edges are those of the
dropped-tail sequence plus the final edge. -/
@[grind →] lemma edges_eq_dropTail_concat_of_length_ne_zero (w : VertexSeq α)
    (h : w.length ≠ 0) :
    w.edges = w.dropTail.edges.concat s(w.dropTail.tail, w.tail) := by
  cases w with
  | singleton v => exact (h rfl).elim
  | cons w v => rfl

/-- The number of traversed arcs equals `length` (one less than the number of
vertices). -/
@[simp, grind =] lemma length_arcs (w : VertexSeq α) :
    w.arcs.length = w.length := by
  induction w with
  | singleton v => rfl
  | cons w v ih => simp only [arcs, length, List.length_concat, ih]; omega

/-- A length-zero sequence (a single vertex) traverses no arcs. -/
@[simp, grind =] lemma arcs_eq_nil_of_length_eq_zero (w : VertexSeq α)
    (h : w.length = 0) : w.arcs = [] := by
  cases w with
  | singleton v => rfl
  | cons w v => simp [length] at h

/-- For a non-trivial sequence, the traversed arcs are those of the
dropped-tail sequence plus the final arc. -/
@[grind →] lemma arcs_eq_dropTail_concat_of_length_ne_zero (w : VertexSeq α)
    (h : w.length ≠ 0) :
    w.arcs = w.dropTail.arcs.concat (w.dropTail.tail, w.tail) := by
  cases w with
  | singleton v => exact (h rfl).elim
  | cons w v => rfl

/-! ## Endpoints -/

/-- Any endpoint of a traversed edge is a vertex of the sequence. -/
@[grind →] lemma mem_of_mem_edges {e : Sym2 α} {x : α} (w : VertexSeq α)
    (he : e ∈ w.edges) (hx : x ∈ e) : x ∈ w := by
  induction w with
  | singleton v => simp [edges] at he
  | cons w v ih => grind [mem_edges_cons, mem_cons, tail_mem]

/-- The source of a traversed arc is a vertex of the sequence. -/
@[grind →] lemma fst_mem_of_mem_arcs {a : α × α} (w : VertexSeq α)
    (ha : a ∈ w.arcs) : a.1 ∈ w := by
  induction w with
  | singleton v => simp [arcs] at ha
  | cons w v ih => grind [mem_arcs_cons, mem_cons, tail_mem]

/-- The target of a traversed arc is a vertex of the sequence. -/
@[grind →] lemma snd_mem_of_mem_arcs {a : α × α} (w : VertexSeq α)
    (ha : a ∈ w.arcs) : a.2 ∈ w := by
  induction w with
  | singleton v => simp [arcs] at ha
  | cons w v ih => grind [mem_arcs_cons, mem_cons, tail_mem]

/-! ## Nodup of edges -/

/-- A duplicate-free sequence traverses each edge at most once (a path is a
trail). -/
@[grind] lemma nodup_edges_of_nodup (w : VertexSeq α) (h : w.nodup) :
    w.edges.Nodup := by
  induction w with
  | singleton v => simp [edges]
  | cons w v ih =>
      obtain ⟨hw, hv⟩ := h
      rw [edges_cons, List.concat_eq_append, List.nodup_append]
      refine ⟨ih hw, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hv (mem_of_mem_edges w ha (by simp))

/-- The only way the edge between a duplicate-free sequence's two endpoints can
be traversed is if the sequence is a single edge: otherwise the endpoints are
not consecutive. Used to show a cycle's closing edge is fresh. -/
@[grind →] lemma length_le_one_of_mem_edges_head_tail (w : VertexSeq α)
    (h : w.nodup) (he : s(w.head, w.tail) ∈ w.edges) : w.length ≤ 1 := by
  cases w with
  | singleton v => simp [edges] at he
  | cons w v =>
      obtain ⟨hw, hv⟩ := h
      simp only [head_cons, tail_cons, mem_edges_cons] at he
      rcases he with he | he
      · exact absurd (mem_of_mem_edges w he (by simp)) hv
      · have hht : w.head = w.tail := by
          rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact h1
          · exact absurd (h1 ▸ head_mem w) hv
        have : w.length = 0 := length_zero_of_nodup_head_eq_tail w hw hht
        simp [length, this]

/-! ## Nodup of arcs -/

/-- A duplicate-free sequence traverses each directed arc at most once. -/
@[grind] lemma nodup_arcs_of_nodup (w : VertexSeq α) (h : w.nodup) :
    w.arcs.Nodup := by
  induction w with
  | singleton v => simp [arcs]
  | cons w v ih =>
      obtain ⟨hw, hv⟩ := h
      rw [arcs_cons, List.concat_eq_append, List.nodup_append]
      refine ⟨ih hw, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab
      exact hv (snd_mem_of_mem_arcs w ha)

/-- In a duplicate-free sequence, an arc from the tail back to the head cannot
occur except in the degenerate length-at-most-one case. -/
@[grind →] lemma length_le_one_of_mem_arcs_tail_head (w : VertexSeq α)
    (h : w.nodup) (ha : (w.tail, w.head) ∈ w.arcs) : w.length ≤ 1 := by
  cases w with
  | singleton v => simp [arcs] at ha
  | cons w v =>
      obtain ⟨hw, hv⟩ := h
      simp only [head_cons, tail_cons, mem_arcs_cons] at ha
      rcases ha with ha | ha
      · exact absurd (fst_mem_of_mem_arcs w ha) hv
      · have hhead : w.head = v := congrArg Prod.snd ha
        exact (hv (by rw [← hhead]; exact head_mem w)).elim

/-! ## append, reverse -/

/-- The edges of an append are those of the operands plus the joining edge
`s(p.tail, q.head)` between them. -/
@[simp, grind =] lemma edges_append (p q : VertexSeq α) :
    (p.append q).edges = p.edges ++ [s(p.tail, q.head)] ++ q.edges := by
  induction q generalizing p with
  | singleton v => simp [append, edges, List.concat_eq_append]
  | cons q v ih =>
      simp only [append, edges_cons, tail_append, head_cons, ih,
        List.concat_eq_append, List.append_assoc]

/-- Reversing a sequence reverses its list of (undirected) edges. -/
@[simp, grind =] lemma edges_reverse (w : VertexSeq α) :
    w.reverse.edges = w.edges.reverse := by
  induction w with
  | singleton v => rfl
  | cons w v ih =>
      rw [reverse, edges_append, edges_cons, ih]
      simp [head_reverse, List.concat_eq_append, Sym2.eq_swap]

/-- The arcs of an append are those of the operands plus the joining arc
`(p.tail, q.head)` between them. -/
@[simp, grind =] lemma arcs_append (p q : VertexSeq α) :
    (p.append q).arcs = p.arcs ++ [(p.tail, q.head)] ++ q.arcs := by
  induction q generalizing p with
  | singleton v => simp [append, arcs, List.concat_eq_append]
  | cons q v ih =>
      simp only [append, arcs_cons, tail_append, head_cons, ih,
        List.concat_eq_append, List.append_assoc]

/-- Reversing a sequence reverses the arc list and swaps every arc's endpoints. -/
@[simp, grind =] lemma arcs_reverse (w : VertexSeq α) :
    w.reverse.arcs = w.arcs.reverse.map (fun a : α × α => (a.2, a.1)) := by
  induction w with
  | singleton v => rfl
  | cons w v ih =>
      rw [reverse, arcs_append, arcs_cons, ih]
      simp [head_reverse, List.concat_eq_append]

/-! ## Subsequence operations do not introduce new edges -/

/-- Dropping the last vertex cannot introduce new traversed edges. -/
@[grind] lemma edges_dropTail_subset (w : VertexSeq α) :
    w.dropTail.edges ⊆ w.edges := by
  cases w <;> simp [dropTail, edges, List.concat_eq_append]

/-- Dropping the first vertex cannot introduce new traversed edges. -/
@[grind] lemma edges_dropHead_subset (w : VertexSeq α) :
    w.dropHead.edges ⊆ w.edges := by
  intro e he
  fun_induction dropHead w <;> grind [mem_edges_cons, tail_dropHead]

/-- Taking a prefix cannot introduce new traversed edges. -/
@[grind] lemma edges_prefixUntil_subset [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : (w.prefixUntil v h).edges ⊆ w.edges := by
  intro e he
  fun_induction prefixUntil w v h <;> grind [mem_edges_cons]

/-- Taking a suffix cannot introduce new traversed edges. -/
@[grind] lemma edges_suffixFrom_subset [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : (w.suffixFrom v h).edges ⊆ w.edges := by
  intro e he
  fun_induction suffixFrom w v h <;> grind [mem_edges_cons, tail_suffixFrom]

/-- Loop erasure cannot introduce new traversed edges. -/
@[grind] lemma edges_loopErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.edges ⊆ w.edges := by
  intro e he
  fun_induction loopErase w <;> grind [mem_edges_cons, tail_loopErase]

/-- Cycle erasure cannot introduce new traversed edges. -/
@[grind] lemma edges_cycleErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.edges ⊆ w.edges := by
  intro e he
  fun_induction cycleErase w <;>
    grind [mem_edges_cons, edges_prefixUntil_subset, tail_cycleErase]

/-! ## Subsequence operations do not introduce new arcs -/

/-- Dropping the last vertex cannot introduce new traversed arcs. -/
@[grind] lemma arcs_dropTail_subset (w : VertexSeq α) :
    w.dropTail.arcs ⊆ w.arcs := by
  cases w <;> simp [dropTail, arcs, List.concat_eq_append]

/-- Dropping the first vertex cannot introduce new traversed arcs. -/
@[grind] lemma arcs_dropHead_subset (w : VertexSeq α) :
    w.dropHead.arcs ⊆ w.arcs := by
  intro a ha
  fun_induction dropHead w <;> grind [mem_arcs_cons, tail_dropHead]

/-- Taking a prefix cannot introduce new traversed arcs. -/
@[grind] lemma arcs_prefixUntil_subset [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : (w.prefixUntil v h).arcs ⊆ w.arcs := by
  intro a ha
  fun_induction prefixUntil w v h <;> grind [mem_arcs_cons]

/-- Taking a suffix cannot introduce new traversed arcs. -/
@[grind] lemma arcs_suffixFrom_subset [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : (w.suffixFrom v h).arcs ⊆ w.arcs := by
  intro a ha
  fun_induction suffixFrom w v h <;> grind [mem_arcs_cons, tail_suffixFrom]

/-- Loop erasure cannot introduce new traversed arcs. -/
@[grind] lemma arcs_loopErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.arcs ⊆ w.arcs := by
  intro a ha
  fun_induction loopErase w <;> grind [mem_arcs_cons, tail_loopErase]

/-- Cycle erasure cannot introduce new traversed arcs. -/
@[grind] lemma arcs_cycleErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.arcs ⊆ w.arcs := by
  intro a ha
  fun_induction cycleErase w <;>
    grind [mem_arcs_cons, arcs_prefixUntil_subset, tail_cycleErase]

end VertexSeq
