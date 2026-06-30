/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Adjacency
import GraphLib.Graph.Subgraph
import GraphLib.Theory.Structures.SimpleWalk

/-!
# Vertex sequences realized in a simple directed graph

A `VertexSeq α` is purely combinatorial: it records an ordered list of vertices,
but it does not know about any graph. This file starts the directed analogue of
`GraphLib.Theory.Structures.InSimpleGraph` by connecting vertex sequences and
simple walks to a `SimpleDiGraph`.

## Main definitions

* `SimpleDiGraph.IsVertexSeqIn G w` — the vertex sequence `w` is realized in
  the simple directed graph `G`: its head is a vertex of `G`, and each
  consecutive step follows a directed edge of `G`.
* `SimpleDiGraph.IsSimpleWalkIn G w` — the simple walk `w` is realized in `G` through
  its underlying vertex sequence.

## Main API

* Constructor characterizations: `singleton_iff`, `cons_iff`.
* Vertex membership: `head_mem`, `tail_mem`, `mem_vertexSet`.
* Arc-list characterization: `iff_arcs`, `mem_edgeSet_of_mem_arcs`, and the
  generated-graph characterization `iff_toSimpleDiGraph_subgraphOf`.
* Closure under direction-preserving `VertexSeq` operations: `prepend`,
  `append`, `dropHead`, `dropTail`, `prefixUntil`, `suffixFrom`, `takeWhile`,
  `dropWhile`, `loopErase`, `cycleErase`, and monotonicity `mono` under
  `SimpleDiGraph.subgraphOf`.
* Thin `IsSimpleWalkIn` wrappers for the corresponding `SimpleWalk`
  operations.
* `nonstalling` — a realized sequence never stalls, because adjacency in a
  simple directed graph forces distinct endpoints.

## Design choices

* **Directed adjacency.** The `cons` constructor uses `G.Adj w.tail u`, meaning
  an arc from the previous tail to the newly appended vertex. Unlike the
  undirected simple-graph version, no symmetry is expected.
* **No reverse closure.** Reversing a sequence reverses every arc, so it is not
  generally realized in the same directed graph.
* **Thin simple-walk layer.** `IsSimpleWalkIn` is only a wrapper around
  `IsVertexSeqIn` on `w.val`; later API should normally be proved by delegating
  to the vertex sequence layer.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleDiGraph

/-! ## Vertex sequences realized in a simple directed graph -/

/-- A vertex sequence is *realized in* a simple directed graph `G` when its head
is a vertex of `G` and each consecutive pair follows a directed edge of `G`. -/
@[grind] inductive IsVertexSeqIn (G : SimpleDiGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (ha : G.Adj w.tail u) :
      IsVertexSeqIn G (w.cons u)

namespace IsVertexSeqIn

/-! ## Constructor characterizations -/

/-- A singleton is realized in `G` exactly when its vertex is in `G`. -/
@[simp, grind =] lemma singleton_iff (G : SimpleDiGraph α) (v : α) :
    G.IsVertexSeqIn (.singleton v) ↔ v ∈ V(G) :=
  ⟨fun h => by cases h; assumption, IsVertexSeqIn.singleton v⟩

/-- A `cons` is realized in `G` exactly when its prefix is realized and the new
step is an arc. -/
@[simp, grind =] lemma cons_iff (G : SimpleDiGraph α) (w : VertexSeq α) (u : α) :
    G.IsVertexSeqIn (w.cons u) ↔ G.IsVertexSeqIn w ∧ G.Adj w.tail u := by
  constructor
  · intro h; cases h with | cons w u hw ha => exact ⟨hw, ha⟩
  · intro ⟨hw, ha⟩; exact .cons w u hw ha

/-! ## Vertex membership -/

/-- The head of a realized sequence is a vertex of `G`. -/
@[grind →] lemma head_mem (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.head ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw ha ih => exact ih

/-- The tail of a realized sequence is a vertex of `G`. -/
@[grind →] lemma tail_mem (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.tail ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw ha ih => exact ha.right_mem

/-- Every vertex of a realized sequence is a vertex of `G`. -/
@[grind →] lemma mem_vertexSet (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : ∀ v ∈ w, v ∈ V(G) := by
  induction hw <;> grind [SimpleDiGraph.Adj.right_mem]

/-- A realized sequence never stalls: consecutive vertices differ, because
adjacency in a simple directed graph forces distinct endpoints. Hence it
underlies a `SimpleWalk`. -/
@[grind →] lemma nonstalling (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.nonstalling := by
  induction hw <;> grind

/-! ## Closure under sequence operations -/

/-- Appending two realized sequences along an arc is realized. -/
@[grind] lemma append (G : SimpleDiGraph α) {w1 w2 : VertexSeq α}
    (h1 : G.IsVertexSeqIn w1) (h2 : G.IsVertexSeqIn w2)
    (ha : G.Adj w1.tail w2.head) : G.IsVertexSeqIn (w1.append w2) := by
  revert ha
  induction h2 with
  | singleton v hv => intro ha; exact .cons w1 v h1 ha
  | cons w u hw hadj ih =>
      intro ha
      exact .cons (w1.append w) u (ih ha) (by grind [VertexSeq.tail_append])

/-- Prepending a vertex along an arc to the head preserves realization. -/
@[grind →] lemma prepend (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {u : α} (ha : G.Adj u w.head) :
    G.IsVertexSeqIn ((VertexSeq.singleton u).append w) :=
  append G (.singleton u ha.left_mem) hw ha

/-- Dropping the last vertex preserves realization. -/
@[grind →] lemma dropTail (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropTail := by
  induction hw <;> grind

/-- Dropping the first vertex preserves realization. -/
@[grind →] lemma dropHead (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropHead := by
  induction hw with
  | singleton v hv => exact .singleton v hv
  | cons w u hw ha ih =>
      cases w with
      | singleton x => exact .singleton u ha.right_mem
      | cons t x => exact .cons _ u ih (by rw [VertexSeq.tail_dropHead]; exact ha)

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleDiGraph α) {w : VertexSeq α}
    (hw : H.IsVertexSeqIn w) (hsub : SimpleDiGraph.subgraphOf H G) :
    G.IsVertexSeqIn w := by
  induction hw with
  | singleton v hv => exact .singleton v (hsub.1 hv)
  | cons w u hw ha ih => exact .cons w u ih (hsub.2 ha)

/-- Taking the prefix up to the first occurrence of `v` preserves realization. -/
@[grind →] lemma prefixUntil [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) :
    ∀ (v : α) (h : v ∈ w), G.IsVertexSeqIn (w.prefixUntil v h) := by
  induction hw with
  | singleton x hx => intro v h; grind
  | cons w u hw ha ih =>
      intro v h
      by_cases h2 : v ∈ w <;> grind

/-- Dropping to the suffix from the first occurrence of `v` preserves
realization. -/
@[grind →] lemma suffixFrom [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) :
    ∀ (v : α) (h : v ∈ w), G.IsVertexSeqIn (w.suffixFrom v h) := by
  induction hw with
  | singleton x hx => intro v h; grind
  | cons w u hw ha ih =>
      intro v h
      by_cases h2 : v ∈ w <;>
        grind [VertexSeq.tail_suffixFrom, SimpleDiGraph.Adj.right_mem]

/-- Taking the longest prefix on which `p` holds (plus its first failure)
preserves realization. -/
lemma takeWhile (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    G.IsVertexSeqIn (w.takeWhile p) := by
  induction hw with
  | singleton x hx => exact .singleton x hx
  | cons w u hw ha ih =>
      change G.IsVertexSeqIn (if ∃ v ∈ w.toList, ¬ p v then w.takeWhile p else w.cons u)
      by_cases hc : ∃ v ∈ w.toList, ¬ p v
      · rw [if_pos hc]; exact ih
      · rw [if_neg hc]; exact .cons w u hw ha

/-- Dropping the longest prefix on which `p` holds preserves realization. -/
lemma dropWhile (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    ∀ (h : ∃ v ∈ w.toList, ¬ p v), G.IsVertexSeqIn (w.dropWhile p h) := by
  induction hw with
  | singleton x hx => intro h; exact .singleton x hx
  | cons w u hw ha ih =>
      intro h
      change G.IsVertexSeqIn
        (if hq : ∃ v ∈ w.toList, ¬ p v then (w.dropWhile p hq).cons u else .singleton u)
      by_cases hc : ∃ v ∈ w.toList, ¬ p v
      · rw [dif_pos hc]
        exact .cons (w.dropWhile p hc) u (ih hc)
          (by rw [VertexSeq.tail_dropWhile]; exact ha)
      · rw [dif_neg hc]; exact .singleton u ha.right_mem

/-- If `G` has no arcs, every realized sequence has length zero. -/
lemma length_eq_zero_of_no_edges (G : SimpleDiGraph α) (hE : E(G) = ∅)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) : w.length = 0 := by
  induction hw <;> grind

/-- Removing immediate stalls preserves realization. (On a realized — hence
non-stalling — sequence `loopErase` is in fact the identity.) -/
lemma loopErase [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.loopErase := by
  rw [VertexSeq.loopErase_eq_self_of_nonstalling w (nonstalling G hw)]
  exact hw

/-- Cycle erasure preserves realization: dropping the detour between two
occurrences of a vertex keeps the sequence realized in `G`. -/
lemma cycleErase [DecidableEq α] (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.cycleErase := by
  revert hw
  fun_induction VertexSeq.cycleErase w <;>
    intro hw <;> grind [IsVertexSeqIn.prefixUntil, VertexSeq.tail_cycleErase]

/-! ## Arc-list characterization -/

/-- The arc-list view of realization, bridging the adjacency-based inductive
definition: `w` is realized in `G` exactly when its head is a vertex of `G` and
every arc it traverses is an edge of `G`. -/
theorem iff_arcs (G : SimpleDiGraph α) (w : VertexSeq α) :
    G.IsVertexSeqIn w ↔ w.head ∈ V(G) ∧ ∀ a ∈ w.arcs, a ∈ E(G) := by
  constructor
  · intro hw
    refine ⟨head_mem G hw, ?_⟩
    induction hw with
    | singleton v hv => intro a ha; simp [VertexSeq.arcs] at ha
    | cons w u hw ha ih =>
        intro a hmem
        rw [VertexSeq.mem_arcs_cons] at hmem
        rcases hmem with hmem | rfl
        · exact ih a hmem
        · exact ha
  · induction w with
    | singleton v => intro h; exact .singleton v h.1
    | cons w u ih =>
        intro h
        rw [cons_iff]
        refine ⟨ih ⟨h.1, fun a ha => h.2 a ?_⟩, h.2 (w.tail, u) ?_⟩
        · rw [VertexSeq.mem_arcs_cons]; exact Or.inl ha
        · rw [VertexSeq.mem_arcs_cons]; exact Or.inr rfl

/-- Any arc traversed by a realized vertex sequence is an edge of the graph. -/
@[grind →] lemma mem_edgeSet_of_mem_arcs (G : SimpleDiGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {a : α × α} (ha : a ∈ w.arcs) : a ∈ E(G) :=
  ((iff_arcs G w).1 hw).2 a ha

/-- The final step of a non-trivial realized vertex sequence is an adjacency in
the graph. -/
@[grind →] lemma adj_dropTail_tail_tail_of_length_ne_zero (G : SimpleDiGraph α)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) (h : w.length ≠ 0) :
    G.Adj w.dropTail.tail w.tail := by
  change (w.dropTail.tail, w.tail) ∈ E(G)
  exact mem_edgeSet_of_mem_arcs G hw
    (by
      rw [VertexSeq.arcs_eq_dropTail_concat_of_length_ne_zero w h]
      simp [List.concat_eq_append])

end IsVertexSeqIn

/-! ## Simple walks realized in a simple directed graph -/

/-- A simple walk is realized in `G` when its underlying vertex sequence is
realized in `G`. -/
@[grind] def IsSimpleWalkIn (G : SimpleDiGraph α) (w : SimpleWalk α) : Prop :=
  G.IsVertexSeqIn w.val

namespace IsSimpleWalkIn

/-! ## Bridge to `IsVertexSeqIn` -/

/-- Realization of a simple walk is realization of its underlying vertex
sequence. -/
@[simp, grind =] lemma isSimpleWalkIn_iff_isVertexSeqIn
    (G : SimpleDiGraph α) (w : SimpleWalk α) :
    G.IsSimpleWalkIn w ↔ G.IsVertexSeqIn w.val := Iff.rfl

/-! ## Vertex membership -/

/-- The head of a realized walk is a vertex of `G`. -/
@[grind →] lemma head_mem (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : w.head ∈ V(G) :=
  IsVertexSeqIn.head_mem G hw

/-- The tail of a realized walk is a vertex of `G`. -/
@[grind →] lemma tail_mem (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : w.tail ∈ V(G) :=
  IsVertexSeqIn.tail_mem G hw

/-- Every vertex visited by a realized walk is a vertex of `G`. -/
@[grind →] lemma mem_vertexSet (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : ∀ v ∈ w.support, v ∈ V(G) :=
  IsVertexSeqIn.mem_vertexSet G hw

/-! ## Vertex and arc membership -/

/-- Any arc traversed by a realized walk is an edge of `G`. -/
@[grind →] lemma mem_edgeSet_of_mem_arcs (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) {a : α × α} (ha : a ∈ w.arcs) : a ∈ E(G) :=
  IsVertexSeqIn.mem_edgeSet_of_mem_arcs G hw ha

/-- A walk is realized in `G` exactly when its head is a vertex of `G` and every
arc it traverses is an edge of `G`. -/
theorem iff_arcs (G : SimpleDiGraph α) (w : SimpleWalk α) :
    G.IsSimpleWalkIn w ↔ w.head ∈ V(G) ∧ ∀ a ∈ w.arcs, a ∈ E(G) :=
  IsVertexSeqIn.iff_arcs G w.val

/-! ## Traversed arcs and the generated simple directed graph -/

/-- All arcs traversed by a realized simple walk are edges of `G`, as a bundled
arc-list predicate. -/
lemma arcs_subset_edgeSet (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : ∀ a ∈ w.arcs, a ∈ E(G) :=
  (iff_arcs G w).1 hw |>.2

/-- The simple directed graph generated by a realized simple walk is a subgraph
of `G`. -/
lemma toSimpleDiGraph_subgraphOf (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : SimpleDiGraph.subgraphOf w.toSimpleDiGraph G := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact mem_vertexSet G hw v (by simpa using hv)
  · intro a ha
    exact mem_edgeSet_of_mem_arcs G hw (by simpa using ha)

/-- If the simple directed graph generated by a simple walk is a subgraph of
`G`, then the walk is realized in `G`. -/
lemma of_toSimpleDiGraph_subgraphOf (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hsub : SimpleDiGraph.subgraphOf w.toSimpleDiGraph G) : G.IsSimpleWalkIn w := by
  rw [iff_arcs]
  refine ⟨?_, ?_⟩
  · exact hsub.1 (by simp [SimpleWalk.support])
  · intro a ha
    exact hsub.2 (by simpa using ha)

/-- A simple walk is realized in `G` exactly when its generated simple directed
graph is a subgraph of `G`. -/
theorem iff_toSimpleDiGraph_subgraphOf (G : SimpleDiGraph α) (w : SimpleWalk α) :
    G.IsSimpleWalkIn w ↔ SimpleDiGraph.subgraphOf w.toSimpleDiGraph G :=
  ⟨toSimpleDiGraph_subgraphOf G, of_toSimpleDiGraph_subgraphOf G⟩

/-! ## Closure under walk operations -/

/-- Dropping the last vertex of a realized walk preserves realization. -/
@[grind →] lemma dropTail (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn w.dropTail :=
  IsVertexSeqIn.dropTail G hw

/-- Dropping the first vertex of a realized walk preserves realization. -/
@[grind →] lemma dropHead (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn w.dropHead :=
  IsVertexSeqIn.dropHead G hw

/-- Taking a prefix of a realized walk preserves realization. -/
@[grind →] lemma prefixUntil [DecidableEq α] (G : SimpleDiGraph α)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) (v : α) (h : v ∈ w.val) :
    G.IsSimpleWalkIn (w.prefixUntil v h) :=
  IsVertexSeqIn.prefixUntil G hw v h

/-- Taking a suffix of a realized walk preserves realization. -/
@[grind →] lemma suffixFrom [DecidableEq α] (G : SimpleDiGraph α)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) (v : α) (h : v ∈ w.val) :
    G.IsSimpleWalkIn (w.suffixFrom v h) :=
  IsVertexSeqIn.suffixFrom G hw v h

/-- Taking the longest prefix on which `p` holds (plus its first failure)
preserves realization. -/
lemma takeWhile (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) (p : α → Prop) [DecidablePred p] :
    G.IsSimpleWalkIn (w.takeWhile p) :=
  IsVertexSeqIn.takeWhile G hw p

/-- Dropping the longest prefix on which `p` holds preserves realization. -/
lemma dropWhile (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.val.toList, ¬ p v) :
    G.IsSimpleWalkIn (w.dropWhile p h) :=
  IsVertexSeqIn.dropWhile G hw p h

/-- Loop erasure preserves realization. On a simple walk this operation is the
identity on the underlying sequence. -/
lemma loopErase [DecidableEq α] (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn (w.loopErase) :=
  IsVertexSeqIn.loopErase G hw

/-- Cycle erasure preserves realization. -/
lemma cycleErase [DecidableEq α] (G : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn (w.cycleErase) :=
  IsVertexSeqIn.cycleErase G hw

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleDiGraph α) {w : SimpleWalk α}
    (hw : H.IsSimpleWalkIn w) (hsub : SimpleDiGraph.subgraphOf H G) :
    G.IsSimpleWalkIn w :=
  IsVertexSeqIn.mono G H hw hsub

/-- If `G` has no arcs, every realized walk in `G` has length zero. -/
lemma length_eq_zero_of_no_edges (G : SimpleDiGraph α) (hE : E(G) = ∅)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) : w.length = 0 :=
  IsVertexSeqIn.length_eq_zero_of_no_edges G hE hw

/-! ## Joining walks -/

/-- Appending two realized walks along an arc of `G` preserves realization. -/
lemma append (G : SimpleDiGraph α) {p q : SimpleWalk α}
    (hp : G.IsSimpleWalkIn p) (hq : G.IsSimpleWalkIn q)
    (ha : G.Adj p.tail q.head) :
    G.IsSimpleWalkIn (p.append q ha.ne) :=
  IsVertexSeqIn.append G hp hq ha

/-- Gluing two realized walks at a shared endpoint preserves realization. -/
lemma glue (G : SimpleDiGraph α) {p q : SimpleWalk α}
    (hp : G.IsSimpleWalkIn p) (hq : G.IsSimpleWalkIn q)
    (h : p.tail = q.head) :
    G.IsSimpleWalkIn (p.glue q h) := by
  unfold SimpleWalk.glue
  by_cases hlen : p.val.length = 0
  · rw [dif_pos hlen]
    exact hq
  · rw [dif_neg hlen]
    exact IsVertexSeqIn.append G (IsVertexSeqIn.dropTail G hp) hq
      (by
        have h' : p.val.tail = q.val.head := h
        rw [← h']
        exact IsVertexSeqIn.adj_dropTail_tail_tail_of_length_ne_zero G hp hlen)

end IsSimpleWalkIn

end SimpleDiGraph

end GraphLib
