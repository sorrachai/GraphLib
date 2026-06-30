/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Adjacency
import GraphLib.Graph.Subgraph
import GraphLib.Theory.Structures.SimpleWalk

/-!
# Vertex sequences realized in a simple graph

A `VertexSeq α` is a purely combinatorial object: it knows nothing about any
graph. This file connects vertex sequences to a `SimpleGraph` through the
predicate `SimpleGraph.IsVertexSeqIn`, which says that the sequence is *realized*
in `G`: its first vertex is a vertex of `G` and every consecutive pair is an edge
of `G` (phrased through `SimpleGraph.Adj`).

This is the undirected analogue intended to mirror, in the `GraphLib` style, the
`IsVertexSeqIn` development from the legacy `GraphAlgorithms` library. The
primary definition is inductive and phrased through `Adj`; the edge-list
characterization appears later as a bridge to generated subgraphs and edge-set
reasoning.

## Main definitions

* `SimpleGraph.IsVertexSeqIn G w` — `w` is realized in `G`.
* `SimpleGraph.IsSimpleWalkIn G w` — a `SimpleWalk` is realized in `G` through its
  underlying vertex sequence.

## Main API

* `SimpleGraph.IsVertexSeqIn.singleton_iff`, `cons_iff` — the two constructor
  characterizations, which drive most downstream proofs.
* Vertex membership: `head_mem`, `tail_mem`, `mem_vertexSet`.
* Closure under the `VertexSeq` operations: `prepend`, `append`, `reverse`,
  `dropHead`, `dropTail`, `prefixUntil`, `suffixFrom`, `takeWhile`, `dropWhile`,
  `loopErase`, `cycleErase`, and monotonicity `mono` under passing to a
  subgraph (`SimpleGraph.subgraphOf`).
* Thin `IsSimpleWalkIn` wrappers for the corresponding `SimpleWalk` operations.
* `nonstalling` — a realized sequence never stalls (so it is a `SimpleWalk`),
  because adjacency in a simple graph forces distinct endpoints.

## Design choices

* **Adjacency, not edge sets.** The `cons` step is stated with `G.Adj w.tail u`
  rather than `s(w.tail, u) ∈ E(G)`. The two are definitionally equal, but `Adj`
  is the intended primitive and carries the reusable `symm`/`ne`/`left_mem`/
  `right_mem` API.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## The realized-in predicate -/

/-- A vertex sequence is *realized in* `G` when its head is a vertex of `G` and
each consecutive pair is an edge of `G`. -/
@[grind] inductive IsVertexSeqIn (G : SimpleGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (he : G.Adj w.tail u) :
      IsVertexSeqIn G (w.cons u)

namespace IsVertexSeqIn

/-! ## Constructor characterizations -/

/-- A singleton is realized in `G` exactly when its vertex is in `G`. -/
@[simp, grind =] lemma singleton_iff (G : SimpleGraph α) (v : α) :
    G.IsVertexSeqIn (.singleton v) ↔ v ∈ V(G) :=
  ⟨fun h => by cases h; assumption, IsVertexSeqIn.singleton v⟩

/-- A `cons` is realized in `G` exactly when its prefix is realized and the new
step is an edge. -/
@[simp, grind =] lemma cons_iff (G : SimpleGraph α) (w : VertexSeq α) (u : α) :
    G.IsVertexSeqIn (w.cons u) ↔ G.IsVertexSeqIn w ∧ G.Adj w.tail u := by
  constructor
  · intro h; cases h with | cons w u hw he => exact ⟨hw, he⟩
  · intro ⟨hw, he⟩; exact .cons w u hw he

/-! ## Vertex membership -/

/-- The head of a realized sequence is a vertex of `G`. -/
@[grind →] lemma head_mem (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.head ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw he ih => exact ih

/-- The tail of a realized sequence is a vertex of `G`. -/
@[grind →] lemma tail_mem (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.tail ∈ V(G) := by
  induction hw with
  | singleton v hv => exact hv
  | cons w u hw he ih => exact he.right_mem

/-- Every vertex of a realized sequence is a vertex of `G`. -/
@[grind →] lemma mem_vertexSet (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : ∀ v ∈ w, v ∈ V(G) := by
  induction hw <;> grind [SimpleGraph.Adj.right_mem]

/-- A realized sequence never stalls: consecutive vertices differ, because
adjacency in a simple graph forces distinct endpoints. Hence it underlies a
`SimpleWalk`. -/
@[grind →] lemma nonstalling (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : w.nonstalling := by
  induction hw <;> grind

/-! ## Closure under sequence operations -/

/-- Appending two realized sequences along an edge is realized. -/
@[grind] lemma append (G : SimpleGraph α) {w1 w2 : VertexSeq α}
    (h1 : G.IsVertexSeqIn w1) (h2 : G.IsVertexSeqIn w2)
    (he : G.Adj w1.tail w2.head) : G.IsVertexSeqIn (w1.append w2) := by
  revert he
  induction h2 with
  | singleton v hv => intro he; exact .cons w1 v h1 he
  | cons w u hw hadj ih =>
      intro he
      exact .cons (w1.append w) u (ih he) (by grind [VertexSeq.tail_append])

/-- Prepending a vertex along an edge to the head preserves realization. -/
@[grind →] lemma prepend (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {u : α} (he : G.Adj u w.head) :
    G.IsVertexSeqIn ((VertexSeq.singleton u).append w) :=
  append G (.singleton u he.left_mem) hw he

/-- Reversing a realized sequence preserves realization (adjacency is symmetric
in a simple graph). -/
@[grind →] lemma reverse (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.reverse := by
  induction hw with
  | singleton v hv => exact .singleton v hv
  | cons w u hw he ih =>
      have hu : G.Adj u w.reverse.head := by
        rw [VertexSeq.head_reverse]; exact he.symm
      simpa [VertexSeq.reverse] using prepend G ih hu

/-- Dropping the last vertex preserves realization. -/
@[grind →] lemma dropTail (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropTail := by
  induction hw <;> grind

/-- Dropping the first vertex preserves realization. -/
@[grind →] lemma dropHead (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.dropHead := by
  induction hw with
  | singleton v hv => exact .singleton v hv
  | cons w u hw he ih =>
      cases w with
      | singleton x => exact .singleton u he.right_mem
      | cons t x => exact .cons _ u ih (by rw [VertexSeq.tail_dropHead]; exact he)

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleGraph α) {w : VertexSeq α}
    (hw : H.IsVertexSeqIn w) (hsub : SimpleGraph.subgraphOf H G) :
    G.IsVertexSeqIn w := by
  induction hw with
  | singleton v hv => exact .singleton v (hsub.1 hv)
  | cons w u hw he ih => exact .cons w u ih (hsub.2 he)

/-- Taking the prefix up to the first occurrence of `v` preserves realization. -/
@[grind →] lemma prefixUntil [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) :
    ∀ (v : α) (h : v ∈ w), G.IsVertexSeqIn (w.prefixUntil v h) := by
  induction hw with
  | singleton x hx => intro v h; grind
  | cons w u hw he ih =>
      intro v h
      by_cases h2 : v ∈ w <;> grind

/-- Dropping to the suffix from the first occurrence of `v` preserves
realization. -/
@[grind →] lemma suffixFrom [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) :
    ∀ (v : α) (h : v ∈ w), G.IsVertexSeqIn (w.suffixFrom v h) := by
  induction hw with
  | singleton x hx => intro v h; grind
  | cons w u hw he ih =>
      intro v h
      by_cases h2 : v ∈ w <;>
        grind [VertexSeq.tail_suffixFrom, SimpleGraph.Adj.right_mem]

/-- Taking the longest prefix on which `p` holds (plus its first failure)
preserves realization. -/
lemma takeWhile (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    G.IsVertexSeqIn (w.takeWhile p) := by
  induction hw with
  | singleton x hx => exact .singleton x hx
  | cons w u hw he ih =>
      change G.IsVertexSeqIn (if ∃ v ∈ w.toList, ¬ p v then w.takeWhile p else w.cons u)
      by_cases hc : ∃ v ∈ w.toList, ¬ p v
      · rw [if_pos hc]; exact ih
      · rw [if_neg hc]; exact .cons w u hw he

/-- Dropping the longest prefix on which `p` holds preserves realization. -/
lemma dropWhile (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) (p : α → Prop) [DecidablePred p] :
    ∀ (h : ∃ v ∈ w.toList, ¬ p v), G.IsVertexSeqIn (w.dropWhile p h) := by
  induction hw with
  | singleton x hx => intro h; exact .singleton x hx
  | cons w u hw he ih =>
      intro h
      change G.IsVertexSeqIn
        (if hq : ∃ v ∈ w.toList, ¬ p v then (w.dropWhile p hq).cons u else .singleton u)
      by_cases hc : ∃ v ∈ w.toList, ¬ p v
      · rw [dif_pos hc]
        exact .cons (w.dropWhile p hc) u (ih hc)
          (by rw [VertexSeq.tail_dropWhile]; exact he)
      · rw [dif_neg hc]; exact .singleton u he.right_mem

/-- If `G` has no edges, every realized sequence has length zero. -/
lemma length_eq_zero_of_no_edges (G : SimpleGraph α) (hE : E(G) = ∅)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) : w.length = 0 := by
  induction hw <;> grind

/-- Removing immediate stalls preserves realization. (On a realized — hence
non-stalling — sequence `loopErase` is in fact the identity.) -/
lemma loopErase [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.loopErase := by
  rw [VertexSeq.loopErase_eq_self_of_nonstalling w (nonstalling G hw)]
  exact hw

/-- Cycle erasure preserves realization: dropping the detour between two
occurrences of a vertex keeps the sequence realized in `G`. -/
lemma cycleErase [DecidableEq α] (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) : G.IsVertexSeqIn w.cycleErase := by
  revert hw
  fun_induction VertexSeq.cycleErase w <;>
    intro hw <;> grind [IsVertexSeqIn.prefixUntil, VertexSeq.tail_cycleErase]

/-! ## Edge-set characterization -/

/-- The edge-set view of realization, bridging the adjacency-based inductive
definition: `w` is realized in `G` exactly when its head is a vertex of `G` and
every edge it traverses is an edge of `G`. -/
theorem iff_edges (G : SimpleGraph α) (w : VertexSeq α) :
    G.IsVertexSeqIn w ↔ w.head ∈ V(G) ∧ ∀ e ∈ w.edges, e ∈ E(G) := by
  constructor
  · intro hw
    refine ⟨head_mem G hw, ?_⟩
    induction hw with
    | singleton v hv => intro e he; simp [VertexSeq.edges] at he
    | cons w u hw he ih =>
        intro e hmem
        rw [VertexSeq.mem_edges_cons] at hmem
        rcases hmem with hmem | rfl
        · exact ih e hmem
        · exact he
  · induction w with
    | singleton v => intro h; exact .singleton v h.1
    | cons w u ih =>
        intro h
        rw [cons_iff]
        refine ⟨ih ⟨h.1, fun e he => h.2 e ?_⟩, h.2 s(w.tail, u) ?_⟩
        · rw [VertexSeq.mem_edges_cons]; exact Or.inl he
        · rw [VertexSeq.mem_edges_cons]; exact Or.inr rfl

/-- Any edge traversed by a realized vertex sequence is an edge of the graph. -/
@[grind →] lemma mem_edgeSet_of_mem_edges (G : SimpleGraph α) {w : VertexSeq α}
    (hw : G.IsVertexSeqIn w) {e : Sym2 α} (he : e ∈ w.edges) : e ∈ E(G) :=
  ((iff_edges G w).1 hw).2 e he

/-- The final step of a non-trivial realized vertex sequence is an adjacency in
the graph. -/
@[grind →] lemma adj_dropTail_tail_tail_of_length_ne_zero (G : SimpleGraph α)
    {w : VertexSeq α} (hw : G.IsVertexSeqIn w) (h : w.length ≠ 0) :
    G.Adj w.dropTail.tail w.tail := by
  change s(w.dropTail.tail, w.tail) ∈ E(G)
  exact mem_edgeSet_of_mem_edges G hw
    (by
      rw [VertexSeq.edges_eq_dropTail_concat_of_length_ne_zero w h]
      simp [List.concat_eq_append])

end IsVertexSeqIn

/-! ## Simple walks realized in a graph -/

/-- A simple walk is realized in `G` when its underlying vertex sequence is
realized in `G`. -/
@[grind] def IsSimpleWalkIn (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  G.IsVertexSeqIn w.val

namespace IsSimpleWalkIn

/-! ## Bridge to `IsVertexSeqIn` -/

/-- Realization of a simple walk is realization of its underlying vertex
sequence. -/
@[simp, grind =] lemma isSimpleWalkIn_iff_isVertexSeqIn (G : SimpleGraph α) (w : SimpleWalk α) :
    G.IsSimpleWalkIn w ↔ G.IsVertexSeqIn w.val := Iff.rfl

/-! ## Vertex and edge membership -/

/-- The head of a realized walk is a vertex of `G`. -/
@[grind →] lemma head_mem (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : w.head ∈ V(G) :=
  IsVertexSeqIn.head_mem G hw

/-- The tail of a realized walk is a vertex of `G`. -/
@[grind →] lemma tail_mem (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : w.tail ∈ V(G) :=
  IsVertexSeqIn.tail_mem G hw

/-- Every vertex visited by a realized walk is a vertex of `G`. -/
@[grind →] lemma mem_vertexSet (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : ∀ v ∈ w.support, v ∈ V(G) :=
  IsVertexSeqIn.mem_vertexSet G hw

/-- Any edge traversed by a realized walk is an edge of `G`. -/
@[grind →] lemma mem_edgeSet_of_mem_edges (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) {e : Sym2 α} (he : e ∈ w.edges) : e ∈ E(G) :=
  IsVertexSeqIn.mem_edgeSet_of_mem_edges G hw he

/-- A walk is realized in `G` exactly when its head is a vertex of `G` and every
edge it traverses is an edge of `G`. -/
theorem iff_edges (G : SimpleGraph α) (w : SimpleWalk α) :
    G.IsSimpleWalkIn w ↔ w.head ∈ V(G) ∧ ∀ e ∈ w.edges, e ∈ E(G) :=
  IsVertexSeqIn.iff_edges G w.val

/-! ## Traversed edges and the generated simple graph -/

/-- All edges traversed by a realized simple walk are edges of `G`, as a bundled
edge-list predicate. -/
lemma edges_subset_edgeSet (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : ∀ e ∈ w.edges, e ∈ E(G) :=
  (iff_edges G w).1 hw |>.2

/-- The simple graph generated by a realized simple walk is a subgraph of `G`. -/
lemma toSimpleGraph_subgraphOf (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : SimpleGraph.subgraphOf w.toSimpleGraph G := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact mem_vertexSet G hw v (by simpa using hv)
  · intro e he
    exact mem_edgeSet_of_mem_edges G hw (by simpa using he)

/-- If the graph generated by a simple walk is a subgraph of `G`, then the walk
is realized in `G`. -/
lemma of_toSimpleGraph_subgraphOf (G : SimpleGraph α) {w : SimpleWalk α}
    (hsub : SimpleGraph.subgraphOf w.toSimpleGraph G) : G.IsSimpleWalkIn w := by
  rw [iff_edges]
  refine ⟨?_, ?_⟩
  · exact hsub.1 (by simp [SimpleWalk.support])
  · intro e he
    exact hsub.2 (by simpa using he)

/-- A simple walk is realized in `G` exactly when its generated simple graph is
a subgraph of `G`. -/
theorem iff_toSimpleGraph_subgraphOf (G : SimpleGraph α) (w : SimpleWalk α) :
    G.IsSimpleWalkIn w ↔ SimpleGraph.subgraphOf w.toSimpleGraph G :=
  ⟨toSimpleGraph_subgraphOf G, of_toSimpleGraph_subgraphOf G⟩

/-! ## Closure under walk operations -/

/-- Reversing a realized walk preserves realization. -/
@[grind →] lemma reverse (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn w.reverse :=
  IsVertexSeqIn.reverse G hw

/-- Dropping the last vertex of a realized walk preserves realization. -/
@[grind →] lemma dropTail (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn w.dropTail :=
  IsVertexSeqIn.dropTail G hw

/-- Dropping the first vertex of a realized walk preserves realization. -/
@[grind →] lemma dropHead (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn w.dropHead :=
  IsVertexSeqIn.dropHead G hw

/-- Taking a prefix of a realized walk preserves realization. -/
@[grind →] lemma prefixUntil [DecidableEq α] (G : SimpleGraph α)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) (v : α) (h : v ∈ w.val) :
    G.IsSimpleWalkIn (w.prefixUntil v h) :=
  IsVertexSeqIn.prefixUntil G hw v h

/-- Taking a suffix of a realized walk preserves realization. -/
@[grind →] lemma suffixFrom [DecidableEq α] (G : SimpleGraph α)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) (v : α) (h : v ∈ w.val) :
    G.IsSimpleWalkIn (w.suffixFrom v h) :=
  IsVertexSeqIn.suffixFrom G hw v h

/-- Taking the longest prefix on which `p` holds (plus its first failure)
preserves realization. -/
lemma takeWhile (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) (p : α → Prop) [DecidablePred p] :
    G.IsSimpleWalkIn (w.takeWhile p) :=
  IsVertexSeqIn.takeWhile G hw p

/-- Dropping the longest prefix on which `p` holds preserves realization. -/
lemma dropWhile (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.val.toList, ¬ p v) :
    G.IsSimpleWalkIn (w.dropWhile p h) :=
  IsVertexSeqIn.dropWhile G hw p h

/-- Loop erasure preserves realization. On a simple walk this operation is the
identity on the underlying sequence. -/
lemma loopErase [DecidableEq α] (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn (w.loopErase) :=
  IsVertexSeqIn.loopErase G hw

/-- Cycle erasure preserves realization. -/
lemma cycleErase [DecidableEq α] (G : SimpleGraph α) {w : SimpleWalk α}
    (hw : G.IsSimpleWalkIn w) : G.IsSimpleWalkIn (w.cycleErase) :=
  IsVertexSeqIn.cycleErase G hw

/-- Realization is monotone under passing to a supergraph. -/
@[grind →] lemma mono (G H : SimpleGraph α) {w : SimpleWalk α}
    (hw : H.IsSimpleWalkIn w) (hsub : SimpleGraph.subgraphOf H G) :
    G.IsSimpleWalkIn w :=
  IsVertexSeqIn.mono G H hw hsub

/-- If `G` has no edges, every realized walk in `G` has length zero. -/
lemma length_eq_zero_of_no_edges (G : SimpleGraph α) (hE : E(G) = ∅)
    {w : SimpleWalk α} (hw : G.IsSimpleWalkIn w) : w.length = 0 :=
  IsVertexSeqIn.length_eq_zero_of_no_edges G hE hw

/-! ## Joining walks -/

/-- Appending two realized walks along an edge of `G` preserves realization. -/
lemma append (G : SimpleGraph α) {p q : SimpleWalk α}
    (hp : G.IsSimpleWalkIn p) (hq : G.IsSimpleWalkIn q)
    (he : G.Adj p.tail q.head) :
    G.IsSimpleWalkIn (p.append q he.ne) :=
  IsVertexSeqIn.append G hp hq he

/-- Gluing two realized walks at a shared endpoint preserves realization. -/
lemma glue (G : SimpleGraph α) {p q : SimpleWalk α}
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

end SimpleGraph

end GraphLib
