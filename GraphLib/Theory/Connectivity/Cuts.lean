/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Theory.Connectivity.Components

/-!
# Cuts, separators and boundaries

A *cut* is a set whose deletion destroys connectivity. This file gives the vertex and
edge versions, both globally (disconnect the whole graph) and locally (separate two
prescribed vertices, or two prescribed sets of vertices), together with the edge
boundary of a vertex set.

## Main definitions

* `SimpleGraph.edgeBoundary G S` — the edges with exactly one endpoint in `S`,
  written `∂(G, S)`.
* `SimpleGraph.IsVertexCut G S` / `SimpleGraph.IsEdgeCut G F` — deleting `S` (resp. `F`)
  disconnects `G`.
* `SimpleGraph.IsCutVertex G v` / `SimpleGraph.IsCutEdge G e` — the singleton cases.
* `SimpleGraph.IsSTVertexCut G A B S` / `SimpleGraph.IsSTEdgeCut G A B F` — deleting the
  set separates every vertex of `A` from every vertex of `B`.
* `SimpleGraph.IsVertexSeparator G S u v` / `SimpleGraph.IsEdgeSeparator G F u v` — the
  two-terminal special case.

## Design choices

* **Three distinct notions, not three names for one.** A *cut* is global: it disconnects
  the graph. A *separator* is local to a pair of vertices. An *S–T cut* is local to a
  pair of vertex *sets*, as in flow theory and Menger's theorem. Stating all three
  keeps each one at the abstraction level where it is actually used, and the two local
  notions are defined in terms of one another so there is only one thing to prove about.
* **Cuts are phrased as `¬ IsPreconnected`, not as a component count.** "`G - S` has more
  than one connected component" is the textbook wording (Definition 3.1(i)), and
  `not_isPreconnected_iff_components_nontrivial` shows the two agree. Working with
  `¬ IsPreconnected` avoids cardinal arithmetic in every downstream proof, and sidesteps
  the trap that `Set.ncard` is `0` — not `⊤` — on a graph with infinitely many
  components. See the design notes in `GraphLib.Theory.Connectivity.Components`.
* **Separators must avoid their terminals; S–T cuts need not.** `IsVertexSeparator G S u v`
  requires `u ∉ S` and `v ∉ S`: without it, `S = {u}` would separate `u` from everything
  vacuously. For `IsSTVertexCut` the Menger convention is the opposite — the cut is
  allowed to meet `A` and `B`, and a terminal inside the cut is simply no longer a vertex.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## The edge boundary -/

/-- The *edge boundary* of `S` in `G`: the edges of `G` with one endpoint in `S` and one
endpoint outside `S`. Since an edge of a simple graph has two distinct endpoints, this
is the same as "exactly one endpoint in `S`". -/
def edgeBoundary (G : SimpleGraph α) (S : Set α) : Set (Sym2 α) :=
  {e ∈ E(G) | (∃ u ∈ e, u ∈ S) ∧ (∃ v ∈ e, v ∉ S)}

end SimpleGraph

/-- `∂(G, S)` is the set of edges of `G` with exactly one endpoint in `S`.

Declared here, directly inside `namespace GraphLib` rather than inside
`namespace SimpleGraph`, so that `scoped` attaches it to `GraphLib` and a plain
`open scoped GraphLib` brings it into scope alongside `V(G)` and `E(G)`. -/
scoped notation "∂(" G ", " S ")" => GraphLib.SimpleGraph.edgeBoundary G S

namespace SimpleGraph

/-- An edge lies in the boundary of `S` exactly when it joins `S` to its complement. -/
@[simp] lemma mem_edgeBoundary {G : SimpleGraph α} {S : Set α} {u v : α} :
    s(u, v) ∈ ∂(G, S) ↔ G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) := by
  constructor
  · rintro ⟨he, ⟨a, ha, haS⟩, ⟨b, hb, hbS⟩⟩
    refine ⟨he, ?_⟩
    rcases Sym2.mem_iff.1 ha with rfl | rfl <;> rcases Sym2.mem_iff.1 hb with rfl | rfl <;>
      simp_all
  · rintro ⟨he, hcase⟩
    refine ⟨he, ?_⟩
    rcases hcase with ⟨huS, hvS⟩ | ⟨huS, hvS⟩
    · exact ⟨⟨u, Sym2.mem_mk_left u v, huS⟩, ⟨v, Sym2.mem_mk_right u v, hvS⟩⟩
    · exact ⟨⟨v, Sym2.mem_mk_right u v, hvS⟩, ⟨u, Sym2.mem_mk_left u v, huS⟩⟩

/-- The boundary consists of edges of `G`. -/
lemma edgeBoundary_subset (G : SimpleGraph α) (S : Set α) : ∂(G, S) ⊆ E(G) :=
  fun _ he => he.1

/-- The empty set has empty boundary. -/
@[simp] lemma edgeBoundary_empty (G : SimpleGraph α) : ∂(G, (∅ : Set α)) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ he => (he.2.1.choose_spec.2).elim

/-- A set and its complement have the same boundary. -/
lemma edgeBoundary_compl (G : SimpleGraph α) (S : Set α) : ∂(G, Sᶜ) = ∂(G, S) := by
  ext e
  simp only [edgeBoundary, Set.mem_setOf_eq, Set.mem_compl_iff, not_not]
  tauto

/-! ## Global cuts -/

/-- Definition 3.1.(i). A *vertex cut* of `G` is a set `S` of vertices of `G` whose
deletion leaves more than one connected component, i.e. leaves two vertices mutually
unreachable. -/
def IsVertexCut (G : SimpleGraph α) (S : Set α) : Prop :=
  S ⊆ V(G) ∧ ¬ (G.deleteVertices S).IsPreconnected

/-- An *edge cut* of `G` is a set `F` of edges of `G` whose deletion leaves more than one
connected component. -/
def IsEdgeCut (G : SimpleGraph α) (F : Set (Sym2 α)) : Prop :=
  F ⊆ E(G) ∧ ¬ (G.deleteEdges F).IsPreconnected

/-- A vertex cut leaves at least two connected components: this is the literal reading of
Definition 3.1.(i). -/
lemma IsVertexCut.one_lt_numComponents {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : 1 < (G.deleteVertices S).numComponents :=
  one_lt_numComponents_of_not_isPreconnected h.2

/-- An edge cut leaves at least two connected components. -/
lemma IsEdgeCut.one_lt_numComponents {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeCut F) : 1 < (G.deleteEdges F).numComponents :=
  one_lt_numComponents_of_not_isPreconnected h.2

/-- The empty set is a vertex cut exactly when `G` is already disconnected. -/
lemma isVertexCut_empty_iff {G : SimpleGraph α} :
    G.IsVertexCut ∅ ↔ ¬ G.IsPreconnected := by
  simp [IsVertexCut]

/-- The empty set is an edge cut exactly when `G` is already disconnected. -/
lemma isEdgeCut_empty_iff {G : SimpleGraph α} :
    G.IsEdgeCut ∅ ↔ ¬ G.IsPreconnected := by
  simp [IsEdgeCut]

/-- A graph with a vertex cut is not preconnected, provided the cut is not everything.
More precisely: deleting vertices can only ever break connectivity, so a graph that
survives having `S` deleted was preconnected to begin with only if the surviving
reachabilities lift — which they do. -/
lemma not_isPreconnected_deleteVertices_of_isVertexCut {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : ¬ (G.deleteVertices S).IsPreconnected := h.2

/-! ## Cut vertices and cut edges -/

/-- Definition 3.1.(ii). A *cut vertex* of `G` is a vertex `v` such that `{v}` is a
vertex cut.

As with every textbook statement of this definition, it is the intended notion for a
connected `G`: in an already-disconnected graph every vertex satisfies it vacuously. -/
def IsCutVertex (G : SimpleGraph α) (v : α) : Prop := G.IsVertexCut {v}

/-- Definition 2.5. A *cut edge* (or *bridge*) of `G` is an edge whose deletion
disconnects `G`. Same caveat as `IsCutVertex`. -/
def IsCutEdge (G : SimpleGraph α) (e : Sym2 α) : Prop := G.IsEdgeCut {e}

/-- Unfolding a cut vertex. -/
lemma isCutVertex_iff {G : SimpleGraph α} {v : α} :
    G.IsCutVertex v ↔ v ∈ V(G) ∧ ¬ (G.deleteVertices {v}).IsPreconnected := by
  simp [IsCutVertex, IsVertexCut, Set.singleton_subset_iff]

/-- Unfolding a cut edge. -/
lemma isCutEdge_iff {G : SimpleGraph α} {e : Sym2 α} :
    G.IsCutEdge e ↔ e ∈ E(G) ∧ ¬ (G.deleteEdges {e}).IsPreconnected := by
  simp [IsCutEdge, IsEdgeCut, Set.singleton_subset_iff]

/-- A cut vertex is a vertex. -/
lemma IsCutVertex.mem {G : SimpleGraph α} {v : α} (h : G.IsCutVertex v) : v ∈ V(G) :=
  isCutVertex_iff.1 h |>.1

/-- A cut edge is an edge. -/
lemma IsCutEdge.mem {G : SimpleGraph α} {e : Sym2 α} (h : G.IsCutEdge e) : e ∈ E(G) :=
  isCutEdge_iff.1 h |>.1

/-! ## Separators between two sets of vertices -/

/-- `S` is an *`A`–`B` vertex cut* of `G`: after deleting `S`, no vertex of `A` reaches a
vertex of `B`.

Following Menger, `S` may meet `A` and `B`; a terminal lying in `S` is simply not a
vertex of `G - S` any more, so the condition on it holds vacuously. -/
def IsSTVertexCut (G : SimpleGraph α) (A B S : Set α) : Prop :=
  S ⊆ V(G) ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ (G.deleteVertices S).Reachable a b

/-- `F` is an *`A`–`B` edge cut* of `G`: after deleting the edges `F`, no vertex of `A`
reaches a vertex of `B`. -/
def IsSTEdgeCut (G : SimpleGraph α) (A B : Set α) (F : Set (Sym2 α)) : Prop :=
  F ⊆ E(G) ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ (G.deleteEdges F).Reachable a b

/-- Shrinking the source set preserves being an `A`–`B` vertex cut. -/
lemma IsSTVertexCut.mono_left {G : SimpleGraph α} {A A' B S : Set α}
    (h : G.IsSTVertexCut A B S) (hA : A' ⊆ A) : G.IsSTVertexCut A' B S :=
  ⟨h.1, fun a ha b hb => h.2 a (hA ha) b hb⟩

/-- Shrinking the target set preserves being an `A`–`B` vertex cut. -/
lemma IsSTVertexCut.mono_right {G : SimpleGraph α} {A B B' S : Set α}
    (h : G.IsSTVertexCut A B S) (hB : B' ⊆ B) : G.IsSTVertexCut A B' S :=
  ⟨h.1, fun a ha b hb => h.2 a ha b (hB hb)⟩

/-- Shrinking the source set preserves being an `A`–`B` edge cut. -/
lemma IsSTEdgeCut.mono_left {G : SimpleGraph α} {A A' B : Set α} {F : Set (Sym2 α)}
    (h : G.IsSTEdgeCut A B F) (hA : A' ⊆ A) : G.IsSTEdgeCut A' B F :=
  ⟨h.1, fun a ha b hb => h.2 a (hA ha) b hb⟩

/-- Shrinking the target set preserves being an `A`–`B` edge cut. -/
lemma IsSTEdgeCut.mono_right {G : SimpleGraph α} {A B B' : Set α} {F : Set (Sym2 α)}
    (h : G.IsSTEdgeCut A B F) (hB : B' ⊆ B) : G.IsSTEdgeCut A B' F :=
  ⟨h.1, fun a ha b hb => h.2 a ha b (hB hb)⟩

/-! ## Separators between two vertices -/

/-- `S` is a *`u`–`v` vertex separator* of `G`: `S` avoids both terminals, and after
deleting `S` there is no walk from `u` to `v`.

The avoidance condition is essential: without it `S = {u}` would separate `u` from
everything, vacuously. -/
def IsVertexSeparator (G : SimpleGraph α) (S : Set α) (u v : α) : Prop :=
  u ∉ S ∧ v ∉ S ∧ G.IsSTVertexCut {u} {v} S

/-- `F` is a *`u`–`v` edge separator* of `G`: after deleting the edges `F` there is no
walk from `u` to `v`. No avoidance condition is needed, since edges have no terminals to
avoid. -/
def IsEdgeSeparator (G : SimpleGraph α) (F : Set (Sym2 α)) (u v : α) : Prop :=
  G.IsSTEdgeCut {u} {v} F

/-- Unfolding a vertex separator to a statement about reachability. -/
lemma isVertexSeparator_iff {G : SimpleGraph α} {S : Set α} {u v : α} :
    G.IsVertexSeparator S u v ↔
      u ∉ S ∧ v ∉ S ∧ S ⊆ V(G) ∧ ¬ (G.deleteVertices S).Reachable u v := by
  simp [IsVertexSeparator, IsSTVertexCut]

/-- Unfolding an edge separator to a statement about reachability. -/
lemma isEdgeSeparator_iff {G : SimpleGraph α} {F : Set (Sym2 α)} {u v : α} :
    G.IsEdgeSeparator F u v ↔ F ⊆ E(G) ∧ ¬ (G.deleteEdges F).Reachable u v := by
  simp [IsEdgeSeparator, IsSTEdgeCut]

/-- A vertex separator between two distinct vertices of `G` is a vertex cut: the two
terminals survive the deletion and are mutually unreachable in what remains. -/
lemma IsVertexSeparator.isVertexCut {G : SimpleGraph α} {S : Set α} {u v : α}
    (h : G.IsVertexSeparator S u v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    G.IsVertexCut S := by
  obtain ⟨hus, hvs, hsub, hreach⟩ := isVertexSeparator_iff.1 h
  exact ⟨hsub, fun hpre => hreach (hpre u ⟨hu, hus⟩ v ⟨hv, hvs⟩)⟩

/-- An edge separator between two vertices of `G` is an edge cut. -/
lemma IsEdgeSeparator.isEdgeCut {G : SimpleGraph α} {F : Set (Sym2 α)} {u v : α}
    (h : G.IsEdgeSeparator F u v) (hu : u ∈ V(G)) (hv : v ∈ V(G)) :
    G.IsEdgeCut F := by
  obtain ⟨hsub, hreach⟩ := isEdgeSeparator_iff.1 h
  exact ⟨hsub, fun hpre => hreach (hpre u hu v hv)⟩

/-- Conversely, a graph that is not preconnected after deleting `S` has two vertices that
`S` separates. -/
lemma IsVertexCut.exists_isVertexSeparator {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : ∃ u v, G.IsVertexSeparator S u v := by
  obtain ⟨u, ⟨-, hus⟩, v, ⟨-, hvs⟩, hreach⟩ := not_isPreconnected_iff.1 h.2
  refine ⟨u, v, hus, hvs, h.1, ?_⟩
  rintro a rfl b rfl
  exact hreach

end SimpleGraph

end GraphLib
