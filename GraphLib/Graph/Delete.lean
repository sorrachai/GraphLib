/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Graph.Adjacency
import GraphLib.Graph.Subgraph

/-!
# Deleting vertices and edges

`GraphLib.Graph.Subgraph` provides the *induced* subgraph `G[S]`, which keeps the
vertices of `G` lying in `S`. This file provides the two complementary deletion
operations, which are what connectivity arguments are actually phrased with: remove
a set of edges, or remove a set of vertices.

## Main definitions

* `SimpleGraph.deleteEdges G F` — remove the edges `F` from `G`, keeping every vertex.
* `SimpleGraph.deleteVertices G S` — remove the vertices `S` from `G`, together with
  every edge incident to one of them.

## Design choices

* **Edge deletion keeps the vertex set.** Deleting an edge must not silently delete
  the vertices it left isolated: edge connectivity and the edge boundary both depend
  on the vertex set staying fixed. So `V(G.deleteEdges F) = V(G)` holds by `rfl`.
* **Vertex deletion is a structure literal, not `induce`.** `deleteVertices G S` is
  equal to `G.induce Sᶜ` (see `deleteVertices_eq_induce`), but writing it directly
  gives `V(G.deleteVertices S) = V(G) \ S` and the membership characterization of its
  edge set *definitionally*. Going through `induce` would instead produce
  `Sᶜ ∩ V(G)`, forcing a normalization step at every use site in the connectivity
  development. The bridge lemma makes the `induce` API available anyway.
* **`SimpleGraph` only.** Unlike `Subgraph.lean`, we do not repeat these for `Graph`,
  `DiGraph` and `SimpleDiGraph`. Only the simple case is needed downstream, and edge
  deletion on the labelled types has a genuine design question (delete by label or by
  endpoint pair?) that should not be settled here as a side effect.
-/

namespace GraphLib
variable {α : Type*}

open scoped GraphLib

/-! ## Edge deletion -/

/-- Delete a set of edges from `G`, keeping every vertex. Both structure axioms are
inherited from `G`: shrinking the edge set can neither break incidence nor create a
loop. -/
def SimpleGraph.deleteEdges (G : SimpleGraph α) (F : Set (Sym2 α)) : SimpleGraph α where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet \ F
  incidence' := fun e he v hv => G.incidence' e he.1 v hv
  loopless' := fun e he => G.loopless' e he.1

/-- Deleting edges leaves the vertex set unchanged. -/
@[simp, grind =] lemma SimpleGraph.vertexSet_deleteEdges (G : SimpleGraph α)
    (F : Set (Sym2 α)) : V(G.deleteEdges F) = V(G) := rfl

/-- The surviving edges are exactly those of `G` outside `F`. -/
@[simp, grind =] lemma SimpleGraph.mem_edgeSet_deleteEdges {G : SimpleGraph α}
    {F : Set (Sym2 α)} {e : Sym2 α} : e ∈ E(G.deleteEdges F) ↔ e ∈ E(G) ∧ e ∉ F :=
  Iff.rfl

/-- Two vertices stay adjacent after deleting `F` exactly when they were adjacent and
their edge was not deleted. -/
@[simp, grind =] lemma SimpleGraph.adj_deleteEdges {G : SimpleGraph α}
    {F : Set (Sym2 α)} {u v : α} :
    (G.deleteEdges F).Adj u v ↔ G.Adj u v ∧ s(u, v) ∉ F := Iff.rfl

/-- Deleting no edges changes nothing. -/
@[simp] lemma SimpleGraph.deleteEdges_empty (G : SimpleGraph α) :
    G.deleteEdges ∅ = G := by
  cases G; simp [SimpleGraph.deleteEdges]

/-- Deleting edges yields a subgraph. -/
@[grind] lemma SimpleGraph.deleteEdges_subgraphOf (G : SimpleGraph α)
    (F : Set (Sym2 α)) : SimpleGraph.subgraphOf (G.deleteEdges F) G :=
  ⟨subset_rfl, Set.diff_subset⟩

/-- Deleting more edges yields a smaller graph. -/
lemma SimpleGraph.deleteEdges_mono (G : SimpleGraph α) {F₁ F₂ : Set (Sym2 α)}
    (h : F₁ ⊆ F₂) : SimpleGraph.subgraphOf (G.deleteEdges F₂) (G.deleteEdges F₁) :=
  ⟨subset_rfl, Set.diff_subset_diff_right h⟩

/-! ## Vertex deletion -/

/-- Delete a set of vertices from `G`, together with every edge incident to one of
them. -/
def SimpleGraph.deleteVertices (G : SimpleGraph α) (S : Set α) : SimpleGraph α where
  vertexSet := G.vertexSet \ S
  edgeSet := {e ∈ G.edgeSet | ∀ v ∈ e, v ∉ S}
  incidence' := fun e he v hv => ⟨G.incidence' e he.1 v hv, he.2 v hv⟩
  loopless' := fun e he => G.loopless' e he.1

/-- Deleting `S` leaves exactly the vertices of `G` outside `S`. -/
@[simp, grind =] lemma SimpleGraph.vertexSet_deleteVertices (G : SimpleGraph α)
    (S : Set α) : V(G.deleteVertices S) = V(G) \ S := rfl

/-- The surviving edges are those of `G` avoiding `S` entirely. -/
@[simp, grind =] lemma SimpleGraph.mem_edgeSet_deleteVertices {G : SimpleGraph α}
    {S : Set α} {e : Sym2 α} :
    e ∈ E(G.deleteVertices S) ↔ e ∈ E(G) ∧ ∀ v ∈ e, v ∉ S := Iff.rfl

/-- Two vertices stay adjacent after deleting `S` exactly when they were adjacent and
neither was deleted. -/
@[simp, grind =] lemma SimpleGraph.adj_deleteVertices {G : SimpleGraph α}
    {S : Set α} {u v : α} :
    (G.deleteVertices S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := by
  constructor
  · rintro ⟨he, hS⟩
    exact ⟨he, hS u (Sym2.mem_mk_left u v), hS v (Sym2.mem_mk_right u v)⟩
  · rintro ⟨he, hu, hv⟩
    refine ⟨he, fun w hw => ?_⟩
    rcases Sym2.mem_iff.1 hw with rfl | rfl <;> assumption

/-- Deleting no vertices changes nothing. -/
@[simp] lemma SimpleGraph.deleteVertices_empty (G : SimpleGraph α) :
    G.deleteVertices ∅ = G := by
  cases G; simp [SimpleGraph.deleteVertices]

/-- Deleting vertices yields a subgraph. -/
@[grind] lemma SimpleGraph.deleteVertices_subgraphOf (G : SimpleGraph α) (S : Set α) :
    SimpleGraph.subgraphOf (G.deleteVertices S) G :=
  ⟨Set.diff_subset, fun _ he => he.1⟩

/-- Deleting more vertices yields a smaller graph. -/
lemma SimpleGraph.deleteVertices_mono (G : SimpleGraph α) {S₁ S₂ : Set α}
    (h : S₁ ⊆ S₂) :
    SimpleGraph.subgraphOf (G.deleteVertices S₂) (G.deleteVertices S₁) :=
  ⟨Set.diff_subset_diff_right h, fun _ he => ⟨he.1, fun v hv => fun hv₁ => he.2 v hv (h hv₁)⟩⟩

/-- Vertex deletion is the subgraph induced on the complement. This is the bridge that
makes the `induce` API of `GraphLib.Graph.Subgraph` available for `deleteVertices`. -/
lemma SimpleGraph.deleteVertices_eq_induce (G : SimpleGraph α) (S : Set α) :
    G.deleteVertices S = G.induce Sᶜ := by
  cases G
  simp only [SimpleGraph.deleteVertices, SimpleGraph.induce, SimpleGraph.mk.injEq]
  refine ⟨?_, rfl⟩
  rw [Set.diff_eq, Set.inter_comm]

end GraphLib
