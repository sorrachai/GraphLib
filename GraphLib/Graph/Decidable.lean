/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Graph.Delete
import GraphLib.Graph.Finite
import GraphLib.Util.Decidable

/-!
# Decidable graph predicates

`GraphLib.Graph.Finite` provides `computeVertexFinset` / `computeEdgeFinset`: `Finset`
views of a graph that are genuinely constructive, at the price of demanding data
(`[Fintype G.vertexSet]`, `[DecidablePred (· ∈ G.edgeSet)]`) where the `Prop`-level
development only demands `[Finite V(G)]`. This file turns those views into *decision
procedures*: adjacency becomes decidable, and the deletion operations of
`GraphLib.Graph.Delete` propagate the finiteness and decidability data to the deleted
graph, so that a predicate about `G.deleteVertices S` is decidable whenever the
corresponding predicate about `G` is.

Reachability and connectedness are decided in `GraphLib.Theory.Connectivity.Computable`,
on top of what is here.

## Main results

* `SimpleGraph.instDecidableRelAdj` — adjacency is decidable when edge membership is.
* Instances propagating `Fintype` on the vertex set and `DecidablePred` on the edge set
  through `SimpleGraph.deleteEdges` and `SimpleGraph.deleteVertices`.
* Instances stating the same data in the `V(·)` / `E(·)` notation, which is how the
  connectivity predicates are phrased.

## Design choices

* **`DecidableRel G.Adj` is an instance, not a hypothesis.** The connectivity
  development deliberately keeps `Decidable` / `DecidableEq` out of the *statements* of
  its `Prop`s (see the design note in `GraphLib.Theory.Connectivity.Reachable`). That
  policy is about `Prop`s, not about instance search: `Adj G u v` is by definition
  `s(u, v) ∈ E(G)`, so an instance deriving its decidability from
  `[DecidablePred (· ∈ G.edgeSet)]` consumes a hypothesis the caller already had to
  supply and changes no statement. Instance search simply fails when it is absent.
* **Both spellings of the vertex and edge sets are registered.** `V(G)` is
  `HasVertexSet.vertexSet G`, a different head symbol from `G.vertexSet`, so instance
  search does not pass between them. The bridge instances below are the single place
  in the library where that gap is closed; downstream files should never work around it
  again.
* **Deletion instances are spelled out.** The membership lemmas of
  `GraphLib.Graph.Delete` are all `Iff.rfl`, so these instances hold by `rfl`; writing
  them explicitly keeps instance search from having to unfold structure literals.
-/

namespace GraphLib

variable {α : Type*}

open scoped GraphLib

/-! ## Bridging the `V(·)` / `E(·)` notation -/

/-- Membership in `V(G)` and in `G.vertexSet` are the same statement. As a `simp` lemma
this is the single normalization step that lets the `Finset` API of
`GraphLib.Graph.Finite` — stated with the projections — meet the connectivity
predicates, which are stated with the notation. -/
@[simp] lemma SimpleGraph.mem_vertexSet_notation (G : SimpleGraph α) {v : α} :
    v ∈ (V(G) : Set α) ↔ v ∈ G.vertexSet := Iff.rfl

/-- The `E(·)` counterpart of `SimpleGraph.mem_vertexSet_notation`. -/
@[simp] lemma SimpleGraph.mem_edgeSet_notation (G : SimpleGraph α) {e : Sym2 α} :
    e ∈ (E(G) : Set (Sym2 α)) ↔ e ∈ G.edgeSet := Iff.rfl

/-- The `V(·)` spelling of `[Fintype G.vertexSet]`. -/
instance SimpleGraph.instFintypeVertexSetNotation (G : SimpleGraph α)
    [Fintype G.vertexSet] : Fintype (V(G) : Set α) :=
  inferInstanceAs (Fintype G.vertexSet)

/-- Membership in the vertex set is decidable once it is finite. Mathlib keeps
`Set.decidableMemOfFintype` a `def` rather than an instance, since it would apply to
every `Set` and diverge; restricting it to `G.vertexSet` is safe, and it is what the
`S ⊆ V(G)` conjunct of every cut predicate needs. -/
instance SimpleGraph.instDecidablePredMemVertexSet (G : SimpleGraph α) [DecidableEq α]
    [Fintype G.vertexSet] : DecidablePred (· ∈ G.vertexSet) :=
  Set.decidableMemOfFintype _

/-- The `V(·)` spelling of `SimpleGraph.instDecidablePredMemVertexSet`. -/
instance SimpleGraph.instDecidablePredMemVertexSetNotation (G : SimpleGraph α)
    [DecidableEq α] [Fintype G.vertexSet] : DecidablePred (· ∈ (V(G) : Set α)) :=
  inferInstanceAs (DecidablePred (· ∈ G.vertexSet))

/-- The `E(·)` spelling of `[DecidablePred (· ∈ G.edgeSet)]`. -/
instance SimpleGraph.instDecidablePredMemEdgeSetNotation (G : SimpleGraph α)
    [DecidablePred (· ∈ G.edgeSet)] : DecidablePred (· ∈ (E(G) : Set (Sym2 α))) :=
  inferInstanceAs (DecidablePred (· ∈ G.edgeSet))

/-! ## Decidable adjacency -/

/-- Adjacency is decidable exactly when edge membership is: `G.Adj u v` is by
definition `s(u, v) ∈ E(G)`. -/
instance SimpleGraph.instDecidableRelAdj (G : SimpleGraph α)
    [DecidablePred (· ∈ G.edgeSet)] : DecidableRel G.Adj :=
  fun u v => decidable_of_iff (s(u, v) ∈ G.edgeSet) Iff.rfl

/-! ## The neighbour finset

The one *definition* in this file, rather than an instance. It lives here rather than
beside `computeVertexFinset` in `GraphLib.Graph.Finite` because it is exactly the
`Finset` that decidable adjacency buys: the neighbours of `v` are the vertices the
adjacency test accepts.

TODO: once `GraphLib.Graph.Degree` compiles, add
`coe_computeNeighborFinset : ↑(G.computeNeighborFinset v) = G.neighborSet v`, and keep
the `compute` prefix — `Degree.lean` reserves the plain name `neighborFinset` for the
`[Finite V(G)]` variant. -/

/-- The neighbours of `v` in `G`, as a `Finset`. -/
def SimpleGraph.computeNeighborFinset (G : SimpleGraph α) [DecidableEq α]
    [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] (v : α) : Finset α :=
  G.computeVertexFinset.filter (G.Adj v ·)

@[simp] lemma SimpleGraph.mem_computeNeighborFinset (G : SimpleGraph α) [DecidableEq α]
    [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] {v u : α} :
    u ∈ G.computeNeighborFinset v ↔ G.Adj v u := by
  simp only [computeNeighborFinset, Finset.mem_filter, mem_computeVertexFinset]
  exact ⟨And.right, fun h => ⟨h.right_mem, h⟩⟩

lemma SimpleGraph.computeNeighborFinset_subset (G : SimpleGraph α) [DecidableEq α]
    [Fintype G.vertexSet] [DecidablePred (· ∈ G.edgeSet)] (v : α) :
    G.computeNeighborFinset v ⊆ G.computeVertexFinset :=
  Finset.filter_subset _ _

/-! ## Propagating the data through deletions -/

/-- Edge deletion keeps the vertex set, hence its `Fintype`. -/
instance SimpleGraph.instFintypeVertexSetDeleteEdges (G : SimpleGraph α)
    (F : Set (Sym2 α)) [Fintype G.vertexSet] :
    Fintype (G.deleteEdges F).vertexSet :=
  inferInstanceAs (Fintype G.vertexSet)

/-- Membership in the edge set after deleting `F` is decidable. -/
instance SimpleGraph.instDecidablePredMemEdgeSetDeleteEdges (G : SimpleGraph α)
    (F : Set (Sym2 α)) [DecidablePred (· ∈ G.edgeSet)] [DecidablePred (· ∈ F)] :
    DecidablePred (· ∈ (G.deleteEdges F).edgeSet) := fun e =>
  decidable_of_iff (e ∈ G.edgeSet ∧ e ∉ F) Iff.rfl

/-- Vertex deletion cuts the vertex set down to a difference, which stays finite. -/
instance SimpleGraph.instFintypeVertexSetDeleteVertices (G : SimpleGraph α)
    (S : Set α) [Fintype G.vertexSet] [DecidablePred (· ∈ S)] :
    Fintype (G.deleteVertices S).vertexSet :=
  inferInstanceAs (Fintype (G.vertexSet \ S : Set α))

/-- Membership in the edge set after deleting `S` is decidable; the surviving edges are
those avoiding `S` at both endpoints, decided by `Sym2.decidableForallMem`. -/
instance SimpleGraph.instDecidablePredMemEdgeSetDeleteVertices (G : SimpleGraph α)
    (S : Set α) [DecidablePred (· ∈ G.edgeSet)] [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ (G.deleteVertices S).edgeSet) := fun e =>
  decidable_of_iff (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∉ S) Iff.rfl

/-! ## Sanity checks

These confirm that the instances compose, and — the point of the exercise — that the
`[Fintype G.vertexSet]` binder style used throughout `GraphLib.Graph.Finite` is found by
instance search when the goal is phrased with the `V(·)` notation instead. -/

example (G : SimpleGraph α) (S : Set α) [Fintype G.vertexSet] [DecidablePred (· ∈ S)] :
    Fintype (G.deleteVertices S).vertexSet := inferInstance

example (G : SimpleGraph α) (S : Set α) [DecidablePred (· ∈ G.edgeSet)]
    [DecidablePred (· ∈ S)] : DecidablePred (· ∈ (G.deleteVertices S).edgeSet) :=
  inferInstance

example (G : SimpleGraph α) (S : Set α) [Fintype G.vertexSet] [DecidablePred (· ∈ S)] :
    Fintype V(G.deleteVertices S) := inferInstance

example (G : SimpleGraph α) (S : Set α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] [DecidablePred (· ∈ S)]
    [Fintype S] : Decidable (S ⊆ V(G) ∧ (V(G) \ S).Subsingleton) := inferInstance

end GraphLib
