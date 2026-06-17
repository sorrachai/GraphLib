/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai
-/
import GraphLib.Graph.Basic

/-!
# Subgraphs and induced subgraphs

This file equips each of the four graph structures from
`GraphLib.Graph.Basic` (`Graph`, `SimpleGraph`, `DiGraph`, `SimpleDiGraph`)
with a subgraph predicate and an induced-subgraph constructor.

## Main definitions

* `Graph.subgraphOf`, `SimpleGraph.subgraphOf`, `DiGraph.subgraphOf`,
  `SimpleDiGraph.subgraphOf` — `H` is a subgraph of `G` when its vertex
  set and edge set are both contained in those of `G`.
* `Graph.induce`, `SimpleGraph.induce`, `DiGraph.induce`,
  `SimpleDiGraph.induce` — the subgraph induced by a vertex set `S`,
  obtained by keeping only the vertices of `G` that lie in `S` and the
  edges of `G` whose endpoints all lie in `S`.

## Notation

* `G[S]`: the subgraph of `G` induced by `S`, provided by `GetElem`
  instances on each of the four graph structures.

## Design choices

* **One predicate per graph type.** We give `subgraphOf` a separate
  definition for each of the four graph structures rather than
  factoring through a `HasSubgraph` typeclass. This keeps the
  definitions concrete and avoids introducing typeclass machinery
  before downstream files have any use for it.
* **Compare structure fields, not projections.** For the labelled types
  `Graph` and `DiGraph`, we compare the underlying `edgeSet : Set (Edge α β)`
  / `Set (Arc α β)` rather than the `E(G)` projection to `Sym2 α`
  / `α × α`. Two parallel edges with different labels are distinct in
  the labelled world, and `subgraphOf` should respect that.
* **Induced on a `Set`, intersected with `V(G)`.** Vertex sets are
  `Set α`, and the induced subgraph takes a set `S : Set α` and uses
  `S ∩ V(G)` as the new vertex set. This makes `induce` well-behaved
  even when `S` mentions vertices outside `V(G)` and ensures the
  result is always literally a subgraph of `G`.
* **No looseness lemma is needed.** The induced edge set is carved from
  `G.edgeSet`, so `loopless'` (when present) is inherited verbatim from
  `G`; no separate looplessness obligation appears.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Subgraph relations -/

/-- `H` is a *subgraph* of `G` when its vertex set and edge set are both
contained in those of `G`. Edge comparison uses the underlying
`Edge α β`-valued field, so parallel edges with different labels are
treated as distinct. -/
@[grind] def Graph.subgraphOf (H G : Graph α β) : Prop :=
  H.vertexSet ⊆ G.vertexSet ∧ H.edgeSet ⊆ G.edgeSet

/-- `H` is a *subgraph* of `G` when its vertex set and edge set are both
contained in those of `G`. -/
@[grind] def SimpleGraph.subgraphOf (H G : SimpleGraph α) : Prop :=
  H.vertexSet ⊆ G.vertexSet ∧ H.edgeSet ⊆ G.edgeSet

/-- `H` is a *subgraph* of `G` when its vertex set and edge set are both
contained in those of `G`. Edge comparison uses the underlying
`Arc α β`-valued field, so parallel edges with different labels are
treated as distinct. -/
@[grind] def DiGraph.subgraphOf (H G : DiGraph α β) : Prop :=
  H.vertexSet ⊆ G.vertexSet ∧ H.edgeSet ⊆ G.edgeSet

/-- `H` is a *subgraph* of `G` when its vertex set and edge set are both
contained in those of `G`. -/
@[grind] def SimpleDiGraph.subgraphOf (H G : SimpleDiGraph α) : Prop :=
  H.vertexSet ⊆ G.vertexSet ∧ H.edgeSet ⊆ G.edgeSet

/-! ## Induced subgraphs -/

/-- The subgraph of `G` induced by the vertex set `S`: its vertices are
`S ∩ V(G)` and its edges are the edges of `G` all of whose endpoints
lie in `S`. -/
def Graph.induce (G : Graph α β) (S : Set α) : Graph α β where
  vertexSet := S ∩ G.vertexSet
  edgeSet := {e ∈ G.edgeSet | ∀ v ∈ e.endpoints, v ∈ S}
  incidence' := by
    rintro e ⟨he, hin⟩ v hv
    exact ⟨hin v hv, G.incidence' e he v hv⟩

/-- The simple graph induced by `G` on the vertex set `S`: its vertices
are `S ∩ V(G)` and its edges are the edges of `G` both of whose
endpoints lie in `S`. Looplessness is inherited from `G`. -/
def SimpleGraph.induce (G : SimpleGraph α) (S : Set α) : SimpleGraph α where
  vertexSet := S ∩ G.vertexSet
  edgeSet := {e ∈ G.edgeSet | ∀ v ∈ e, v ∈ S}
  incidence' := by
    rintro e ⟨he, hin⟩ v hv
    exact ⟨hin v hv, G.incidence' e he v hv⟩
  loopless' := by
    rintro e ⟨he, _⟩
    exact G.loopless' e he

/-- The directed graph induced by `G` on the vertex set `S`: its vertices
are `S ∩ V(G)` and its edges are the directed edges of `G` whose source
and target both lie in `S`. -/
def DiGraph.induce (G : DiGraph α β) (S : Set α) : DiGraph α β where
  vertexSet := S ∩ G.vertexSet
  edgeSet := {e ∈ G.edgeSet | e.endpoints.1 ∈ S ∧ e.endpoints.2 ∈ S}
  incidence' := by
    rintro e ⟨he, h1, h2⟩
    obtain ⟨g1, g2⟩ := G.incidence' e he
    exact ⟨⟨h1, g1⟩, ⟨h2, g2⟩⟩

/-- The simple directed graph induced by `G` on the vertex set `S`: its
vertices are `S ∩ V(G)` and its edges are the directed edges of `G`
whose source and target both lie in `S`. Looplessness is inherited
from `G`. -/
def SimpleDiGraph.induce (G : SimpleDiGraph α) (S : Set α) : SimpleDiGraph α where
  vertexSet := S ∩ G.vertexSet
  edgeSet := {e ∈ G.edgeSet | e.1 ∈ S ∧ e.2 ∈ S}
  incidence' := by
    rintro e ⟨he, h1, h2⟩
    obtain ⟨g1, g2⟩ := G.incidence' e he
    exact ⟨⟨h1, g1⟩, ⟨h2, g2⟩⟩
  loopless' := by
    rintro e ⟨he, _, _⟩
    exact G.loopless' e he

section Notation

/-- `G[S]` is the subgraph of `G` induced by the vertex set `S`. -/
instance {α β : Type*} : GetElem (Graph α β) (Set α) (Graph α β) (fun _ _ => True) where
  getElem G S _ := G.induce S

/-- `G[S]` is the subgraph of `G` induced by the vertex set `S`. -/
instance {α : Type*} : GetElem (SimpleGraph α) (Set α) (SimpleGraph α) (fun _ _ => True) where
  getElem G S _ := G.induce S

/-- `G[S]` is the subgraph of `G` induced by the vertex set `S`. -/
instance {α β : Type*} : GetElem (DiGraph α β) (Set α) (DiGraph α β) (fun _ _ => True) where
  getElem G S _ := G.induce S

/-- `G[S]` is the subgraph of `G` induced by the vertex set `S`. -/
instance {α : Type*} :
    GetElem (SimpleDiGraph α) (Set α) (SimpleDiGraph α) (fun _ _ => True) where
  getElem G S _ := G.induce S

end Notation

end GraphLib
