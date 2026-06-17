/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import GraphLib.Graph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice

/-!
# Neighbourhoods and degrees

This file equips each of the four graph structures from
`GraphLib.Graph.Basic` (`Graph`, `SimpleGraph`, `DiGraph`,
`SimpleDiGraph`) with neighbour sets, incidence sets, a degree function,
and the minimum and maximum degree.

## Main definitions

* `Graph.neighborSet`, `SimpleGraph.neighborSet` — the set of vertices
  adjacent to `v`.
* `DiGraph.outNeighborSet`, `DiGraph.inNeighborSet`,
  `SimpleDiGraph.outNeighborSet`, `SimpleDiGraph.inNeighborSet` — out-
  and in-neighbour sets.
* `Graph.incidenceSet`, `SimpleGraph.incidenceSet`,
  `DiGraph.outIncidenceSet`, `DiGraph.inIncidenceSet`,
  `SimpleDiGraph.outIncidenceSet`, `SimpleDiGraph.inIncidenceSet` —
  edges incident to (resp. leaving / entering) a vertex.
* `Graph.degree`, `SimpleGraph.degree`, `DiGraph.outDegree`,
  `DiGraph.inDegree`, `SimpleDiGraph.outDegree`,
  `SimpleDiGraph.inDegree` — the size of the relevant set, taken as a
  natural number via `Set.ncard`.
* `Graph.maxDegree`, `Graph.minDegree`, and analogues — the supremum
  / infimum of the degrees over `V(G)`, valued in `ℕ∞`.

## Design choices

* **Degree counts incident edges, not neighbours.** For the labelled
  multigraph types (`Graph`, `DiGraph`), `degree` is the cardinality
  of the incidence set, so parallel edges contribute their multiplicity.
  For the simple types, neighbour count and incidence count agree, and
  we define `degree` directly from `neighborSet` for brevity.
* **Loops are not neighbours.** For `Graph`, `neighborSet G v` excludes
  `v` itself. For simple graphs this is automatic by looplessness.
* **`Set.ncard` for total counting.** Degrees land in `ℕ`, returning
  `0` when the relevant set is infinite. Downstream finiteness
  hypotheses are needed to read this as a true cardinality.
* **`ℕ∞`-valued extremal degrees.** `minDegree` and `maxDegree` return
  values in `ℕ∞`, so the empty graph gives `maxDegree = 0` and
  `minDegree = ⊤` without per-definition finiteness hypotheses.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Neighbour sets -/

/-- The neighbours of `v` in the multigraph `G`: vertices `u ≠ v` that
share an edge with `v`. A loop at `v` does not make `v` its own
neighbour. -/
def Graph.neighborSet (G : Graph α β) (v : α) : Set α :=
  {u | u ≠ v ∧ ∃ e ∈ G.edgeSet, u ∈ e.endpoints ∧ v ∈ e.endpoints}

/-- The neighbours of `v` in the simple graph `G`. -/
def SimpleGraph.neighborSet (G : SimpleGraph α) (v : α) : Set α :=
  {u | s(u, v) ∈ G.edgeSet}

/-- The out-neighbours of `v` in the directed multigraph `G`: vertices
`u ≠ v` such that some edge of `G` points from `v` to `u`. -/
def DiGraph.outNeighborSet (G : DiGraph α β) (v : α) : Set α :=
  {u | u ≠ v ∧ ∃ e ∈ G.edgeSet, e.endpoints = (v, u)}

/-- The in-neighbours of `v` in the directed multigraph `G`. -/
def DiGraph.inNeighborSet (G : DiGraph α β) (v : α) : Set α :=
  {u | u ≠ v ∧ ∃ e ∈ G.edgeSet, e.endpoints = (u, v)}

/-- The out-neighbours of `v` in the simple directed graph `G`. -/
def SimpleDiGraph.outNeighborSet (G : SimpleDiGraph α) (v : α) : Set α :=
  {u | (v, u) ∈ G.edgeSet}

/-- The in-neighbours of `v` in the simple directed graph `G`. -/
def SimpleDiGraph.inNeighborSet (G : SimpleDiGraph α) (v : α) : Set α :=
  {u | (u, v) ∈ G.edgeSet}

/-! ## Incidence sets -/

/-- The set of edges of `G` incident to `v`. -/
def Graph.incidenceSet (G : Graph α β) (v : α) : Set (Edge α β) :=
  {e ∈ G.edgeSet | v ∈ e.endpoints}

/-- The set of edges of `G` incident to `v`. -/
def SimpleGraph.incidenceSet (G : SimpleGraph α) (v : α) : Set (Sym2 α) :=
  {e ∈ G.edgeSet | v ∈ e}

/-- The set of directed edges of `G` with source `v`. -/
def DiGraph.outIncidenceSet (G : DiGraph α β) (v : α) : Set (Arc α β) :=
  {e ∈ G.edgeSet | e.endpoints.1 = v}

/-- The set of directed edges of `G` with target `v`. -/
def DiGraph.inIncidenceSet (G : DiGraph α β) (v : α) : Set (Arc α β) :=
  {e ∈ G.edgeSet | e.endpoints.2 = v}

/-- The set of directed edges of `G` with source `v`. -/
def SimpleDiGraph.outIncidenceSet (G : SimpleDiGraph α) (v : α) : Set (α × α) :=
  {e ∈ G.edgeSet | e.1 = v}

/-- The set of directed edges of `G` with target `v`. -/
def SimpleDiGraph.inIncidenceSet (G : SimpleDiGraph α) (v : α) : Set (α × α) :=
  {e ∈ G.edgeSet | e.2 = v}

/-! ## Degrees -/

noncomputable section Degrees

/-- The degree of `v` in the multigraph `G`, counted as the number of
incident edges (parallel edges contribute their multiplicity). Returns
`0` if `v` has infinitely many incident edges. -/
def Graph.degree (G : Graph α β) (v : α) : ℕ := (G.incidenceSet v).ncard

/-- The degree of `v` in the simple graph `G`. Returns `0` if `v` has
infinitely many neighbours. -/
def SimpleGraph.degree (G : SimpleGraph α) (v : α) : ℕ := (G.neighborSet v).ncard

/-- The out-degree of `v` in the directed multigraph `G`. -/
def DiGraph.outDegree (G : DiGraph α β) (v : α) : ℕ := (G.outIncidenceSet v).ncard

/-- The in-degree of `v` in the directed multigraph `G`. -/
def DiGraph.inDegree (G : DiGraph α β) (v : α) : ℕ := (G.inIncidenceSet v).ncard

/-- The out-degree of `v` in the simple directed graph `G`. -/
def SimpleDiGraph.outDegree (G : SimpleDiGraph α) (v : α) : ℕ :=
  (G.outNeighborSet v).ncard

/-- The in-degree of `v` in the simple directed graph `G`. -/
def SimpleDiGraph.inDegree (G : SimpleDiGraph α) (v : α) : ℕ :=
  (G.inNeighborSet v).ncard

end Degrees

/-! ## Maximum and minimum degree -/

/-- The maximum degree `Δ(G)` of the multigraph `G`, valued in `ℕ∞`. For
the empty graph this is `0`. -/
noncomputable def Graph.finMaxDegree (G : Graph α β) [Finite G.vertexSet] : ℕ∞ :=
  ⨆ v ∈ V(G), (G.degree v : ℕ∞)

/-- The minimum degree `δ(G)` of the multigraph `G`, valued in `ℕ∞`. For
the empty graph this is `⊤`. -/
noncomputable def Graph.minDegree (G : Graph α β) : ℕ∞ :=
  ⨅ v ∈ V(G), (G.degree v : ℕ∞)

/-- The maximum degree `Δ(G)` of the simple graph `G`. -/
noncomputable def SimpleGraph.maxDegree (G : SimpleGraph α) : ℕ∞ :=
  ⨆ v ∈ V(G), (G.degree v : ℕ∞)

/-- The minimum degree `δ(G)` of the simple graph `G`. -/
noncomputable def SimpleGraph.minDegree (G : SimpleGraph α) : ℕ∞ :=
  ⨅ v ∈ V(G), (G.degree v : ℕ∞)

/-- The maximum out-degree of the directed multigraph `G`. -/
noncomputable def DiGraph.maxOutDegree (G : DiGraph α β) : ℕ∞ :=
  ⨆ v ∈ V(G), (G.outDegree v : ℕ∞)

/-- The minimum out-degree of the directed multigraph `G`. -/
noncomputable def DiGraph.minOutDegree (G : DiGraph α β) : ℕ∞ :=
  ⨅ v ∈ V(G), (G.outDegree v : ℕ∞)

/-- The maximum in-degree of the directed multigraph `G`. -/
noncomputable def DiGraph.maxInDegree (G : DiGraph α β) : ℕ∞ :=
  ⨆ v ∈ V(G), (G.inDegree v : ℕ∞)

/-- The minimum in-degree of the directed multigraph `G`. -/
noncomputable def DiGraph.minInDegree (G : DiGraph α β) : ℕ∞ :=
  ⨅ v ∈ V(G), (G.inDegree v : ℕ∞)

/-- The maximum out-degree of the simple directed graph `G`. -/
noncomputable def SimpleDiGraph.maxOutDegree (G : SimpleDiGraph α) : ℕ∞ :=
  ⨆ v ∈ V(G), (G.outDegree v : ℕ∞)

/-- The minimum out-degree of the simple directed graph `G`. -/
noncomputable def SimpleDiGraph.minOutDegree (G : SimpleDiGraph α) : ℕ∞ :=
  ⨅ v ∈ V(G), (G.outDegree v : ℕ∞)

/-- The maximum in-degree of the simple directed graph `G`. -/
noncomputable def SimpleDiGraph.maxInDegree (G : SimpleDiGraph α) : ℕ∞ :=
  ⨆ v ∈ V(G), (G.inDegree v : ℕ∞)

/-- The minimum in-degree of the simple directed graph `G`. -/
noncomputable def SimpleDiGraph.minInDegree (G : SimpleDiGraph α) : ℕ∞ :=
  ⨅ v ∈ V(G), (G.inDegree v : ℕ∞)

end GraphLib
