/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic

/-!
# Adjacency

This file equips each of the four graph structures from
`GraphLib.Graph.Basic` (`Graph`, `SimpleGraph`, `DiGraph`, `SimpleDiGraph`)
with an adjacency relation `Adj` on vertices, together with its basic API.

`Adj` is the primitive vertex relation that downstream files build on: a
walk lives in a graph when consecutive vertices are adjacent, a proper
colouring assigns distinct colours to adjacent vertices, and so on. We
therefore place it directly above `GraphLib.Graph.Basic` and below
`GraphLib.Graph.Degree`, where the neighbour and degree functions are
defined in terms of the same edge-membership conditions.

## Main definitions

* `Graph.Adj` — `u` and `v` are adjacent when a single edge has them as
  endpoints; loops may make a vertex adjacent to itself.
* `SimpleGraph.Adj` — `u` and `v` are adjacent when the unordered pair
  `s(u, v)` is an edge, necessarily with distinct endpoints.
* `DiGraph.Adj`, `SimpleDiGraph.Adj` — there is an arc *from* `u` *to* `v`.
  Directed adjacency is not symmetric.

## Main API

* `Adj.symm`, `adj_comm` — symmetry of adjacency, for the undirected
  types `Graph` and `SimpleGraph` only.
* `Adj.ne` — adjacent vertices are distinct. Available only for the simple
  types, where it follows from looplessness; for the multigraph types a
  loop genuinely makes a vertex adjacent to itself, so no such lemma holds.
* `Adj.left_mem`, `Adj.right_mem` — the endpoints of an adjacency are
  vertices of the graph.

## Design choices

* **One definition per graph type.** As elsewhere in `GraphLib.Graph`, we
  spell out `Adj` separately for each of the four structures rather than
  factoring through a typeclass, keeping each definition concrete.
* **Adjacency is pure edge-existence; it does not exclude loops.** `Adj` is
  simply "there is an edge joining the two vertices". For the simple types
  irreflexivity is automatic from looplessness, but for the multigraph
  types (`Graph`, `DiGraph`) a loop at `v` makes `Adj v v` hold. Excluding
  the vertex itself is the job of the *open* neighbourhood, not of the
  adjacency relation, so the `\ {v}` lives in `GraphLib.Graph.Degree`.
* **Directed adjacency is asymmetric.** `DiGraph.Adj G u v` and
  `SimpleDiGraph.Adj G u v` mean there is an arc with source `u` and
  target `v`; no `symm` lemma is provided for them.
-/

namespace GraphLib
variable {α β : Type*}

open scoped GraphLib

/-! ## Adjacency relations -/

/-- Two vertices are *adjacent* in the multigraph `G` when some edge has
them as its endpoints. A loop at `v` makes `v` adjacent to itself. -/
@[grind] def Graph.Adj (G : Graph α β) (u v : α) : Prop :=
  ∃ e ∈ E(G), u ∈ e ∧ v ∈ e

/-- Two vertices are *adjacent* in the simple graph `G` when `s(u, v)` is an
edge. -/
@[grind] def SimpleGraph.Adj (G : SimpleGraph α) (u v : α) : Prop :=
  s(u, v) ∈ E(G)

/-- There is an *arc* from `u` to `v` in the directed multigraph `G` when
some edge points from `u` to `v`. A loop at `v` is a self-arc. -/
@[grind] def DiGraph.Adj (G : DiGraph α β) (u v : α) : Prop :=
  (u, v) ∈ E(G)

/-- There is an *arc* from `u` to `v` in the simple directed graph `G` when
`(u, v)` is an edge. -/
@[grind] def SimpleDiGraph.Adj (G : SimpleDiGraph α) (u v : α) : Prop :=
  (u, v) ∈ E(G)

/-! ## Symmetry (undirected types) -/

/-- Adjacency in a multigraph is symmetric. -/
@[symm, grind →] lemma Graph.Adj.symm {G : Graph α β} {u v : α} (h : G.Adj u v) :
    G.Adj v u := by
  obtain ⟨e, he, hu, hv⟩ := h
  exact ⟨e, he, hv, hu⟩

/-- Adjacency in a multigraph is symmetric. -/
lemma Graph.adj_comm (G : Graph α β) (u v : α) : G.Adj u v ↔ G.Adj v u :=
  ⟨Graph.Adj.symm, Graph.Adj.symm⟩

/-- Adjacency in a simple graph is symmetric. -/
@[symm, grind →] lemma SimpleGraph.Adj.symm {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    G.Adj v u := by
  change s(v, u) ∈ E(G)
  rw [show s(v, u) = s(u, v) from Sym2.eq_swap]
  exact h

/-- Adjacency in a simple graph is symmetric. -/
lemma SimpleGraph.adj_comm (G : SimpleGraph α) (u v : α) : G.Adj u v ↔ G.Adj v u :=
  ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩

/-! ## Adjacent vertices are distinct

These hold only for the simple types, where looplessness rules out loops.
For the multigraph types a loop makes a vertex adjacent to itself, so the
analogous statements are false. -/

/-- Adjacent vertices in a simple graph are distinct, by looplessness. -/
@[grind →] lemma SimpleGraph.Adj.ne {G : SimpleGraph α} {u v : α} (h : G.Adj u v) : u ≠ v := by
  have hnd := G.loopless h
  rwa [Sym2.mk_isDiag_iff] at hnd

/-- The endpoints of an arc in a simple directed graph are distinct, by
looplessness. -/
@[grind →] lemma SimpleDiGraph.Adj.ne {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) : u ≠ v :=
  G.loopless h

/-! ## Endpoints are vertices -/

/-- The left endpoint of an adjacency is a vertex of the multigraph. -/
@[grind →] lemma Graph.Adj.left_mem {G : Graph α β} {u v : α} (h : G.Adj u v) : u ∈ V(G) := by
  obtain ⟨e, he, hu, _⟩ := h
  exact G.incidence he hu

/-- The right endpoint of an adjacency is a vertex of the multigraph. -/
@[grind →] lemma Graph.Adj.right_mem {G : Graph α β} {u v : α} (h : G.Adj u v) : v ∈ V(G) := by
  obtain ⟨e, he, _, hv⟩ := h
  exact G.incidence he hv

/-- The left endpoint of an adjacency is a vertex of the simple graph. -/
@[grind →] lemma SimpleGraph.Adj.left_mem {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    u ∈ V(G) := G.incidence h (by simp)

/-- The right endpoint of an adjacency is a vertex of the simple graph. -/
@[grind →] lemma SimpleGraph.Adj.right_mem {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    v ∈ V(G) := G.incidence h (by simp)

/-- The source of an arc is a vertex of the directed multigraph. -/
@[grind →] lemma DiGraph.Adj.left_mem {G : DiGraph α β} {u v : α} (h : G.Adj u v) : u ∈ V(G) :=
  (G.incidence h).1

/-- The target of an arc is a vertex of the directed multigraph. -/
@[grind →] lemma DiGraph.Adj.right_mem {G : DiGraph α β} {u v : α} (h : G.Adj u v) : v ∈ V(G) :=
  (G.incidence h).2

/-- The source of an arc is a vertex of the simple directed graph. -/
@[grind →] lemma SimpleDiGraph.Adj.left_mem {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) :
    u ∈ V(G) := (G.incidence h).1

/-- The target of an arc is a vertex of the simple directed graph. -/
@[grind →] lemma SimpleDiGraph.Adj.right_mem {G : SimpleDiGraph α} {u v : α} (h : G.Adj u v) :
    v ∈ V(G) := (G.incidence h).2

end GraphLib
