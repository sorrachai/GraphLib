/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan,
         Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Theory.Structures.InSimpleGraph

/-!
# Forests

A *forest* is an acyclic simple graph. Equivalently, every two vertices are
joined by at most one path.

## Main definitions

* `SimpleGraph.IsForest G` — `G` contains no simple cycle.

## Implementation notes

`IsForest` is the textbook name for `SimpleGraph.IsAcyclic`, which is defined in
`GraphLib.Theory.Structures.InSimpleGraph` as "`G` realizes no `SimpleCycle`". The two
are definitionally equal (`isForest_iff_isAcyclic`), and the cycle API of the
`InSimpleGraph` development applies to forests unchanged.

This file previously carried its own predicate `SimpleGraph.Contains`, spelling out by
hand that a walk's vertices and edges lie in `G`. That has been retired in favour of
`SimpleGraph.IsSimpleWalkIn`, which says the same thing (see
`SimpleGraph.IsSimpleWalkIn.iff_edges`) and carries the whole closure API.
-/

open GraphLib

variable {α : Type*}

namespace GraphLib.SimpleGraph

/-- `G` is a *forest* if it contains no cycle: no simple cycle of `G` is realized in
`G`. -/
def IsForest (G : SimpleGraph α) : Prop := G.IsAcyclic

/-- Being a forest is being acyclic. -/
@[simp, grind =] lemma isForest_iff_isAcyclic (G : SimpleGraph α) :
    G.IsForest ↔ G.IsAcyclic := Iff.rfl

/-- A forest realizes no simple cycle. -/
lemma IsForest.not_isSimpleCycleIn {G : SimpleGraph α} (h : G.IsForest)
    (c : SimpleCycle α) : ¬ G.IsSimpleCycleIn c := fun hc => h ⟨c, hc⟩

/-- A subgraph of a forest is a forest. -/
lemma IsForest.subgraph {G H : SimpleGraph α} (h : G.IsForest)
    (hsub : SimpleGraph.subgraphOf H G) : H.IsForest :=
  isAcyclic_of_subgraph G H hsub h

end GraphLib.SimpleGraph
