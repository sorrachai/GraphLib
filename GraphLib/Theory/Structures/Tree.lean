/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan,
         Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Theory.Connectivity.Reachable
import GraphLib.Theory.Structures.Forest

/-!
# Trees

A *tree* is a connected forest: an acyclic simple graph in which every pair
of vertices is joined by a (necessarily unique) walk.

## Main definitions

* `SimpleGraph.IsTree G` — `G` is a connected forest.

## Implementation notes

Connectedness itself is not defined here. `SimpleGraph.IsConnected` lives in
`GraphLib.Theory.Connectivity.Reachable`, where it is built on
`SimpleGraph.Reachable` and comes with the full component API. This file previously
carried a second, standalone definition of `IsConnected` phrased over the now-retired
`SimpleGraph.Contains`; it has been removed in favour of the canonical one, so that
there is a single notion of connectedness in the library.
-/

open GraphLib

variable {α : Type*}

namespace GraphLib.SimpleGraph

/-- `G` is a *tree* if it is a connected forest. -/
def IsTree (G : SimpleGraph α) : Prop :=
  G.IsForest ∧ G.IsConnected

/-- A tree is a forest. -/
lemma IsTree.isForest {G : SimpleGraph α} (h : G.IsTree) : G.IsForest := h.1

/-- A tree is connected. -/
lemma IsTree.isConnected {G : SimpleGraph α} (h : G.IsTree) : G.IsConnected := h.2

/-- A tree has at least one vertex. -/
lemma IsTree.nonempty {G : SimpleGraph α} (h : G.IsTree) : V(G).Nonempty := h.2.1

end GraphLib.SimpleGraph
