/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.SimpleWalk
import GraphLib.Theory.Structures.Forest

/-!
# Trees

A *tree* is a connected forest: an acyclic simple graph in which every pair
of vertices is joined by a (necessarily unique) walk.

## Main definitions

* `SimpleGraph.IsConnected G` — every two vertices of `G` are joined by a
  simple walk in `G`.
* `SimpleGraph.IsTree G` — `G` is a connected forest.
-/

open GraphLib

variable {α : Type*}

namespace GraphLib.SimpleGraph

/-- `G` is *connected* if every two vertices of `G` are linked by some
simple walk inside `G`. -/
def IsConnected (G : SimpleGraph α) : Prop :=
  ∀ u v, u ∈ G.vertexSet → v ∈ G.vertexSet →
    ∃ w : SimpleWalk α, G.Contains w ∧ w.val.head = u ∧ w.val.tail = v

/-- `G` is a *tree* if it is a connected forest. -/
def IsTree (G : SimpleGraph α) : Prop :=
  G.IsForest ∧ G.IsConnected

end GraphLib.SimpleGraph
