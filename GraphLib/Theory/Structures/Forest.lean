/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.SimpleWalk

/-!
# Forests

A *forest* is an acyclic simple graph. Equivalently, every two vertices are
joined by at most one path.

## Main definitions

* `SimpleGraph.IsForest G` — `G` contains no closed non-trivial simple walk
  whose interior is a path (i.e. no cycle).
-/

open GraphLib

variable {α : Type*}

namespace GraphLib.SimpleGraph

/-- The edges and vertices of `w` lie entirely in `G`. -/
def Contains (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  (∀ v ∈ w.val.toList, v ∈ G.vertexSet) ∧
  (∀ e ∈ w.val.edges, e ∈ G.edgeSet)

/-- `G` is a *forest* if it contains no cycle: no closed simple walk of
length ≥ 3 whose interior (everything but the last vertex) has distinct
vertices. -/
def IsForest (G : SimpleGraph α) : Prop :=
  ∀ w : SimpleWalk α, G.Contains w →
    ¬ (w.val.closed ∧ w.val.dropTail.nodup ∧ 3 ≤ w.val.length)

end GraphLib.SimpleGraph
