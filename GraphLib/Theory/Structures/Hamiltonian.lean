/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.Walk
import GraphLib.Theory.Structures.SimpleWalk

/-!
# Hamiltonian walks

A *Hamiltonian* walk visits every vertex of a graph exactly once. A
Hamiltonian *path* is open (head ≠ tail in a simple graph); a Hamiltonian
*cycle* is closed and returns to its start vertex.

## Main definitions

* `Walk.IsHamiltonian G w` — the walk `w` visits every vertex of `G`
  exactly once.
* `Walk.IsHamiltonianCycle G w` — Hamiltonian and closed.
* `SimpleWalk.IsHamiltonian G w` — analogue for simple walks.
* `SimpleWalk.IsHamiltonianCycle G w` — Hamiltonian and closed.
-/

open GraphLib

variable {α ε : Type*}

namespace Walk

/-- A walk is *Hamiltonian* in `G` when every vertex of `G` is visited
exactly once. -/
def IsHamiltonian (G : Graph α ε) (w : Walk α ε) : Prop :=
  (∀ v : α, v ∈ G.vertexSet ↔ v ∈ w) ∧ w.toVertexList.Nodup

/-- A *Hamiltonian cycle* is a Hamiltonian walk whose endpoints coincide.
The closing return-edge means the interior — the walk with its last vertex
dropped — is the part that visits every vertex exactly once. -/
def IsHamiltonianCycle (G : Graph α ε) (w : Walk α ε) : Prop :=
  w.dropTail.IsHamiltonian G ∧ w.closed ∧ 3 ≤ w.length

end Walk

namespace SimpleWalk

/-- A simple walk is *Hamiltonian* in `G` when every vertex of `G` is
visited exactly once. -/
def IsHamiltonian (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  (∀ v : α, v ∈ G.vertexSet ↔ v ∈ w.val) ∧ w.val.nodup

/-- A *Hamiltonian cycle* is a closed simple walk whose interior visits
every vertex of `G` exactly once. -/
def IsHamiltonianCycle (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  (∀ v : α, v ∈ G.vertexSet ↔ v ∈ w.val) ∧
    w.val.dropTail.nodup ∧ w.val.closed ∧ 3 ≤ w.val.length

end SimpleWalk
