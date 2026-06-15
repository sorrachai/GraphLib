/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.Walk
import GraphLib.Theory.Structures.SimpleWalk

/-!
# Eulerian walks

An *Eulerian* walk traverses every edge of a graph exactly once. A walk is
*Eulerian* in `G` when its edge multiset equals `G.edgeSet` and no edge is
repeated. An Eulerian *circuit* is closed (head = tail); an Eulerian *trail*
is open.

## Main definitions

* `Walk.IsEulerian G w` — the walk `w` uses every edge of `G` exactly once.
* `Walk.IsEulerianCircuit G w` — Eulerian and closed.
* `SimpleWalk.IsEulerian G w` — analogue for simple walks.
* `SimpleWalk.IsEulerianCircuit G w` — Eulerian and closed.
-/

open GraphLib

variable {α ε : Type*}

namespace Walk

/-- A walk is *Eulerian* in `G` when every edge of `G` is traversed exactly
once and no extra edges are used. -/
def IsEulerian (G : Graph α ε) (w : Walk α ε) : Prop :=
  (∀ e : Edge α ε, e ∈ G.edgeSet ↔ e ∈ w.edges) ∧ w.edges.Nodup

/-- An *Eulerian circuit* is an Eulerian walk that returns to its start. -/
def IsEulerianCircuit (G : Graph α ε) (w : Walk α ε) : Prop :=
  w.IsEulerian G ∧ w.closed

end Walk

namespace SimpleWalk

/-- A simple walk is *Eulerian* in `G` when every edge of `G` is traversed
exactly once and no extra edges are used. -/
def IsEulerian (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  (∀ e : Sym2 α, e ∈ G.edgeSet ↔ e ∈ w.val.edges) ∧ w.val.edges.Nodup

/-- A simple-graph *Eulerian circuit* is an Eulerian simple walk that closes. -/
def IsEulerianCircuit (G : SimpleGraph α) (w : SimpleWalk α) : Prop :=
  w.IsEulerian G ∧ w.val.closed

end SimpleWalk
