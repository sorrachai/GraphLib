import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic


-- Simple Directed Graphs
-- Authors: Sorrachai Yingchareonthawornchai

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

abbrev Edge (V : Type*) := V × V

structure SimpleDiGraph (α : Type*) where
  vertexSet : Finset α
  edgeSet   : Finset (Edge α)
  incidence : ∀ e ∈ edgeSet, e.1 ∈ vertexSet ∧ e.2 ∈ vertexSet
  loopless :  ∀ e ∈ edgeSet, e.1 ≠ e.2

open Finset

namespace SimpleDiGraph

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => SimpleDiGraph.vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => SimpleDiGraph.edgeSet G

abbrev OutIncidentEdgeSet (G : SimpleDiGraph α) (s : α) :
  Finset (Edge α) := {e ∈ E(G) | s = e.1}

/-- `δ⁺(G,v)` denotes the `out-edge-incident-set` of a vertex `v` in `G`. -/
scoped notation "δ⁺(" G "," v ")" => SimpleDiGraph.OutIncidentEdgeSet G v

abbrev OutNeighbors (G : SimpleDiGraph α) (s : α) :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s = e.1 ∧ u = e.2 ∧ u ≠ s}

/-- `N⁺(G,v)` denotes the `out-neighbors` of a graph `G`. -/
scoped notation "N⁺(" G "," v ")" => SimpleDiGraph.OutNeighbors G v

/-- `deg⁺(G)` denotes the `out-degree` of a graph `G`. -/
scoped notation "deg⁺(" G "," v ")" => #δ⁺(G,v)

abbrev subgraphOf (H G : SimpleDiGraph α) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => SimpleDiGraph.subgraphOf

end SimpleDiGraph
