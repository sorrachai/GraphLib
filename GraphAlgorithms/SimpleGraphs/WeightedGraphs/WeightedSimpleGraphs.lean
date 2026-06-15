import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Basic

-- Undirected Weighed Graphs
-- Authors: Christos Demetriou

set_option tactic.hygienic false
variable {α : Type*}
/-
TODO extend with : variable {β : Type*} [LinearOrder β] [Preorder β]
[AddCommMonoid β] [IsOrderedAddMonoid β]
-/

abbrev Edge := Sym2

structure WeightedSimpleGraph (α : Type*) where
  vertexSet : Finset α
  edgeSet   : Finset (Edge α)
  edgeWeight  : Edge α → ENNReal
  incidence : ∀ e ∈ edgeSet, ∀ v  ∈ e, v ∈ vertexSet
  loopless :  ∀ e ∈ edgeSet, ¬ e.IsDiag
  weightInclusion : ∀ e, e ∉ edgeSet ↔ (edgeWeight e) = ⊤ 

open Finset
open NNReal
open ENNReal




namespace WeightedSimpleGraph

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => edgeSet G

abbrev IncidentEdgeSet (G : WeightedSimpleGraph α) (s : α) [DecidableEq α] :
  Finset (Edge α) := {e ∈ E(G) | s ∈ e}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/
scoped notation "δ(" G "," v ")" => IncidentEdgeSet G v

abbrev Neighbors (G : WeightedSimpleGraph α) (s : α) [DecidableEq α] :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s ∈ e ∧ u ∈ e ∧ u ≠ s}

/-- `N(G,v)` denotes the `neighbors` of a graph `G`. -/
scoped notation "N(" G "," v ")" => Neighbors G v

/-- `deg(G)` denotes the `degree` of a graph `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)

abbrev EdgeWeight (G : WeightedSimpleGraph α) (e : Edge α) :=
  G.edgeWeight e

scoped notation "w(" G ", " e ")" => EdgeWeight G e

abbrev subgraphOf (H G : WeightedSimpleGraph α) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => subgraphOf

@[grind →]
lemma ne_of_mem_edgeSet (G : WeightedSimpleGraph α) (u v : α) (h : s(u, v) ∈ E(G)) : u ≠ v := by
  by_contra!
  subst this
  have:= G.loopless
  apply this s(u,u) h
  rfl

@[grind ←]
lemma edgeSet_sym (G : WeightedSimpleGraph α) (u v : α) (h : s(u, v) ∈ E(G)) :
  s(v, u) ∈ E(G) := by grind
end WeightedSimpleGraph
