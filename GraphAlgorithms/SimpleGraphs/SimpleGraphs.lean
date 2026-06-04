import Mathlib.Data.Sym.Sym2

-- Undirected Graphs
-- Authors: Sorrachai Yingchareonthawornchai

set_option tactic.hygienic false
variable {α : Type*}

abbrev Edge := Sym2

structure SimpleGraph (α : Type*) where
  vertexSet : Finset α
  edgeSet   : Finset (Edge α)
  incidence : ∀ e ∈ edgeSet, ∀ v ∈ e, v ∈ vertexSet
  loopless :  ∀ e ∈ edgeSet, ¬ e.IsDiag



open Finset




namespace SimpleGraph

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "V(" G ")" => vertexSet G

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "E(" G ")" => edgeSet G

abbrev IncidentEdgeSet (G : SimpleGraph α) (s : α) [DecidableEq α] :
  Finset (Edge α) := {e ∈ E(G) | s ∈ e}

/-- `δ(G,v)` denotes the `edge-incident-set` of a vertex `v` in `G`. -/
scoped notation "δ(" G "," v ")" => IncidentEdgeSet G v

abbrev Neighbors (G : SimpleGraph α) (s : α) [DecidableEq α] :
  Finset α := {u ∈ V(G) | ∃ e ∈ E(G), s ∈ e ∧ u ∈ e ∧ u ≠ s}

/-- `N(G,v)` denotes the `neighbors` of a graph `G`. -/
scoped notation "N(" G "," v ")" => Neighbors G v

/-- `deg(G)` denotes the `degree` of a graph `G`. -/
scoped notation "deg(" G "," v ")" => #δ(G,v)

abbrev subgraphOf (H G : SimpleGraph α) : Prop :=
  V(H) ⊆ V(G) ∧ E(H) ⊆ E(G)

scoped infix:50 " ⊆ᴳ " => subgraphOf

@[grind →]
lemma ne_of_mem_edgeSet (G : SimpleGraph α) (u v : α) (h : s(u, v) ∈ E(G)) : u ≠ v := by
  by_contra!
  subst this
  have:= G.loopless
  apply this s(u,u) h
  rfl

@[grind ←]
lemma edgeSet_sym (G : SimpleGraph α) (u v : α) (h : s(u, v) ∈ E(G)) :
  s(v, u) ∈ E(G) := by grind

end SimpleGraph
