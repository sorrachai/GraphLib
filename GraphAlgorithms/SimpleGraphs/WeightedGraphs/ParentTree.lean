import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Tree.Basic

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

structure ParentTree (α : Type*) where
  vertexSet : Finset α
  parent : α -> α
  level : α -> ℕ
  incidence : ∀ v ∈ vertexSet, parent v ∈ vertexSet
  ordering : ∀ v ∈ vertexSet, level v > 0 → level (parent v) <  level v
  root : ∀  v ∈ vertexSet, level v = 0 ↔ v = parent v

abbrev Edge := Sym2

open Finset

namespace ParentTree 

/-- `V(G)` denotes the `vertexSet` of a graph `G`. -/
scoped notation "Vₚ(" G ")" => vertexSet G

abbrev EdgeSet (G : ParentTree α) : Finset (Edge α) := 
   G.vertexSet |> .image (fun p => s(p, G.parent p)) 
   |> .filter (fun e => ¬ e.IsDiag)

/-- `E(G)` denotes the `edgeSet` of a graph `G`. -/
scoped notation "Eₚ(" G ")" => EdgeSet G


abbrev NeighbourSet (G : ParentTree α) (v : α) : Finset α := 
   (Vₚ(G).filter (fun p => G.parent p = v)  ∪ {G.parent v}) \ {v}


/-- `Nₚ(G,v)` denotes the neighbours of a vertex `v` in graph `G`. -/
scoped notation "Nₚ(" G "," v ")" => NeighbourSet G v

abbrev IncidentEdgeSet (G : ParentTree α) (s : α) [DecidableEq α] :
  Finset (Edge α) := Nₚ(G,s) |> .image (fun p => s(p, s))

/-- `δₚ(G,v)` denotes the `edge-incident-set` of a vertex `v` in graph `G`. -/
scoped notation "δₚ(" G "," v ")" => IncidentEdgeSet G v

/-- `degree(G,v)` denotes the degree of `v` in graph `G`. -/
scoped notation "degₚ(" G "," v ")" => #δₚ(G, v)


section ParentTreeLemmas

end ParentTreeLemmas

end ParentTree 



