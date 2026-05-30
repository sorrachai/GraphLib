import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.SimpleGraphs.DirectedGraphs.SimpleDiGraphs
import GraphAlgorithms.SimpleGraphs.DirectedGraphs.Walk  -- already incl. GraphAlgorithms.SimpleGraphs.Walk


set_option tactic.hygienic false

open SimpleDiGraph
open Walk Path
open Finset

variable {α : Type*} [DecidableEq α] [LinearOrder α]

-- functional specification
abbrev ENat.min (a b : ℕ∞) : ℕ∞ :=
  if a ≤ b then a else b

def relaxNeighbors_spec
    (G : SimpleDiGraph α) (len : α → α → ℕ)
    (u : α) (du : ℕ∞)
    (pq : List (ℕ∞ × α)) : List (ℕ∞ × α) :=
  pq.map (fun (dv, v) =>
    if v ∈ N⁺(G,u)
    then (ENat.min dv (du + len u v), v)
    else (dv, v))

set_option linter.unusedVariables false

def dijkstraRec (G : SimpleDiGraph α) (len : α → α → ℕ) (src : α) (pq : List (ℕ∞ × α))
    (dist : α → ℕ∞) : α → ℕ∞ :=
    match h: pq.argmin (fun x : (ℕ∞ × α) ↦ x.1) with
    | none => dist
    | some (du,u) =>
      let dist' := fun v => if v = u then du else dist v
      let pq' := pq.erase (du,u)
      let pq'' := relaxNeighbors_spec G len u du pq'
      dijkstraRec G len src pq'' dist'
termination_by pq.length
decreasing_by
  simp only [relaxNeighbors_spec, mem_filter, ne_eq, Prod.exists, ↓existsAndEq, true_and,
    Prod.mk.eta, List.length_map]
  rw [List.length_erase_of_mem (List.argmin_mem h)]
  have: (du,u) ∈ pq := List.argmin_mem h
  grind

def dijkstraSpec (G : SimpleDiGraph α) (len : α → α → ℕ) (src : α) : α → ℕ∞ :=
  let pq := ((V(G).sort).map  (fun v => (if v = src then 0 else ⊤, v)))
  let dist := (fun _ => ⊤)
  dijkstraRec G len src pq dist

-- Analysis
theorem dijkstraSpec_correct (G : SimpleDiGraph α) (len : α → α → ℕ) (s : α) :
  let dist := dijkstraSpec G len s
  ∀ u, dist u = Path.weighted_distance G len s u := sorry
