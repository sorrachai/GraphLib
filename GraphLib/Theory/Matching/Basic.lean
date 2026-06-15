/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import GraphLib.Graph.Basic
import GraphLib.Graph.Subgraph
import GraphLib.Theory.Walks.Basic

/-!
# Matchings, augmenting paths, Berge's theorem, and friends

## Scope and status


## Main definitions

- Matching
- Vertex Covering, Edge Covering (maybe separate file)
- Matching covers vertex?
- Maximal, Maximum, Perfect Matching
- Path alternating
- Path augmenting
- Augment matching
- matching for bipartite graph

## Main theorems

- `augmenting paths are mathings`
- `Berge`
- `König`
- `Hall`
- `Tutte`
- `Tutte Berge`
- `Petersen`
- `Gallai Edmonds`
- `Vizing`
-/

namespace GraphLib

open scoped GraphLib

variable {α β : Type*}

/-! ## Matchings -/

structure Matching (G : Graph α β) where
  edges : Set (Edge α β)
  disjoint : ∀ e ∈ E(G), ∀ f ∈ E(G), e ≠ f → Disjoint e.endpoints.toFinset f.endpoints.toFinset

def Matching.size (G : Graph α β) (M : Matching G) := M.edges.card

def Matching.IsMaximal

def Matching.IsMaximum

def Matching.IsPerfect

def Matching.covered

def Path.augmenting

def Path.alternating

def Matching.augment

def Matching.union

def Matching.xor
