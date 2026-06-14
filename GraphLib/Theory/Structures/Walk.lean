/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.Sym.Sym2
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.VertexSeq

/-!
# Vertex Sequence

This file develops a graph-agnostic theory of walks, paths and cycles. A walk
is modelled as a non-empty sequence of vertices in which consecutive vertices
differ. No underlying graph is referenced, so the same data structure can be
specialised later to walks in `SimpleGraph`, `DiGraph`, or other graph types
by adding an adjacency hypothesis on top of `Walk`.

## Main definitions

* `VertexSeq α`: non-empty sequence of vertices, defined inductively with a
  `singleton` base case and a right-extending `cons`.
* `IsWalk : VertexSeq α → Prop`: the predicate that consecutive vertices of
  the sequence differ (no immediate backtracking).
* `Walk α`: bundle of a `VertexSeq α` together with a proof of `IsWalk`.
* `VertexSeq.append`, `VertexSeq.reverse`, `VertexSeq.dropHead`,
  `VertexSeq.dropTail`: basic operations on sequences.
* `VertexSeq.takeUntil` / `VertexSeq.dropUntil`: split a sequence at the
  first occurrence of a given vertex.
* `VertexSeq.loopErase` / `Walk.toPath`: erase self-loops to obtain a path
  while preserving the endpoints.
* `Walk.IsPath`: a walk whose support has no repeated vertices.
* `Walk.IsCycle`: a walk of length at least 3 whose endpoints coincide and
  whose interior is a path.
* `Walk.rerootCycle`: rotate a cycle so that a chosen vertex on it becomes
  the new base point.

## Design choices

* **Graph-agnostic.** `IsWalk` only encodes the local non-stalling condition
  `w.tail ≠ u`. Adjacency in a specific graph is the responsibility of
  downstream files. This keeps the basic combinatorial API reusable for
  simple graphs, digraphs, multigraphs, and so on.
* **Non-empty by construction.** `VertexSeq` has a `singleton` base case
  rather than wrapping `List`, ruling out empty walks at the type level.
  Consequently `length` counts *edges* and `singleton` has length `0`.
* **Right-extending `cons`.** `cons w u` appends `u` at the end, matching the
  natural left-to-right reading of a walk `v₀, v₁, ..., vₙ`. Thus `head` of
  `cons w u` is `w.head` and `tail` is `u`.
* **Bundled `Walk`.** The structure carries data and validity together so
  that downstream lemmas need not thread `IsWalk` hypotheses by hand.
* **`grind`-driven proofs.** Most lemmas close by `grind`/`fun_induction`.
  Definitions and constructors carry `@[grind]` so the tactic can unfold and
  rewrite them automatically.
-/

set_option tactic.hygienic false

variable {α ε : Type*}

open VertexSeq

@[grind] inductive Walk (α ε : Type*)
  | singleton (v : α) : Walk α ε
  | cons (w : Walk α ε) (v : α) (e : ε) : Walk α ε

inductive NonStalling : VertexSeq α → Prop
  | singleton (v : α) : NonStalling (.singleton v)
  | cons {w : VertexSeq α} {v : α} (hw : NonStalling w) (h : w.tail ≠ v) :
      NonStalling (.cons w v)

def SimpleWalk (α : Type*) := { w : VertexSeq α // NonStalling w }

namespace Walk

open GraphLib.Graph
open GraphLib.DiGraph

@[simp] def head : Walk α ε → α
  | singleton v => v
  | cons w _ _  => w.head

@[simp] def tail : Walk α ε → α
  | singleton v => v
  | cons _ v _ => v

@[simp] def length : Walk α ε → ℕ
  | singleton _ => 0
  | cons w _ _ => 1 + w.length

@[simp] def toSimpleWalk : Walk α ε → SimpleWalk α
  | singleton v => SimpleWalk.singleton v
  | cons w v _ => w.toSimpleWalk.cons v

@[simp] def toVertexList : Walk α ε → List α
  | singleton v => [v]
  | cons w v _ => w.toVertexList.concat v

@[simp] def toEdgeList : Walk α ε → List ε
  | singleton _ => []
  | cons w _ e => w.toEdgeList.concat e

theorem vertices_singleton (v : α) :
    (singleton v : Walk α ε).toVertexList = [v] := rfl

theorem vertices_cons (v : α) (e : ε) (w : Walk α ε) :
    (cons w v e : Walk α ε).toVertexList = w.toVertexList.concat v := rfl

-- membership instances

instance : Membership α (Walk α ε) := ⟨fun w v => v ∈ w.toVertexList⟩

@[simp] theorem mem_def_vertices {v : α} (w : Walk α ε) : v ∈ w ↔ v ∈ w.toVertexList := Iff.rfl

instance : Membership ε (Walk α ε) := ⟨fun w e => e ∈ w.toEdgeList⟩

@[simp] theorem mem_def_edges {e : ε} (w : Walk α ε) : e ∈ w ↔ e ∈ w.toEdgeList := Iff.rfl

-- trivial things

lemma head_singleton (v : α) :
    (singleton v : Walk α ε).head = v := by
  simp

lemma tail_singleton (v : α) :
    (singleton v : Walk α ε).tail = v := by
  simp

lemma head_cons (w : Walk α ε) (v : α) (e : ε) :
    (cons w v e).head = w.head := by
  simp

lemma tail_cons (w : Walk α ε) (v : α) (e : ε) :
    (cons w v e).tail = v := by
  simp

/-- The `head` always appears in the underlying list of vertices. -/
@[grind ←] lemma head_mem_toList (w : Walk α ε) : some w.head = w.toVertexList.head? := by
  induction w
  · simp
  · simp
    rw [←w_ih]
    simp

/-- The `head` is a member of the underlying list of vertices. -/
@[simp, grind] lemma head_mem (w : Walk α ε) : w.head ∈ w.toVertexList := by
  induction w with
  | singleton _ => simp [head]
  | cons w _ ih => simp [head] ; tauto

/-- The `tail` is a member of the underlying list of vertices. -/
@[simp, grind] lemma tail_mem (w : Walk α ε) : w.tail ∈ w.toVertexList := by
  cases w with
  | singleton _ => simp [tail]
  | cons _ _ => simp [tail]

-- length of the edges list + 1 = length of the vertex list

theorem len_edge_list_succ_eq_len_vertex_list (w : Walk α ε) :
    w.toEdgeList.length + 1 = w.toVertexList.length := by
  induction w
  · simp
  · simp [w_ih]

-- length of a walk is the length of the edge list

@[simp] theorem len_walk_eq_len_edge_list (w : Walk α ε) :
    w.length = w.toEdgeList.length := by
  induction w
  · simp
  · simp [w_ih]
    grind

/- dropHead, dropTail -/

@[grind] def dropHead : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons (.singleton _) v _ => .singleton v
  | .cons w v e => .cons w.dropHead v e

@[grind] def dropTail : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons w _ _ => w

/- reverse, append -/

/- takeUntil, dropUntil, loopErase -/

/- map, foldl, foldr -/

/- zip -/

/- closed property -/

/- in graph -/

def toGraph (w : Walk α ε) : Graph α ε := by sorry

def toDiGraph (w : Walk α ε) : DiGraph α ε := by sorry



end Walk

namespace SimpleWalk

end SimpleWalk

namespace VertexSeq

/-! ## Basic accessors -/

@[grind] def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons w v    => w.toList.concat v

@[simp] theorem toList_singleton (v : α) : (singleton v).toList = [v] := rfl

@[simp] theorem toList_cons (w : VertexSeq α) (v : α) :
  (cons w v).toList = w.toList.concat v := rfl

theorem toList_ne_nil (w : VertexSeq α) : w.toList ≠ [] := by
  cases w <;> simp



@[grind] def length : VertexSeq
