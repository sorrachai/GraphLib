/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.Sym.Sym2
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.VertexSeq

/-!
# Walks

A `Walk α ε` is a non-empty inductive sequence of vertices in `α` with edges
in `ε` between consecutive vertices. Mirror of `VertexSeq` but carrying edges
as well: `cons w v e` extends `w` on the right by appending vertex `v` and the
edge `e` joining `w.tail` to `v`.

This file mirrors the API of `VertexSeq` lemma-for-lemma, with the additional
edge list `toEdgeList` and edge-aware membership.
-/

variable {α ε : Type*}

/-- A non-empty inductive sequence of vertices interleaved with edges.
`cons w v e` extends `w` on the right by the vertex `v` and the edge `e`
joining `w.tail` to `v`. -/
@[grind] inductive Walk (α ε : Type*)
  | singleton (v : α) : Walk α ε
  | cons (w : Walk α ε) (v : α) (e : ε) : Walk α ε

namespace Walk

/-! ## Basic accessors -/

/-- The number of *edges* in the walk: `0` for a `singleton`. -/
@[grind] def length : Walk α ε → ℕ
  | .singleton _ => 0
  | .cons w _ _ => 1 + w.length

/-- The first vertex of the walk. -/
@[grind] def head : Walk α ε → α
  | .singleton v => v
  | .cons w _ _ => w.head

/-- The last vertex of the walk. -/
@[grind] def tail : Walk α ε → α
  | .singleton v => v
  | .cons _ v _ => v

/-- The list of vertices visited by the walk, head to tail. -/
@[grind] def toVertexList : Walk α ε → List α
  | .singleton v => [v]
  | .cons w v _ => w.toVertexList.concat v

/-- The list of edges traversed by the walk, in order. -/
@[grind] def toEdgeList : Walk α ε → List ε
  | .singleton _ => []
  | .cons w _ e => w.toEdgeList.concat e

@[simp, grind =] lemma head_singleton (u : α) :
    (Walk.singleton u : Walk α ε).head = u := rfl

@[simp, grind =] lemma head_cons (w : Walk α ε) (u : α) (e : ε) :
    (w.cons u e).head = w.head := rfl

@[simp, grind =] lemma tail_singleton (u : α) :
    (Walk.singleton u : Walk α ε).tail = u := rfl

@[simp, grind =] lemma tail_cons (w : Walk α ε) (u : α) (e : ε) :
    (w.cons u e).tail = u := rfl

/-- The `head` belongs to the underlying vertex list. -/
@[simp, grind] lemma head_mem (w : Walk α ε) : w.head ∈ w.toVertexList := by
  induction w with
  | singleton _ => simp [head, toVertexList]
  | cons w _ _ ih => simp [head, toVertexList]; exact Or.inl ih

/-- The `tail` belongs to the underlying vertex list. -/
@[simp, grind] lemma tail_mem (w : Walk α ε) : w.tail ∈ w.toVertexList := by
  cases w with
  | singleton _ => simp [tail, toVertexList]
  | cons _ _ _ => simp [tail, toVertexList]

/-- The vertex list has `length + 1` entries. -/
lemma length_toVertexList (w : Walk α ε) :
    w.toVertexList.length = w.length + 1 := by
  induction w <;> grind

/-- The edge list has `length` entries (one fewer than the vertex list). -/
lemma length_toEdgeList (w : Walk α ε) :
    w.toEdgeList.length = w.length := by
  induction w <;> grind

/-- The vertex list is exactly one longer than the edge list. -/
lemma length_toVertexList_eq_length_toEdgeList_succ (w : Walk α ε) :
    w.toVertexList.length = w.toEdgeList.length + 1 := by
  induction w <;> grind

/-! ## Membership -/

/-- Vertex membership is the default `∈` on `Walk α ε`. Edge membership uses
the separate notation `∈ₑ` (defined below) because Lean's `Membership` class
has `outParam` on the element type and disallows two instances. -/
instance : Membership α (Walk α ε) := ⟨fun w v ↦ v ∈ w.toVertexList⟩

@[simp, grind] theorem mem_def {v : α} (w : Walk α ε) :
    v ∈ w ↔ v ∈ w.toVertexList := Iff.rfl

/-- Edge membership predicate. -/
def hasEdge (w : Walk α ε) (e : ε) : Prop := e ∈ w.toEdgeList

scoped infix:50 " ∈ₑ " => fun e w => Walk.hasEdge w e

@[simp, grind] theorem mem_edge_def (e : ε) (w : Walk α ε) :
    e ∈ₑ w ↔ e ∈ w.toEdgeList := Iff.rfl

@[simp] lemma mem_cons_vertex (v u : α) (e : ε) (w : Walk α ε) :
    v ∈ Walk.cons w u e ↔ v ∈ w ∨ v = u := by
  grind

@[simp] lemma mem_cons_edge (f e : ε) (u : α) (w : Walk α ε) :
    f ∈ₑ Walk.cons w u e ↔ f ∈ₑ w ∨ f = e := by
  grind

instance [DecidableEq α] (v : α) (w : Walk α ε) : Decidable (v ∈ w) :=
  inferInstanceAs (Decidable (v ∈ w.toVertexList))

instance [DecidableEq ε] (e : ε) (w : Walk α ε) : Decidable (e ∈ₑ w) :=
  inferInstanceAs (Decidable (e ∈ w.toEdgeList))

instance : HasSubset (Walk α ε) :=
  ⟨fun w1 w2 ↦ (∀ v : α, v ∈ w1 → v ∈ w2) ∧ (∀ e : ε, e ∈ₑ w1 → e ∈ₑ w2)⟩

@[simp, grind] theorem subset_def {w1 w2 : Walk α ε} :
    w1 ⊆ w2 ↔ (∀ v : α, v ∈ w1 → v ∈ w2) ∧ (∀ e : ε, e ∈ₑ w1 → e ∈ₑ w2) :=
  Iff.rfl

/-! ## dropHead, dropTail -/

/-- Drop the first vertex (and its outgoing edge). -/
@[grind] def dropHead : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons (.singleton _) v e => .singleton v
  | .cons w v e => .cons w.dropHead v e

/-- Drop the last vertex (and its incoming edge). -/
@[grind] def dropTail : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons w _ _ => w

/-! ## reverse -/

/-- Reverse a walk. Edges are kept in the original direction (the user must
re-interpret them in any directed context). -/
@[grind] def reverse : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons w v e => reverseAux (.singleton v) w e
where
  reverseAux : Walk α ε → Walk α ε → ε → Walk α ε
    | acc, .singleton u, e => .cons acc u e
    | acc, .cons w u e', e => reverseAux (.cons acc u e) w e'

/-! ## prefixUntil, suffixFrom -/

/-- The prefix of `w` ending at the first occurrence of vertex `v`, inclusive. -/
@[grind] def prefixUntil [DecidableEq α] (w : Walk α ε) (v : α) (h : v ∈ w) :
    Walk α ε :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x e =>
    if h2 : v ∈ w2 then prefixUntil w2 v h2
    else .cons w2 x e

/-- The suffix of `w` starting at the first occurrence of vertex `v`, inclusive. -/
@[grind] def suffixFrom [DecidableEq α] (w : Walk α ε) (v : α) (h : v ∈ w) :
    Walk α ε :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x e =>
    if h2 : v ∈ w2 then .cons (suffixFrom w2 v h2) x e
    else .singleton x

@[simp] lemma length_prefixUntil_le [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).length ≤ w.length := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma length_suffixFrom_le [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).length ≤ w.length := by
  fun_induction suffixFrom w v h <;> grind

@[simp] lemma head_prefixUntil [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).head = w.head := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma tail_prefixUntil [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).tail = v := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma head_suffixFrom [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).head = v := by
  fun_induction suffixFrom w v h <;> grind

@[simp] lemma tail_suffixFrom [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).tail = w.tail := by
  fun_induction suffixFrom w v h <;> grind

/-! ## map, foldl, foldr, any, all -/

/-- Map a function over every vertex (edges untouched). -/
def mapV {β : Type*} (f : α → β) : Walk α ε → Walk β ε
  | .singleton v => .singleton (f v)
  | .cons w v e => .cons (w.mapV f) (f v) e

/-- Map a function over every edge (vertices untouched). -/
def mapE {η : Type*} (g : ε → η) : Walk α ε → Walk α η
  | .singleton v => .singleton v
  | .cons w v e => .cons (w.mapE g) v (g e)

/-- Left fold over the vertices (head to tail). -/
def foldl {β : Type*} (f : β → α → β) (b : β) : Walk α ε → β
  | .singleton v => f b v
  | .cons w v _ => f (w.foldl f b) v

/-- Right fold over the vertices (tail to head). -/
def foldr {β : Type*} (f : α → β → β) (b : β) : Walk α ε → β
  | .singleton v => f v b
  | .cons w v _ => w.foldr f (f v b)

def any (p : α → Prop) : Walk α ε → Prop
  | .singleton v => p v
  | .cons w v _ => w.any p ∨ p v

def all (p : α → Prop) : Walk α ε → Prop
  | .singleton v => p v
  | .cons w v _ => w.all p ∧ p v

/-! ## nodup, nonstalling -/

/-- The walk has no repeated vertex. -/
def nodup : Walk α ε → Prop
  | .singleton _ => True
  | .cons w v _  => w.nodup ∧ v ∉ w

/-- The walk never stalls: no two consecutive vertices are equal. -/
def nonstalling : Walk α ε → Prop
  | .singleton _ => True
  | .cons w v _  => w.nonstalling ∧ w.tail ≠ v

/-- A walk is *closed* when its first and last vertex coincide. -/
def closed (w : Walk α ε) : Prop := w.head = w.tail

/-! ## takeWhile, dropWhile -/

/-- Take every vertex satisfying `p`, plus the first failure (if any). -/
@[grind] def takeWhile (w : Walk α ε) (p : α → Prop) [DecidablePred p] :
    Walk α ε :=
  match w with
  | .singleton x => .singleton x
  | .cons q x e =>
    if ∃ v ∈ q.toVertexList, ¬ p v then takeWhile q p
    else .cons q x e

/-- Drop the longest prefix on which `p` holds; result starts at first failure. -/
@[grind] def dropWhile (w : Walk α ε) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.toVertexList, ¬ p v) : Walk α ε :=
  match w with
  | .singleton x => .singleton x
  | .cons q x e =>
    if hq : ∃ v ∈ q.toVertexList, ¬ p v then .cons (dropWhile q p hq) x e
    else .singleton x

/-! ## loopErase, cycleErase -/

/-- Remove immediate stalls (consecutive duplicate vertices), keeping the
edge of the kept copy. Produces a non-stalling walk. -/
@[grind] def loopErase [DecidableEq α] : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons w v e =>
      if w.tail = v then loopErase w
      else .cons (loopErase w) v e

/-- Cycle erasure: jump past any vertex that has occurred before. Produces a
walk with no duplicate vertex (`nodup`). -/
@[grind] def cycleErase [DecidableEq α] : Walk α ε → Walk α ε
  | .singleton v => .singleton v
  | .cons w v e =>
      if h : v ∈ w then
        cycleErase (prefixUntil w v h)
      else
        .cons (cycleErase w) v e
  termination_by p => p.length
  decreasing_by
  · simp [length]
    grind [length_prefixUntil_le]
  · simp [length]

/-! ## Indexing -/

instance : GetElem (Walk α ε) ℕ α (fun w i ↦ i < w.toVertexList.length) where
  getElem w i h := w.toVertexList[i]

/-! ## Forgetful functor to `VertexSeq` -/

/-- Forget the edges, viewing a walk as its underlying vertex sequence. -/
@[grind] def toVertexSeq : Walk α ε → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v _ => .cons w.toVertexSeq v

@[simp, grind =] lemma toVertexSeq_head (w : Walk α ε) :
    w.toVertexSeq.head = w.head := by
  induction w <;> grind [toVertexSeq, VertexSeq.head, head]

@[simp, grind =] lemma toVertexSeq_tail (w : Walk α ε) :
    w.toVertexSeq.tail = w.tail := by
  cases w <;> grind [toVertexSeq, VertexSeq.tail, tail]

@[simp, grind =] lemma toVertexSeq_length (w : Walk α ε) :
    w.toVertexSeq.length = w.length := by
  induction w <;> grind [toVertexSeq, VertexSeq.length, length]

@[simp, grind =] lemma toVertexSeq_toList (w : Walk α ε) :
    w.toVertexSeq.toList = w.toVertexList := by
  induction w <;> grind [toVertexSeq, VertexSeq.toList, toVertexList]

/-! ### Commutation of vertex operations with `toVertexSeq`

For every operation that only touches vertices, the diagram

```
  Walk α ε  --φ-->  Walk α ε
     |                  |
  toVertexSeq      toVertexSeq
     ↓                  ↓
  VertexSeq α --φ->  VertexSeq α
```

commutes. -/

@[simp, grind =] lemma toVertexSeq_dropHead (w : Walk α ε) :
    w.dropHead.toVertexSeq = w.toVertexSeq.dropHead := by
  fun_induction dropHead <;> grind [toVertexSeq, VertexSeq.dropHead]

@[simp, grind =] lemma toVertexSeq_dropTail (w : Walk α ε) :
    w.dropTail.toVertexSeq = w.toVertexSeq.dropTail := by
  cases w <;> grind [toVertexSeq, dropTail, VertexSeq.dropTail]

@[simp, grind =] lemma toVertexSeq_prefixUntil [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) :
    (w.prefixUntil v h).toVertexSeq = w.toVertexSeq.prefixUntil v (by grind) := by
  fun_induction prefixUntil w v h <;>
    grind [toVertexSeq, prefixUntil, VertexSeq.prefixUntil]

@[simp, grind =] lemma toVertexSeq_suffixFrom [DecidableEq α] (w : Walk α ε)
    (v : α) (h : v ∈ w) :
    (w.suffixFrom v h).toVertexSeq = w.toVertexSeq.suffixFrom v (by grind) := by
  fun_induction suffixFrom w v h <;>
    grind [toVertexSeq, suffixFrom, VertexSeq.suffixFrom]

@[simp, grind =] lemma toVertexSeq_takeWhile (w : Walk α ε) (p : α → Prop)
    [DecidablePred p] :
    (w.takeWhile p).toVertexSeq = w.toVertexSeq.takeWhile p := by
  induction w with
  | singleton _ => rfl
  | cons q x e ih =>
    simp only [takeWhile, toVertexSeq, VertexSeq.takeWhile, toVertexSeq_toList]
    split
    · exact ih
    · rfl

@[simp, grind =] lemma toVertexSeq_dropWhile (w : Walk α ε) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toVertexList, ¬ p v) :
    (w.dropWhile p h).toVertexSeq =
      w.toVertexSeq.dropWhile p (by simpa using h) := by
  fun_induction dropWhile <;>
    grind [toVertexSeq, dropWhile, VertexSeq.dropWhile, toVertexList]

@[simp, grind =] lemma toVertexSeq_loopErase [DecidableEq α] (w : Walk α ε) :
    w.loopErase.toVertexSeq = w.toVertexSeq.loopErase := by
  fun_induction loopErase <;>
    grind [toVertexSeq, loopErase, VertexSeq.loopErase]

@[simp, grind =] lemma toVertexSeq_cycleErase [DecidableEq α] (w : Walk α ε) :
    w.cycleErase.toVertexSeq = w.toVertexSeq.cycleErase := by
  fun_induction cycleErase <;>
    grind [toVertexSeq, cycleErase, VertexSeq.cycleErase]

/-! ### Predicates pull back along `toVertexSeq` -/

@[simp, grind =] lemma toVertexSeq_nodup (w : Walk α ε) :
    w.toVertexSeq.nodup ↔ w.nodup := by
  induction w <;>
    grind [toVertexSeq, nodup, VertexSeq.nodup, mem_def, VertexSeq.mem_def,
           toVertexSeq_toList]

@[simp, grind =] lemma toVertexSeq_nonstalling (w : Walk α ε) :
    w.toVertexSeq.nonstalling ↔ w.nonstalling := by
  induction w <;>
    grind [toVertexSeq, nonstalling, VertexSeq.nonstalling]

@[simp, grind =] lemma toVertexSeq_closed (w : Walk α ε) :
    w.toVertexSeq.closed ↔ w.closed := by
  grind [VertexSeq.closed, closed]

/-! ## Graph conversion -/

open GraphLib

/-- The list of edges of `w` as labelled, unordered-endpoint `Edge α ε` records. -/
@[grind] def edges : Walk α ε → List (Edge α ε)
  | .singleton _ => []
  | .cons w v e => w.edges.concat ⟨e, s(w.tail, v)⟩

/-- The list of arcs of `w` as labelled, ordered-endpoint `Arc α ε` records. -/
@[grind] def arcs : Walk α ε → List (Arc α ε)
  | .singleton _ => []
  | .cons w v e => w.arcs.concat ⟨e, (w.tail, v)⟩

/-- View `w` as a `Graph` whose vertex set / edge set are exactly those
visited by the walk. -/
def toGraph (w : Walk α ε) : Graph α ε where
  vertexSet := { v | v ∈ w.toVertexList }
  edgeSet := { e | e ∈ w.edges }
  incidence' := by
    intro e he v hv
    induction w with
    | singleton _ => simp [edges] at he
    | cons w' u e' ih =>
      simp [edges] at he
      rcases he with he_old | he_new
      · -- e came from a smaller walk
        have hv' : v ∈ w'.toVertexList := ih he_old
        simp [toVertexList]; left; exact hv'
      · subst he_new
        -- e is the new edge ⟨e', s(w'.tail, u)⟩
        simp [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · simp [toVertexList]
        · simp [toVertexList]

/-- View `w` as a `DiGraph` whose vertex set / arc set are exactly those
visited by the walk. -/
def toDiGraph (w : Walk α ε) : DiGraph α ε where
  vertexSet := { v | v ∈ w.toVertexList }
  edgeSet := { a | a ∈ w.arcs }
  incidence' := by
    intro a ha
    induction w with
    | singleton _ => simp [arcs] at ha
    | cons w' u e' ih =>
      simp [arcs] at ha
      rcases ha with ha_old | ha_new
      · obtain ⟨h1, h2⟩ := ih ha_old
        refine ⟨?_, ?_⟩
        · simp [toVertexList]; left; exact h1
        · simp [toVertexList]; left; exact h2
      · subst ha_new
        refine ⟨?_, ?_⟩
        · simp [toVertexList]
        · simp [toVertexList]

end Walk
