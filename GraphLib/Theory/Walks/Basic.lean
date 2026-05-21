/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.Sym.Sym2

/-!
# Walks

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

variable {α : Type*}

/-- A non-empty sequence of vertices in `α`, used as the underlying data of a
walk. `cons w u` extends `w` on the right by the vertex `u`. -/
@[grind] inductive VertexSeq (α : Type*)
  | singleton (v : α) : VertexSeq α
  | cons (w : VertexSeq α) (v : α) : VertexSeq α

namespace VertexSeq

/-! ## Basic accessors -/

/-- The list of vertices visited by the sequence, in order from head to tail. -/
@[grind] def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons p v => p.toList.concat v

/-- The number of *edges* in the sequence: `0` for a `singleton`, otherwise
one plus the length of the prefix. -/
@[grind] def length : VertexSeq α → ℕ
  | .singleton _ => 0
  | .cons w _ => 1 + w.length

/-- The first vertex of the sequence. -/
@[grind] def head : VertexSeq α → α
  | .singleton v => v
  | .cons w _ => head w

/-- The last vertex of the sequence. -/
@[grind] def tail : VertexSeq α → α
  | .singleton v => v
  | .cons _ v => v

/-- `head` of a singleton is the lone vertex. -/
@[grind =] lemma head_singleton (u : α) :
    (VertexSeq.singleton u).head = u := by simp [head]

/-- `tail` of a singleton is the lone vertex. -/
@[grind =] lemma tail_singleton (u : α) :
    (VertexSeq.singleton u).tail = u := by simp [tail]

/-- `head` is preserved by right-extending `cons`. -/
@[grind =] lemma head_cons (w : VertexSeq α) (u : α) :
    (w.cons u).head = w.head := rfl

/-- `tail` of `cons w u` is the freshly appended vertex `u`. -/
@[grind =] lemma tail_cons (w : VertexSeq α) (u : α) :
    (w.cons u).tail = u := rfl

/-- The `head` always appears in the underlying list of vertices. -/
@[grind ←] lemma head_mem_toList (w : VertexSeq α) : some w.head = w.toList.head? := by
  induction w <;> grind [VertexSeq.head, VertexSeq.toList]

/-! ## dropHead, dropTail -/

/-- Drop the first vertex of the sequence (returns the sequence unchanged
when it is a singleton). -/
@[grind] def dropHead : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons (.singleton _) v => .singleton v
  | .cons w v => .cons (dropHead w) v

/-- Drop the last vertex of the sequence (returns the sequence unchanged
when it is a singleton). -/
@[grind] def dropTail : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w _ => w

/-! ## append, reverse, and their laws -/

/-- Concatenate two sequences. The joining vertices `p.tail` and `q.head` are
*both* preserved. If they are equal the duplicate is intentional (caller may
drop it with `dropTail`). -/
@[grind] def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons u v => .cons (append w u) v

/-- Reverse a sequence: the head becomes the tail and vice versa. -/
@[grind] def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

/-- Length of an append is the sum of lengths plus one (for the duplicated
joining vertex contributing an extra edge). -/
@[simp, grind =] lemma length_append (p q : VertexSeq α) :
    (p.append q).length = p.length + q.length + 1 := by
  fun_induction append p q <;> grind

/-- `tail` of an append is the tail of the right operand. -/
@[simp, grind =] lemma tail_append (p q : VertexSeq α) :
    (p.append q).tail = q.tail := by
  fun_induction append <;> simp_all [tail]

/-- `head` of an append is the head of the left operand. -/
@[simp, grind =] lemma head_append (p q : VertexSeq α) :
    (p.append q).head = p.head := by
  fun_induction append <;> simp_all [head]

/-- Appending a singleton on the right yields `x` as the new tail. -/
@[simp, grind =] lemma tail_append_singleton (p : VertexSeq α) (x : α) :
    (p.append (.singleton x)).tail = x := by
  grind

/-- Appending on the left of a singleton makes `x` the new head. -/
@[simp, grind =] lemma head_singleton_append (p : VertexSeq α) (x : α) :
    ((VertexSeq.singleton x).append p).head = x := by
  grind

/-- `append` is associative. -/
@[simp, grind =] lemma append_assoc (p q r : VertexSeq α) :
    (p.append q).append r = p.append (q.append r) := by
  fun_induction append q r <;> simp_all [append]

/-- Reversing a singleton leaves it unchanged. -/
@[grind =] lemma reverse_singleton (v : α) :
    (VertexSeq.singleton v).reverse = .singleton v := rfl

/-- Reverse distributes over `append`, swapping the order of operands. -/
@[simp, grind =] lemma reverse_append (p q : VertexSeq α) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  fun_induction append <;> simp_all [reverse]

/-- `reverse` is an involution. -/
@[simp, grind =] lemma reverse_reverse (p : VertexSeq α) :
    p.reverse.reverse = p := by
  fun_induction reverse p <;> grind

/-- The head of the reverse is the tail of the original. -/
@[simp, grind =] lemma head_reverse (p : VertexSeq α) :
    p.reverse.head = p.tail := by
  fun_induction reverse p <;> grind

/-- The tail of the reverse is the head of the original. -/
@[simp, grind =] lemma tail_reverse (p : VertexSeq α) :
    p.reverse.tail = p.head := by
  fun_induction reverse p <;> grind

/-- Dropping the tail does not affect the head. -/
@[simp, grind =] lemma head_dropTail (p : VertexSeq α) :
    p.dropTail.head = p.head := by
  fun_induction reverse p <;> grind

/-! ## takeUntil, dropUntil, loopErase -/

/-- Take vertices until the first occurrence of `v` (including `v`). -/
@[simp, grind] def takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then takeUntil w2 v h2
    else .cons w2 x

/-- Drop vertices until the last occurrence of `v` (not including `v`). -/
@[simp, grind] def dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2.toList then .cons (dropUntil w2 v h2) x
    else .singleton x

/-- `takeUntil` never increases the length. -/
@[simp] lemma length_takeUntil_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.takeUntil v h).length ≤ w.length := by
  fun_induction takeUntil w v h <;> grind

/-- `dropUntil` never increases the length. -/
@[simp] lemma length_dropUntil_le [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).length ≤ w.length := by
  fun_induction dropUntil w v h <;> grind

/-- `takeUntil` preserves the head. -/
@[simp, grind =] lemma head_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (takeUntil w v h).head = w.head := by
  induction w <;> grind

/-- The tail of `takeUntil w v h` is the target vertex `v`. -/
@[simp, grind =] lemma tail_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (takeUntil w v h).tail = v := by
  induction w <;> grind

/-- Membership in `takeUntil` implies membership in the original sequence. -/
@[simp, grind →] lemma mem_takeUntil [DecidableEq α] (w : VertexSeq α)
    (v x : α) (h : v ∈ w.toList) :
    x ∈ (takeUntil w v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

/-- The head of `dropUntil w v h` is the target vertex `v`. -/
@[simp, grind =] lemma head_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).head = v := by
  induction w <;> grind

/-- `dropUntil` preserves the tail. -/
@[simp, grind =] lemma tail_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) : (w.dropUntil v h).tail = w.tail := by
  fun_induction VertexSeq.dropUntil w v h <;> simp [VertexSeq.tail]

/-- Membership in `dropUntil` implies membership in the original sequence. -/
@[simp, grind →] lemma mem_dropUntil [DecidableEq α] (w : VertexSeq α) (v x : α)
    (h : v ∈ w.toList) :
    x ∈ (w.dropUntil v h).toList → x ∈ w.toList := by
  induction w generalizing v <;> grind

/-- Self-loop erasure: scan the sequence and, whenever the current vertex
already appears earlier, drop the intermediate detour. The result has the
same `head` and `tail` and is `Nodup` (see `head_loopErase`, `tail_loopErase`,
`nodup_loopErase`). -/
@[grind] def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if h : v ∈ w.toList then
        loopErase (takeUntil w v h)
      else
        .cons (loopErase w) v
  termination_by p => p.length
  decreasing_by
  · simp [length]
    grind [length_takeUntil_le]
  · simp [length]

/-- Membership in `loopErase` implies membership in the original sequence. -/
lemma mem_loopErase [DecidableEq α] (w : VertexSeq α) :
    ∀ {x : α}, x ∈ w.loopErase.toList → x ∈ w.toList := by
  fun_induction loopErase w <;> grind [toList, mem_takeUntil]

/-- The vertex list produced by `loopErase` has no duplicates. -/
theorem nodup_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.toList.Nodup := by
  fun_induction VertexSeq.loopErase w <;> grind [toList, mem_loopErase]

/-- `loopErase` preserves the head. -/
@[simp] lemma head_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.head = w.head := by
  fun_induction loopErase w <;> grind

/-- `loopErase` preserves the tail. -/
@[simp] lemma tail_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.tail = w.tail := by
  fun_induction loopErase w <;> grind

end VertexSeq

/-! ## IsWalk, Walk core data -/

/-- A `VertexSeq` is a walk when consecutive vertices differ (no immediate
backtracking). The predicate is graph-agnostic, and downstream files can
specialise it by adding an adjacency hypothesis. -/
@[grind] inductive IsWalk : VertexSeq α → Prop
  | singleton (v : α) : IsWalk (.singleton v)
  | cons (w : VertexSeq α) (u : α)
      (hw : IsWalk w)
      (hneq : w.tail ≠ u) :
      IsWalk (.cons w u)

grind_pattern IsWalk.singleton => IsWalk (.singleton v)
grind_pattern IsWalk.cons => IsWalk (.cons w u)

/-- A walk is a `VertexSeq` satisfying the `IsWalk` predicate. -/
def Walk (α : Type*) := { w : VertexSeq α // IsWalk w }

namespace Walk
open VertexSeq

/-! ## Basic `IsWalk` helper lemmas -/

/-- A `cons` walk has a walk as its prefix. -/
@[simp, grind =>] lemma isWalk_of_cons (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : IsWalk w2 := by
  grind

/-- The tail of the prefix of a `cons` walk differs from the new head. -/
@[simp, grind <=] lemma tail_ne_of_isWalk_cons (w2 : VertexSeq α) (v : α)
    (valid : IsWalk (w2.cons v)) : w2.tail ≠ v := by
  grind

/-- The concatenation of two walks meeting at distinct endpoints is a walk. -/
@[grind ←]
lemma isWalk_append (w1 w2 : VertexSeq α)
    (h1 : IsWalk w1) (h2 : IsWalk w2) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.append w2) := by
  fun_induction w1.append w2 <;> grind

/-- Prepending a singleton with a distinct vertex preserves the walk property. -/
@[grind ←]
theorem isWalk_singleton_append (p : VertexSeq α) (v : α)
    (h : IsWalk p) (h2 : p.head ≠ v) :
    IsWalk ((VertexSeq.singleton v).append p) := by grind

/-- An `append` being a walk implies both factors are walks and the joining
endpoints differ. -/
@[grind →]
theorem isWalk_of_append (p q : VertexSeq α) (h : IsWalk (p.append q)) :
    IsWalk p ∧ IsWalk q ∧ p.tail ≠ q.head := by
  fun_induction append <;> grind

/-- `IsWalk` is preserved by reversal in either direction. -/
@[simp, grind =]
lemma isWalk_reverse_iff (w : VertexSeq α) : IsWalk w.reverse ↔ IsWalk w := by
  fun_induction reverse <;> grind

/-- A sequence with distinct vertices is automatically a walk. -/
lemma isWalk_of_nodup (w : VertexSeq α) (h : w.toList.Nodup) : IsWalk w := by
  induction w <;> grind

/-- `takeUntil` of a walk is a walk. -/
@[grind →]
lemma isWalk_takeUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) (hw : IsWalk w) :
    IsWalk (w.takeUntil v h) := by
  induction hw generalizing v <;> grind

/-- `dropUntil` of a walk is a walk. -/
@[grind →]
lemma isWalk_dropUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w.toList) (hw : IsWalk w) :
    IsWalk (w.dropUntil v h) := by
  induction hw generalizing v <;> grind

/-- `loopErase` always produces a walk (its underlying list is `Nodup`). -/
lemma isWalk_loopErase [DecidableEq α] (w : VertexSeq α) : IsWalk w.loopErase := by
  grind [isWalk_of_nodup, nodup_loopErase]

/-! ## support, head, tail, length, dropTail for Walk -/

/-- The list of vertices visited by the walk, in order. -/
@[simp, grind] def support (w : Walk α) : List α := w.val.toList

/-- The first vertex of the walk. -/
abbrev head (w : Walk α) : α := w.val.head

/-- The last vertex of the walk. -/
abbrev tail (w : Walk α) : α := w.seq.tail

/-- The number of edges in the walk. -/
abbrev length (w : Walk α) : ℕ := w.seq.length

/-- Drop the last vertex of the walk. -/
abbrev dropTail (w : Walk α) : Walk α :=
  { seq := w.seq.dropTail
    valid := by grind [Walk] }

/-- Extend a walk by appending a single vertex `u` distinct from `w.tail`. -/
def append_single (w : Walk α) (u : α) (h : u ≠ w.tail) : Walk α :=
  { seq := w.seq.cons u
    valid := by grind [Walk]}

/-- `dropTail` preserves the head. -/
@[simp, grind =]
lemma head_dropTail (w : Walk α) : w.dropTail.head = w.head := by
  cases w
  induction valid <;> grind

/-- If dropping the tail leaves the tail unchanged, the walk has length zero. -/
@[simp, grind .]
lemma length_eq_zero_of_dropTail_tail (w : Walk α) (h : w.dropTail.tail = w.tail) :
    w.length = 0 := by
  cases w
  induction valid <;> grind

/-- A walk of length zero is a singleton, so its head equals its tail. -/
@[simp, grind ←]
lemma head_eq_tail_of_length_zero (w : Walk α) (h : w.length = 0) :
    w.head = w.tail := by
  cases w
  induction valid <;> grind

/-! ## Walk append, reverse and related lemmas -/

/-- The sequence-level concatenation of two walks (under the meeting condition)
is itself a walk. -/
@[grind ←]
lemma isWalk_seq_append (w1 w2 : Walk α) (hneq : w1.tail ≠ w2.head) :
    IsWalk (w1.seq.append w2.seq) := by
  cases w1
  cases w2
  grind

/-- Concatenate two walks meeting at a shared vertex (`w1.tail = w2.head`).
The duplicated joining vertex is collapsed by dropping the tail of `w1`. -/
@[grind =]
def append (w1 w2 : Walk α) (h : w1.tail = w2.head) : Walk α :=
  if h1 : w1.length = 0 then w2
  else
    { seq := w1.dropTail.seq.append w2.seq
      valid := by grind [Walk] }

/-- Reverse a walk: head and tail are swapped. -/
@[grind =]
def reverse (w : Walk α) : Walk α :=
  { seq := w.seq.reverse
    valid := by grind [Walk] }

/-- The head of a reversed walk is the original tail. -/
@[simp, grind =] lemma head_reverse (w : Walk α) :
    w.reverse.head = w.tail := by grind

/-- The tail of a reversed walk is the original head. -/
@[simp, grind =] lemma tail_reverse (w : Walk α) :
    w.reverse.tail = w.head := by grind

/-- The head of an append is the head of the left walk. -/
@[simp, grind =] lemma head_append (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).head = w1.head := by
  cases w1
  induction valid <;> grind

/-- The tail of an append is the tail of the right walk. -/
@[simp, grind =] lemma tail_append (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).tail = w2.tail := by grind

/-- Length of an `append` adds the lengths (the duplicated joining vertex is
absorbed by dropping the tail of `w1`). -/
@[simp, grind =] lemma length_append (w1 w2 : Walk α) (h : w1.tail = w2.head) :
    (Walk.append w1 w2 h).length = w1.length + w2.length := by
  unfold Walk.append
  by_cases h1 : w1.length = 0
  · grind
  · have hdrop : w1.dropTail.length + 1 = w1.length := by
      cases w1
      induction valid <;> grind
    grind

/-! ## Path, cycle -/

/-- A path is a walk whose support has no repeated vertices. -/
@[grind =] def Path (α : Type*) := { w : Walk α // w.support.Nodup }

/-- Erase self-loops from a walk to obtain a path with the same endpoints. -/
def toPath [DecidableEq α] (w : Walk α) : Path α :=
  { seq := w.seq.loopErase
    valid := isWalk_loopErase w.seq }

/-- `toPath` always produces a path. -/
theorem toPath_isPath [DecidableEq α] (w : Walk α) : IsPath (toPath w) := by
  unfold IsPath toPath support
  simpa using nodup_loopErase w.seq

/-- `toPath` preserves the tail. -/
lemma tail_toPath [DecidableEq α] (w : Walk α) : (toPath w).tail = w.tail := by
  grind [tail_loopErase]

/-- `toPath` preserves the head. -/
lemma head_toPath [DecidableEq α] (w : Walk α) : (toPath w).head = w.head := by
  grind [head_loopErase]

/-- A cycle is a walk of length at least 3 whose endpoints coincide and whose
interior (the walk with its last vertex dropped) is a path. -/
def IsCycle (w : Walk α) : Prop :=
  3 ≤ w.length ∧ w.head = w.tail ∧ IsPath w.dropTail

/-! ## Some more helper lemmas -/

/-- `takeUntil` at the head of a sequence yields just the singleton head. -/
@[simp, grind .] lemma takeUntil_head [DecidableEq α] (w : VertexSeq α)
    (h : w.head ∈ w.toList) :
    w.takeUntil w.head h = VertexSeq.singleton w.head := by
  induction w <;> grind

/-- `dropUntil` at the head of a sequence returns the whole sequence. -/
@[simp, grind .] lemma dropUntil_head [DecidableEq α] (w : VertexSeq α)
    (h : w.head ∈ w.toList) :
    w.dropUntil w.head h = w := by
  induction w <;> grind

/-- Splitting a sequence at an interior vertex `v` and rejoining via `append`
reconstructs the original. -/
@[simp, grind →] lemma dropTail_takeUntil_append_dropUntil [DecidableEq α]
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList) (hne : v ≠ w.head) :
    (w.takeUntil v h).dropTail.append (w.dropUntil v h) = w := by
  induction w generalizing v <;> grind

/-- A walk can be reconstructed as the `append` of its prefix up to a chosen
vertex `u ∈ w.support` and its suffix from `u`. -/
@[simp, grind →] lemma eq_append_takeUntil_dropUntil [DecidableEq α]
    (w : Walk α) (u : α) (hu : u ∈ w.support) :
    w = Walk.append
      ⟨w.seq.takeUntil u hu, isWalk_takeUntil w.seq u hu w.valid⟩
      ⟨w.seq.dropUntil u hu, isWalk_dropUntil w.seq u hu w.valid⟩
      (by grind) := by
  by_cases h : u = w.head
  · ext
    grind
  · ext
    grind

/-! ## Re-rooting a cycle -/

/-- Re-root a cycle at any chosen vertex in its support. -/
@[simp, grind] def rerootCycle [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
    (u : α) (hu : u ∈ w.support) : Walk α :=
  Walk.append
    ⟨w.seq.dropUntil u hu, isWalk_dropUntil w.seq u hu w.valid⟩
    ⟨w.seq.takeUntil u hu, isWalk_takeUntil w.seq u hu w.valid⟩
    (by
      rcases hcyc with ⟨_, hht, _⟩
      grind)

/-- `toList` of an append is the concatenation in reverse order (since `cons`
extends on the right). -/
@[simp, grind =] lemma toList_append (p q : VertexSeq α) :
    (p.append q).toList = q.toList ++ p.toList := by
  induction q generalizing p <;> grind

/-- Dropping the tail commutes with `append` as long as the right walk is not
collapsed to a singleton. -/
lemma dropTail_append (w1 w2 : Walk α) (h : w1.tail = w2.head)
    (hlen : w2.head ≠ w2.tail) :
    (Walk.append w1 w2 h).dropTail = Walk.append w1 w2.dropTail (by grind) := by
  by_cases h1 : w1.length = 0
  · grind
  · ext
    cases w2
    induction valid <;> grind

/-- Re-rooting a cycle at any vertex on it yields another cycle. -/
lemma isCycle_rerootCycle [DecidableEq α] (w : Walk α) (hcyc : IsCycle w)
    (u : α) (hu : u ∈ w.support) :
    IsCycle (rerootCycle w hcyc u hu) := by
  have h2 : w.length = (w.rerootCycle hcyc u hu).length := by grind
  rcases hcyc with ⟨hlen, hht, hpath⟩
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · by_cases h : u = w.head
    · have hz : w.length ≠ 0 := by omega
      grind
    · grind [dropTail_append]

end Walk
