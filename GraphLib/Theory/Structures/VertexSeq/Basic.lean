/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.List.Basic

/-!
# Vertex sequences: carrier and basic accessors

A `VertexSeq α` is a non-empty inductive sequence of vertices, with a
`singleton` base case and a right-extending `cons`. It is the underlying
carrier for walks, paths and cycles in the graph theory library.

This file sets up the carrier together with its most primitive structure: the
`length`/`head`/`tail`/`toList` accessors, the `Membership` and `HasSubset`
instances, and the endpoint-dropping operations `dropHead`/`dropTail`.

## Main definitions

* `VertexSeq α` — non-empty sequence of vertices.
* `VertexSeq.head`, `VertexSeq.tail` — first and last vertex.
* `VertexSeq.length` — number of *edges* (one less than the vertex count).
* `VertexSeq.toList` — the underlying list of visited vertices.
* `VertexSeq.dropHead`, `VertexSeq.dropTail` — drop the first or last vertex.
-/

variable {α : Type*}

/-- A type that admits a right-extension operation. -/
class Snoc (γ δ : Type*) where
  /-- Append a single element on the right. -/
  snoc : γ → δ → γ

scoped[Snoc] infixl:67 " :+ " => Snoc.snoc

/-- A non-empty inductive sequence of vertices. `cons w v` extends `w` on the
right by appending the vertex `v`. -/
@[grind] inductive VertexSeq (α : Type*)
  | singleton (v : α) : VertexSeq α
  | cons (w : VertexSeq α) (v : α) : VertexSeq α

instance : Snoc (VertexSeq α) α := ⟨VertexSeq.cons⟩

-- The matching `Snoc (Walk α ε) (α × ε)` instance lives in `Walk.lean`, since
-- `Walk` is only defined there (and that file imports this one).

namespace VertexSeq

scoped infixl:67 " :+ " => VertexSeq.cons

/-! ## Basic accessors -/

/-- The number of *edges* in the sequence: `0` for a `singleton`, otherwise one
plus the length of the prefix. -/
@[grind] def length : VertexSeq α → ℕ
  | .singleton _ => 0
  | .cons w _ => 1 + w.length

/-- The first vertex of the sequence. -/
@[grind] def head : VertexSeq α → α
  | .singleton v => v
  | .cons w _ => w.head

/-- The last vertex of the sequence. -/
@[grind] def tail : VertexSeq α → α
  | .singleton v => v
  | .cons _ v => v

/-- The list of vertices visited by the sequence, in order from head to tail. -/
@[grind] def toList : VertexSeq α → List α
  | .singleton v => [v]
  | .cons w v => w.toList.concat v

@[simp, grind =] lemma head_singleton (u : α) :
    (VertexSeq.singleton u).head = u := rfl

@[simp, grind =] lemma head_cons (w : VertexSeq α) (u : α) :
    (w.cons u).head = w.head := rfl

@[simp, grind =] lemma tail_singleton (u : α) :
    (VertexSeq.singleton u).tail = u := rfl

@[simp, grind =] lemma tail_cons (w : VertexSeq α) (u : α) :
    (w.cons u).tail = u := rfl

/-- The `head` belongs to the underlying list of vertices. -/
@[simp, grind] lemma head_mem (w : VertexSeq α) : w.head ∈ w.toList := by
  induction w with
  | singleton _ =>
    simp [head, toList]
  | cons w _ ih =>
    simp [head, toList]
    exact Or.inl ih

/-- The `tail` belongs to the underlying list of vertices. -/
@[simp, grind] lemma tail_mem (w : VertexSeq α) : w.tail ∈ w.toList := by
  cases w with
  | singleton _ => simp [tail, toList]
  | cons _ _ => simp [tail, toList]

/-- The underlying list has `length + 1` vertices. -/
lemma length_toList (w : VertexSeq α) : w.toList.length = w.length + 1 := by
  induction w <;> grind

/-- `toList` is injective. -/
@[grind] theorem toList_injective : Function.Injective (@toList α) := by
  intro x y hxy
  induction x generalizing y with
  | singleton v =>
    cases y with
    | singleton w => simpa [toList] using hxy
    | cons w u =>
      exfalso
      simp only [toList] at hxy
      have hlen := congrArg List.length hxy
      simp only [List.length_singleton, List.length_concat] at hlen
      have := length_toList w
      omega
  | cons w v ih =>
    cases y with
    | singleton w' =>
      exfalso
      simp only [toList] at hxy
      have hlen := congrArg List.length hxy
      simp only [List.length_singleton, List.length_concat] at hlen
      have := length_toList w
      omega
    | cons w' v' =>
      simp only [toList, List.concat_eq_append] at hxy
      have hlen : w.toList.length = w'.toList.length := by
        have hl := congrArg List.length hxy
        simp only [List.length_append, List.length_singleton] at hl
        omega
      obtain ⟨hw, hv⟩ := List.append_inj hxy hlen
      obtain rfl := ih hw
      simp at hv
      exact congrArg _ hv

/-! ## Membership -/

instance : Membership α (VertexSeq α) := ⟨fun w v ↦ v ∈ w.toList⟩

@[simp, grind] theorem mem_def {v : α} (w : VertexSeq α) :
    v ∈ w ↔ v ∈ w.toList := Iff.rfl

@[simp] lemma mem_cons (v u : α) (w : VertexSeq α) :
    v ∈ w :+ u ↔ v ∈ w ∨ v = u := by
  grind

instance [DecidableEq α] (v : α) (w : VertexSeq α) : Decidable (v ∈ w) :=
  inferInstanceAs (Decidable (v ∈ w.toList))

instance : HasSubset (VertexSeq α) := ⟨fun w1 w2 ↦ ∀ v ∈ w1, v ∈ w2⟩

@[simp, grind] theorem subset_def {w1 w2 : VertexSeq α} :
    w1 ⊆ w2 ↔ ∀ v ∈ w1, v ∈ w2 := Iff.rfl

/-! ## dropHead, dropTail -/

/-- Drop the first vertex of the sequence (returns the sequence unchanged when
it is a singleton). -/
@[grind] def dropHead : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons (.singleton _) v => .singleton v
  | .cons w v => w.dropHead :+ v

/-- Drop the last vertex of the sequence (returns the sequence unchanged when
it is a singleton). -/
@[grind] def dropTail : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w _ => w

/-- Dropping the tail does not affect the head. -/
@[simp, grind =] lemma head_dropTail (p : VertexSeq α) :
    p.dropTail.head = p.head := by
  cases p <;> grind

/-- Dropping the first vertex does not affect the tail. -/
@[simp, grind =] lemma tail_dropHead (w : VertexSeq α) :
    w.dropHead.tail = w.tail := by
  fun_induction dropHead w <;> grind

/-- Dropping the tail of a `cons` recovers the prefix length. -/
@[simp, grind =] lemma length_dropTail_cons (w : VertexSeq α) (v : α) :
    (w :+ v).dropTail.length = w.length := rfl

/-- A length-zero sequence is a single vertex, so its head and tail agree. -/
@[simp, grind =] lemma head_eq_tail_of_length_zero (w : VertexSeq α)
    (h : w.length = 0) : w.head = w.tail := by
  cases w with
  | singleton v =>
      rfl
  | cons w v =>
      simp [length] at h

/-- For a non-trivial sequence, dropping the tail drops exactly one edge. -/
@[simp, grind =] lemma dropTail_length_succ (w : VertexSeq α) (h : w.length ≠ 0) :
    w.dropTail.length + 1 = w.length := by
  cases w with
  | singleton v =>
      exact (h rfl).elim
  | cons w v =>
      simp [length, dropTail]
      omega

end VertexSeq
