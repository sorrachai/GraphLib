/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Predicates

/-!
# Vertex sequences: append and reverse

Concatenation and reversal of vertex sequences, with their head/tail/length
laws, associativity and involutivity, and the preservation of `nodup` and
`nonstalling`.

## Main definitions

* `VertexSeq.append` — concatenation, keeping both joining vertices.
* `VertexSeq.reverse` — reversal, swapping head and tail.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## append, reverse, and their laws -/

/-- Concatenate two sequences. The joining vertices `p.tail` and `q.head` are
*both* preserved. If they are equal the duplicate is intentional (the caller
may drop it with `dropTail`). -/
@[grind] def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons u v => .cons (append w u) v

instance : Append (VertexSeq α) := ⟨VertexSeq.append⟩

@[simp, grind =] lemma toList_append (p q : VertexSeq α) :
    (p.append q).toList = p.toList ++ q.toList := by
  induction q generalizing p with
  | singleton v =>
      simp [append, toList, List.concat_eq_append]
  | cons q v ih =>
      simp [append, toList, ih, List.concat_eq_append, List.append_assoc]

@[simp] lemma mem_append (v : α) (w1 w2 : VertexSeq α) :
    v ∈ w1 ++ w2 ↔ v ∈ w1 ∨ v ∈ w2 := by
  change v ∈ (w1.append w2).toList ↔ v ∈ w1.toList ∨ v ∈ w2.toList
  rw [toList_append, List.mem_append]

/-- Reverse a sequence: the head becomes the tail and vice versa. -/
@[grind] def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

@[simp] lemma mem_reverse (v : α) (w : VertexSeq α) :
    v ∈ w ↔ v ∈ w.reverse := by
  induction w with
  | singleton _ => simp [reverse]
  | cons w x ih =>
      have ih' : v ∈ w.toList ↔ v ∈ w.reverse.toList := by
        simpa [mem_def] using ih
      simp [reverse, toList_append, toList, List.concat_eq_append, ih',
        or_comm]

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

/-! ## Nodup and non-stalling preservation -/

/-- Appending disjoint `nodup` sequences preserves `nodup`. -/
@[grind] lemma nodup_append (p q : VertexSeq α) (hp : p.nodup) (hq : q.nodup)
    (hdisj : ∀ v : α, v ∈ p → v ∈ q → False) : (p.append q).nodup := by
  induction q with
  | singleton v =>
      simp [append, nodup]
      exact ⟨hp, fun hv => hdisj v hv (by grind)⟩
  | cons q v ih =>
      simp [append, nodup] at hq ⊢
      refine ⟨ih hq.1 (fun x hx hq' => hdisj x hx (by grind)), ?_⟩
      constructor
      · intro hpv
        exact hdisj v (by simpa [mem_def] using hpv) (by grind)
      · exact hq.2

/-- Reversal preserves `nodup`. -/
@[grind] lemma nodup_reverse (w : VertexSeq α) (h : w.nodup) :
    w.reverse.nodup := by
  fun_induction reverse w <;> grind [nodup_append, mem_reverse]

/-- An `append` is non-stalling exactly when both operands are and the joining
vertices differ. -/
@[grind] lemma nonstalling_append (p q : VertexSeq α) :
    (p.append q).nonstalling ↔
      p.nonstalling ∧ q.nonstalling ∧ p.tail ≠ q.head := by
  fun_induction append p q <;> grind

/-- Reversal preserves non-stalling. -/
@[grind] lemma nonstalling_reverse (w : VertexSeq α) :
    w.reverse.nonstalling ↔ w.nonstalling := by
  fun_induction reverse w <;> grind

/-! ## Interaction of dropTail with append and reverse -/

/-- Reversal preserves length. -/
@[simp, grind =] lemma length_reverse (w : VertexSeq α) :
    w.reverse.length = w.length := by
  fun_induction reverse w <;> grind

/-- For a non-trivial right operand, dropping the tail of an append drops the
tail of that operand. -/
@[simp, grind =] lemma dropTail_append_of_length_ne_zero (p q : VertexSeq α)
    (hq : q.length ≠ 0) :
    (p.append q).dropTail = p.append q.dropTail := by
  cases q with
  | singleton v =>
      simp [length] at hq
  | cons q v =>
      rfl

/-- Dropping the tail of a reverse is reversing the `dropHead`. -/
@[simp, grind =] lemma dropTail_reverse (w : VertexSeq α) :
    w.reverse.dropTail = w.dropHead.reverse := by
  induction w with
  | singleton v =>
      rfl
  | cons w v ih =>
      cases w with
      | singleton u =>
          rfl
      | cons t u =>
          rw [reverse]
          rw [dropTail_append_of_length_ne_zero]
          · exact congrArg (fun x => (singleton v).append x) (by simpa [reverse] using ih)
          · simp [length_reverse, length]

/-- The reversed interior of a cycle (drop the repeated tail) is `nodup`. -/
@[grind] lemma nodup_reverse_dropTail_of_cycle (w : VertexSeq α)
    (hclosed : w.closed) (hnodup : w.dropTail.nodup) :
    w.reverse.dropTail.nodup := by
  rw [dropTail_reverse]
  exact nodup_reverse w.dropHead (nodup_dropHead_of_closed_dropTail w hclosed hnodup)

/-- `nodup` of an append is symmetric in its operands. -/
lemma nodup_append_comm (p q : VertexSeq α) (h : (p.append q).nodup) :
    (q.append p).nodup := by
  rw [nodup_iff_toList_nodup]
  rw [toList_append]
  have hlist : (p.toList ++ q.toList).Nodup := by
    simpa [toList_append] using (nodup_iff_toList_nodup (p.append q)).1 h
  rw [List.nodup_append] at hlist ⊢
  aesop

end VertexSeq
