/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan,
         Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Theory.Structures.VertexSeq.Subseq

/-!
# Vertex sequences: erasure operations

Two ways to remove redundancy from a vertex sequence:

* `VertexSeq.loopErase` — remove immediate stalls (consecutive duplicates); the
  result is `nonstalling`.
* `VertexSeq.cycleErase` — remove the detour between the two occurrences of any
  repeated vertex; the result is `nodup`.

## Main definitions

* `VertexSeq.loopErase`, `VertexSeq.cycleErase`.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## loopErase -/

/-- Remove immediate stalls (consecutive duplicate vertices). The result
satisfies `nonstalling`. -/
@[grind] def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if w.tail = v then loopErase w
      else .cons (loopErase w) v

/-- `loopErase` preserves the tail. -/
@[simp, grind =] lemma tail_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.tail = w.tail := by
  induction w with
  | singleton _ => rfl
  | cons w v ih =>
      by_cases h : w.tail = v <;> simp [loopErase, h, ih]

/-- Membership in `loopErase` implies membership in the original sequence. -/
@[grind] lemma loopErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.loopErase ⊆ w := by
  intro x hx
  induction w <;> grind [loopErase]

/-- `loopErase` always produces a non-stalling sequence: that is the point of
the operation. -/
@[grind] lemma nonstalling_loopErase [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.nonstalling := by
  induction w with
  | singleton _ => grind [loopErase]
  | cons w v ih =>
      by_cases h : w.tail = v <;> grind [loopErase, tail_loopErase]

/-- `loopErase` preserves `nodup`. -/
@[grind] lemma nodup_loopErase [DecidableEq α] (w : VertexSeq α) (hw : w.nodup) :
    w.loopErase.nodup := by
  induction w <;> grind [loopErase_subset]

/-- On a non-stalling sequence, `loopErase` is the identity: there are no
consecutive duplicates to remove. -/
@[grind =] lemma loopErase_eq_self_of_nonstalling [DecidableEq α] (w : VertexSeq α)
    (h : w.nonstalling) : w.loopErase = w := by
  induction w <;> grind

/-! ## cycleErase -/

/-- Cycle erasure: whenever a vertex repeats, drop the intermediate detour
between its two occurrences. The result satisfies `nodup`. -/
@[grind] def cycleErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if h : v ∈ w then
        cycleErase (prefixUntil w v h)
      else
        .cons (cycleErase w) v
  termination_by p => p.length
  decreasing_by
  · simp [length]
    grind [length_prefixUntil_le]
  · simp [length]

/-- `cycleErase` preserves the tail vertex. -/
@[grind =] lemma tail_cycleErase [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.tail = w.tail := by
  fun_induction cycleErase w <;> grind [tail_prefixUntil]

/-- `cycleErase` preserves the head vertex. Erasure only ever replaces a sequence
by one of its `prefixUntil` cuts, and those keep the head. -/
@[grind =] lemma head_cycleErase [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.head = w.head := by
  fun_induction cycleErase w <;> grind [head_prefixUntil]

/-- Membership in `cycleErase` implies membership in the original sequence. -/
@[grind] lemma cycleErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase ⊆ w := by
  intro x hx
  fun_induction cycleErase w <;> grind [prefixUntil_subset]

/-- `cycleErase` always produces a duplicate-free sequence: that is the point of
the operation. -/
@[grind] lemma nodup_cycleErase [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.nodup := by
  fun_induction cycleErase w <;> grind [cycleErase_subset]

end VertexSeq
