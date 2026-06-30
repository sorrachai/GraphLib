/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Subseq

/-!
# Vertex sequences: erasure operations

Two ways to remove redundancy from a vertex sequence:

* `VertexSeq.loopErase` — remove immediate stalls (consecutive duplicates); the
  result is `nonstalling`.
* `VertexSeq.cycleErase` — remove the detour between the two occurrences of any
  repeated vertex; the result is `nodup`.
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

@[grind] lemma loopErase_nonstalling [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.nonstalling := by
  induction w with
  | singleton _ => grind [loopErase]
  | cons w v ih =>
      by_cases h : w.tail = v <;> grind [loopErase, tail_loopErase]

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

/-- Membership in `cycleErase` implies membership in the original sequence. -/
@[grind] lemma cycleErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase ⊆ w := by
  intro x hx
  fun_induction cycleErase w <;> grind [prefixUntil_subset]

@[grind] lemma cycleErase_nodup [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.nodup := by
  fun_induction cycleErase w <;> grind [cycleErase_subset]

/-! ## Nodup preservation under loopErase -/

/-- Membership in `loopErase` implies membership in the original sequence. -/
@[grind] lemma loopErase_subset [DecidableEq α] (w : VertexSeq α) :
    w.loopErase ⊆ w := by
  intro x hx
  induction w with
  | singleton v =>
      grind [loopErase]
  | cons w v ih =>
      by_cases htail : w.tail = v
      · have hxw : x ∈ w := by
          exact ih (by simpa [loopErase, htail] using hx)
        grind
      · have hx' : x ∈ w.loopErase :+ v := by
          simpa [loopErase, htail] using hx
        rcases (mem_cons x v w.loopErase).1 hx' with hxold | rfl
        · exact (mem_cons x v w).2 (Or.inl (ih hxold))
        · exact (mem_cons x x w).2 (Or.inr rfl)

/-- `loopErase` preserves `nodup`. -/
@[grind] lemma nodup_loopErase [DecidableEq α] (w : VertexSeq α) (hw : w.nodup) :
    w.loopErase.nodup := by
  induction w with
  | singleton v => grind
  | cons w v ih =>
      by_cases htail : w.tail = v
      · grind
      · simp [loopErase, htail, nodup] at hw ⊢
        exact ⟨ih hw.1, fun hv => hw.2 (loopErase_subset w v hv)⟩

/-! ## Interaction with non-stalling and the tail -/

/-- On a non-stalling sequence, `loopErase` is the identity: there are no
consecutive duplicates to remove. -/
@[grind =] lemma loopErase_eq_self_of_nonstalling [DecidableEq α] (w : VertexSeq α)
    (h : w.nonstalling) : w.loopErase = w := by
  induction w with
  | singleton v => rfl
  | cons w v ih =>
      obtain ⟨hns, hne⟩ := h
      have hstep : (w.cons v).loopErase = (w.loopErase).cons v := by
        change (if w.tail = v then w.loopErase else (w.loopErase).cons v) = _
        rw [if_neg hne]
      rw [hstep, ih hns]

/-- `cycleErase` preserves the tail vertex. -/
@[grind =] lemma tail_cycleErase [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.tail = w.tail := by
  fun_induction cycleErase w <;> grind [tail_prefixUntil]

end VertexSeq
