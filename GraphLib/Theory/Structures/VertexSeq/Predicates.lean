/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Basic

/-!
# Vertex sequences: structural predicates

The three predicates that classify the shape of a vertex sequence:

* `VertexSeq.nodup` — no repeated vertex.
* `VertexSeq.nonstalling` — no two consecutive vertices are equal.
* `VertexSeq.closed` — the first and last vertex coincide.

This file states their definitions together with the preservation lemmas that
only involve the endpoint-dropping operations of `Basic`; preservation under
`append`, `reverse`, the subsequence operations, etc. lives alongside those
operations in their own files.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## Definitions -/

/-- The sequence has no repeated vertex. -/
@[grind] def nodup : VertexSeq α → Prop
  | .singleton _ => True
  | .cons w v    => w.nodup ∧ v ∉ w

/-- The sequence never stalls: no two consecutive vertices are equal. -/
@[grind] def nonstalling : VertexSeq α → Prop
  | .singleton _ => True
  | .cons w v    => w.nonstalling ∧ w.tail ≠ v

/-- A vertex sequence is *closed* when its first and last vertex coincide. -/
@[grind] def closed (w : VertexSeq α) : Prop := w.head = w.tail

@[grind] lemma nodup_nonstalling (w : VertexSeq α) (h : w.nodup) :
    w.nonstalling := by induction w <;> grind

/-! ## Nodup preservation under dropHead, dropTail -/

/-- A `dropHead` result is contained in the original sequence. -/
@[grind] lemma dropHead_subset (w : VertexSeq α) : w.dropHead ⊆ w := by
  intro v hv
  fun_induction dropHead w <;> grind

/-- Dropping the first vertex preserves `nodup`. -/
@[grind] lemma nodup_dropHead (w : VertexSeq α) (h : w.nodup) :
    w.dropHead.nodup := by
  induction w with
  | singleton _ => grind
  | cons w v ih =>
    cases w with
    | singleton _ => grind
    | cons t u =>
      simp [nodup] at h ⊢
      exact ⟨ih h.1, fun hv => h.2 (dropHead_subset (t :+ u) v hv)⟩

/-- Dropping the last vertex preserves `nodup`. -/
@[grind] lemma nodup_dropTail (w : VertexSeq α) (h : w.nodup) :
    w.dropTail.nodup := by
  cases w <;> grind

/-! ## Non-stalling preservation under dropHead, dropTail -/

/-- Dropping the first vertex preserves non-stalling. -/
@[grind] lemma nonstalling_dropHead (w : VertexSeq α) (h : w.nonstalling) :
    w.dropHead.nonstalling := by
  fun_induction dropHead w <;> grind

/-- Dropping the last vertex preserves non-stalling. -/
@[grind] lemma nonstalling_dropTail (w : VertexSeq α) (h : w.nonstalling) :
    w.dropTail.nonstalling := by
  cases w <;> grind

/-! ## Nodup, closedness and the underlying list -/

/-- A closed `nodup` sequence has length zero: a repeated endpoint forces a
duplicate unless the sequence is a single vertex. -/
@[grind] lemma length_zero_of_nodup_head_eq_tail (w : VertexSeq α)
    (hnd : w.nodup) (hht : w.head = w.tail) : w.length = 0 := by
  cases w with
  | singleton v =>
      rfl
  | cons w v =>
      exfalso
      exact hnd.2 (by
        have h : w.head = v := by simpa using hht
        change v ∈ w
        rw [← h]
        exact head_mem w)

/-- In a non-trivial `nodup` sequence, the head does not reappear after dropping
it. -/
@[grind] lemma head_not_mem_dropHead_of_nodup (w : VertexSeq α)
    (hnd : w.nodup) (hpos : w.length ≠ 0) : w.head ∉ w.dropHead := by
  induction w with
  | singleton v =>
      exact (hpos rfl).elim
  | cons w v ih =>
      cases w with
      | singleton u =>
          simpa [dropHead, nodup, mem_def, toList, eq_comm] using hnd.2
      | cons t u =>
          intro hmem
          simp [nodup] at hnd
          rcases (mem_cons ((t :+ u).head) v (t :+ u).dropHead).1 hmem with hprefix | hlast
          · exact ih hnd.1 (by simp [length]) hprefix
          · exact hnd.2 (by
              rw [← hlast]
              exact head_mem (t :+ u))

/-- For a closed sequence with a `nodup` interior (drop the repeated tail), the
opposite interior (drop the repeated head) is also `nodup`. -/
@[grind] lemma nodup_dropHead_of_closed_dropTail (w : VertexSeq α)
    (hclosed : w.closed) (hnodup : w.dropTail.nodup) :
    w.dropHead.nodup := by
  cases w with
  | singleton v =>
      grind [dropHead]
  | cons w v =>
      cases w with
      | singleton u =>
          grind [dropHead, nodup]
      | cons t u =>
          simp [dropTail, nodup] at hnodup ⊢
          constructor
          · exact nodup_dropHead (t :+ u) hnodup
          · intro hv
            exact head_not_mem_dropHead_of_nodup (t :+ u) hnodup (by simp [length])
              (by simpa [closed] using hclosed ▸ hv)

/-- `nodup` is exactly `Nodup` of the underlying list. -/
lemma nodup_iff_toList_nodup (w : VertexSeq α) :
    w.nodup ↔ w.toList.Nodup := by
  induction w with
  | singleton v =>
      simp [nodup, toList]
  | cons w v ih =>
      constructor
      · intro h
        rw [toList, List.concat_eq_append, List.nodup_append]
        refine ⟨ih.mp h.1, by simp, ?_⟩
        intro a ha b hb hab
        simp at hb
        subst hb
        subst hab
        exact h.2 (by simpa [mem_def] using ha)
      · intro h
        rw [toList, List.concat_eq_append, List.nodup_append] at h
        refine ⟨ih.mpr h.1, ?_⟩
        intro hv
        exact h.2.2 v (by simpa [mem_def] using hv) v (by simp) rfl

end VertexSeq
