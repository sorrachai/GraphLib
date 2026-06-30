/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Append

/-!
# Vertex sequences: subsequence operations

Operations that carve a contiguous piece out of a vertex sequence, together
with their head/tail/length/subset laws and the preservation of `nodup` and
`nonstalling`.

## Main definitions

* `VertexSeq.prefixUntil`, `VertexSeq.suffixFrom` — the prefix/suffix cut at a
  chosen vertex.
* `VertexSeq.takeWhile`, `VertexSeq.dropWhile` — the prefix/suffix cut at the
  first vertex failing a predicate.
* `VertexSeq.splitAt` — split into pieces at every occurrence of a vertex.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## prefixUntil, suffixFrom -/

/-- The prefix of `w` ending at the first occurrence of the vertex `v`,
inclusive of that vertex. The hypothesis guarantees such a vertex exists. -/
@[grind] def prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2 then prefixUntil w2 v h2
    else w2 :+ x

/-- The suffix of `w` starting at the first occurrence of the vertex `v`,
inclusive of that vertex. The hypothesis guarantees such a vertex exists. -/
@[grind] def suffixFrom [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2 then .cons (suffixFrom w2 v h2) x
    else .singleton x

@[simp] lemma length_prefixUntil_le [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).length ≤ w.length := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma length_suffixFrom_le [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).length ≤ w.length := by
  fun_induction suffixFrom w v h <;> grind

@[simp] lemma head_prefixUntil [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).head = w.head := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma tail_prefixUntil [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h).tail = v := by
  fun_induction prefixUntil w v h <;> grind

@[simp] lemma prefixUntil_subset [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.prefixUntil v h) ⊆ w := by
  fun_induction prefixUntil <;> grind

@[simp] lemma head_suffixFrom [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).head = v := by
  fun_induction suffixFrom w v h <;> grind

@[simp] lemma tail_suffixFrom [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h).tail = w.tail := by
  fun_induction suffixFrom w v h <;> grind

/-- A `suffixFrom` result is contained in the original sequence. -/
@[simp] lemma suffixFrom_subset [DecidableEq α] (w : VertexSeq α)
    (v : α) (h : v ∈ w) : (w.suffixFrom v h) ⊆ w := by
  fun_induction suffixFrom w v h
  · grind
  · expose_names
    intro u hu
    apply (mem_cons u x (w2.suffixFrom v h_1)).1 at hu
    cases hu
    · expose_names
      grind
    · grind
  grind

/-! ## takeWhile, dropWhile -/

/-- Take every vertex of `w` satisfying `p`, plus the first failure (if any).
If every vertex satisfies `p`, the whole sequence is returned. -/
@[grind] def takeWhile (w : VertexSeq α) (p : α → Prop) [DecidablePred p] :
    VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons q x =>
    if ∃ v ∈ q.toList, ¬ p v then takeWhile q p
    else q :+ x

/-- Drop the longest prefix of `w` on which `p` holds; the result starts at
the first failure. The hypothesis ensures a failure exists. -/
@[grind] def dropWhile (w : VertexSeq α) (p : α → Prop) [DecidablePred p]
    (h : ∃ v ∈ w.toList, ¬ p v) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons q x =>
    if hq : ∃ v ∈ q.toList, ¬ p v then (dropWhile q p hq) :+ x
    else .singleton x

/-- `dropWhile` returns a suffix ending at the original tail, so it preserves
the tail. -/
@[simp, grind =] lemma tail_dropWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) :
    (w.dropWhile p h).tail = w.tail := by
  fun_induction dropWhile w p h <;> grind

/-! ## splitAt -/

/-- Split `w` into a list of pieces at every occurrence of the vertex `v`.
The split point `v` is *duplicated*: it appears as the tail of one piece and
the head of the next, so that re-concatenating the pieces recovers `w`. -/
@[grind] def splitAt [DecidableEq α] : VertexSeq α → α → List (VertexSeq α)
  | .singleton x, _ => [.singleton x]
  | .cons q x, v =>
    if x = v then appendToLast (splitAt q v) v ++ [.singleton v]
    else appendToLast (splitAt q v) x
where
  appendToLast : List (VertexSeq α) → α → List (VertexSeq α)
    | [], _ => []
    | [w], x => [w :+ x]
    | p :: ps, x => p :: appendToLast ps x

/-! ## Nodup preservation -/

/-- A `prefixUntil` of a `nodup` sequence is `nodup`. -/
@[grind] lemma nodup_prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nodup) : (w.prefixUntil v h).nodup := by
  fun_induction prefixUntil w v h <;> grind

/-- A `suffixFrom` of a `nodup` sequence is `nodup`. -/
@[grind] lemma nodup_suffixFrom [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nodup) : (w.suffixFrom v h).nodup := by
  fun_induction suffixFrom w v h <;> grind [suffixFrom_subset]

/-- `takeWhile` preserves `nodup`. -/
@[grind] lemma nodup_takeWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (hw : w.nodup) : (w.takeWhile p).nodup := by
  fun_induction takeWhile w p <;> grind

/-- A `dropWhile` result is a suffix of the original sequence. -/
@[grind] lemma dropWhile_subset (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) : (w.dropWhile p h) ⊆ w := by
  intro y hy
  fun_induction dropWhile w p h <;> grind

/-- `dropWhile` preserves `nodup`. -/
@[grind] lemma nodup_dropWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) (hw : w.nodup) :
    (w.dropWhile p h).nodup := by
  fun_induction dropWhile w p h <;> grind [dropWhile_subset]

/-- If every piece of `L` is contained in `w`, then every piece of
`appendToLast L x` is contained in `w :+ x`. -/
@[grind] lemma appendToLast_subset (L : List (VertexSeq α)) (x : α)
    (w : VertexSeq α) (hL : ∀ p ∈ L, p ⊆ w) :
    ∀ p ∈ splitAt.appendToLast L x, p ⊆ w :+ x := by
  induction L with
  | nil =>
      grind [splitAt.appendToLast]
  | cons p ps ih =>
      cases ps with
      | nil =>
          intro r hr y hy
          have hr' : r = p :+ x := by
            simpa [splitAt.appendToLast] using hr
          subst r
          rcases (mem_cons y x p).1 hy with hyp | rfl
          · exact (mem_cons y x w).2 (Or.inl (hL p (by simp) y hyp))
          · exact (mem_cons y y w).2 (Or.inr rfl)
      | cons q qs =>
          intro r hr y hy
          have hr' : r = p ∨ r ∈ splitAt.appendToLast (q :: qs) x := by
            simpa [splitAt.appendToLast] using hr
          rcases hr' with rfl | hr'
          · exact (mem_cons y x w).2 (Or.inl (hL r (by simp) y hy))
          · have htail : ∀ s ∈ q :: qs, s ⊆ w := by
              intro s hs
              exact hL s (by simp [hs])
            exact ih htail r hr' y hy

/-- Every piece produced by `splitAt` is contained in the original sequence. -/
@[grind] lemma splitAt_subset [DecidableEq α] (w : VertexSeq α) (v : α) :
    ∀ p ∈ w.splitAt v, p ⊆ w := by
  fun_induction splitAt w v <;> grind [appendToLast_subset]

/-- If every piece of `L` is nodup and avoids `x`, then `appendToLast L x`
has only nodup pieces. -/
@[grind] lemma nodup_appendToLast (L : List (VertexSeq α)) (x : α)
    (hL : ∀ p ∈ L, p.nodup) (havoid : ∀ p ∈ L, x ∉ p) :
    ∀ p ∈ splitAt.appendToLast L x, p.nodup := by
  induction L with
  | nil =>
      grind [splitAt.appendToLast]
  | cons p ps ih =>
      cases ps with
      | nil =>
          intro r hr
          have hr' : r = p :+ x := by
            simpa [splitAt.appendToLast] using hr
          subst r
          exact ⟨hL p (by simp), havoid p (by simp)⟩
      | cons q qs =>
          intro r hr
          have hr' : r = p ∨ r ∈ splitAt.appendToLast (q :: qs) x := by
            simpa [splitAt.appendToLast] using hr
          rcases hr' with rfl | hr'
          · exact hL r (by simp)
          · have htail : ∀ s ∈ q :: qs, s.nodup := by
              intro s hs
              exact hL s (by simp [hs])
            have havoid' : ∀ s ∈ q :: qs, x ∉ s := by
              intro s hs
              exact havoid s (by simp [hs])
            exact ih htail havoid' r hr'

/-- Each piece of a `splitAt` of a `nodup` sequence is `nodup`. -/
@[grind] lemma nodup_splitAt [DecidableEq α] (w : VertexSeq α)
    (hw : w.nodup) (v : α) : ∀ p ∈ w.splitAt v, p.nodup := by
  induction w with
  | singleton x =>
      intro p hp
      have hp' : p = VertexSeq.singleton x := by
        simpa [splitAt] using hp
      subst p
      grind
  | cons q x ih =>
      intro p hp
      simp [nodup] at hw
      by_cases hx : x = v
      · have hp' : p ∈ splitAt.appendToLast (q.splitAt v) v ∨
            p ∈ [VertexSeq.singleton v] := by
          simpa [splitAt, hx] using hp
        rcases hp' with hp_append | hp_single
        · exact nodup_appendToLast (q.splitAt v) v (ih hw.1)
            (fun s hs hsv => hw.2 (by
              rw [hx]
              exact splitAt_subset q v s hs v hsv)) p hp_append
        · have hp_eq : p = VertexSeq.singleton v := by
            simpa using hp_single
          subst p
          grind
      · exact nodup_appendToLast (q.splitAt v) x (ih hw.1)
          (fun s hs hsx => hw.2 (splitAt_subset q v s hs x hsx)) p
          (by simpa [splitAt, hx] using hp)

/-! ## Non-stalling preservation -/

/-- A `prefixUntil` of a non-stalling sequence is non-stalling. -/
@[grind] lemma nonstalling_prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nonstalling) : (w.prefixUntil v h).nonstalling := by
  fun_induction prefixUntil w v h <;> grind

/-- A `suffixFrom` of a non-stalling sequence is non-stalling. -/
@[grind] lemma nonstalling_suffixFrom [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) (hw : w.nonstalling) : (w.suffixFrom v h).nonstalling := by
  fun_induction suffixFrom w v h <;> grind

/-- `takeWhile` preserves non-stalling. -/
@[grind] lemma nonstalling_takeWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (hw : w.nonstalling) : (w.takeWhile p).nonstalling := by
  fun_induction takeWhile w p <;> grind

/-- `dropWhile` preserves non-stalling. -/
@[grind] lemma nonstalling_dropWhile (w : VertexSeq α) (p : α → Prop)
    [DecidablePred p] (h : ∃ v ∈ w.toList, ¬ p v) (hw : w.nonstalling) :
    (w.dropWhile p h).nonstalling := by
  fun_induction dropWhile w p h <;> grind

/-- `appendToLast` extends the final piece, so the last piece becomes the old
last piece with `x` appended. -/
@[simp, grind =] lemma getLast?_appendToLast (L : List (VertexSeq α)) (x : α) :
    (splitAt.appendToLast L x).getLast? = (L.getLast?).map (· :+ x) := by
  fun_induction splitAt.appendToLast L x <;> grind

/-- If every piece of `L` is non-stalling and the final piece does not end at
`x`, then every piece of `appendToLast L x` is non-stalling. -/
@[grind] lemma nonstalling_appendToLast (L : List (VertexSeq α)) (x : α)
    (hL : ∀ p ∈ L, p.nonstalling) (hlast : ∀ p ∈ L.getLast?, p.tail ≠ x) :
    ∀ p ∈ splitAt.appendToLast L x, p.nonstalling := by
  fun_induction splitAt.appendToLast L x <;> grind

/-- Every piece produced by `splitAt` ends at the original tail. -/
@[grind] lemma tail_getLast?_splitAt [DecidableEq α] (w : VertexSeq α) (v : α) :
    ∀ p ∈ (w.splitAt v).getLast?, p.tail = w.tail := by
  fun_induction splitAt w v <;> grind

/-- Each piece of a `splitAt` of a non-stalling sequence is non-stalling. -/
@[grind] lemma nonstalling_splitAt [DecidableEq α] (w : VertexSeq α)
    (hw : w.nonstalling) (v : α) : ∀ p ∈ w.splitAt v, p.nonstalling := by
  fun_induction splitAt w v <;> grind

/-! ## Reassembling a sequence from its cut at a vertex -/

/-- Cutting at an interior vertex `v` and re-gluing the prefix (with its
duplicated `v` dropped) to the suffix recovers the original sequence. -/
@[simp, grind →] lemma dropTail_prefixUntil_append_suffixFrom [DecidableEq α]
    (w : VertexSeq α) (v : α) (h : v ∈ w) (hne : v ≠ w.head) :
    (w.prefixUntil v h).dropTail.append (w.suffixFrom v h) = w := by
  induction w generalizing v with
  | singleton x =>
      exact (hne (by grind)).elim
  | cons w x ih =>
      by_cases hmem : v ∈ w
      · simp [prefixUntil, suffixFrom, hmem]
        by_cases hvhead : v = w.head
        · subst hvhead
          grind
        · exact congrArg (fun q => q :+ x) (ih v hmem hvhead)
      · have hvx : v = x := by
          have hv : v ∈ w ∨ v = x := (mem_cons v x w).1 h
          exact hv.elim (fun hw => (hmem hw).elim) id
        subst hvx
        simp [prefixUntil, suffixFrom, hmem, append, dropTail]

end VertexSeq
