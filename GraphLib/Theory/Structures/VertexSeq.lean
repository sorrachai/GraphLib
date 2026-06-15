/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import Mathlib.Data.Sym.Sym2

/-!
# Vertex sequences

A `VertexSeq α` is a non-empty inductive sequence of vertices, with a
`singleton` base case and a right-extending `cons`. It is the underlying
carrier for walks, paths and cycles in the graph theory library.

## Main definitions

* `VertexSeq α` — non-empty sequence of vertices.
* `VertexSeq.head`, `VertexSeq.tail` — first and last vertex.
* `VertexSeq.length` — number of *edges* (one less than the vertex count).
* `VertexSeq.toList` — the underlying list of visited vertices.
* `VertexSeq.append`, `VertexSeq.reverse` — concatenation and reversal.
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

/-! ## append, reverse, and their laws -/

/-- Concatenate two sequences. The joining vertices `p.tail` and `q.head` are
*both* preserved. If they are equal the duplicate is intentional (the caller
may drop it with `dropTail`). -/
@[grind] def append : VertexSeq α → VertexSeq α → VertexSeq α
  | w, .singleton v => .cons w v
  | w, .cons u v => .cons (append w u) v

instance : Append (VertexSeq α) := ⟨VertexSeq.append⟩

@[simp] lemma mem_append (v : α) (w1 w2 : VertexSeq α) :
    v ∈ w1 ++ w2 ↔ v ∈ w1 ∨ v ∈ w2 := by
  fun_induction append w1 w2 <;> expose_names
  · constructor
    · intro h
      sorry
    · sorry
  · sorry

/-- Reverse a sequence: the head becomes the tail and vice versa. -/
@[grind] def reverse : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v => append (.singleton v) (reverse w)

@[simp] lemma mem_reverse (v : α) (w : VertexSeq α) :
    v ∈ w ↔ v ∈ w.reverse := by
  fun_induction reverse w <;> sorry

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
  cases p <;> grind

/-! ## prefixUntil, suffixFrom, loopErase -/

/-- The prefix of `w` ending at the first vertex satisfying the predicate `p`,
inclusive of that vertex. The hypothesis guarantees such a vertex exists. -/
@[grind] def prefixUntil [DecidableEq α] (w : VertexSeq α) (v : α)
    (h : v ∈ w) : VertexSeq α :=
  match w with
  | .singleton x => .singleton x
  | .cons w2 x =>
    if h2 : v ∈ w2 then prefixUntil w2 v h2
    else w2 :+ x

/-- The suffix of `w` starting at the first vertex satisfying the predicate
`p`, inclusive of that vertex. The hypothesis guarantees such a vertex
exists. -/
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

/-- todo: polish -/
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

/- # Sub-VertexSeq -/

/- # Map, Foldl, Foldr, Zip, All, Any, nodup, nostall -/

def map {β : Type*} (f : α → β) : VertexSeq α → VertexSeq β
  | .singleton v => singleton (f v)
  | .cons w v => w.map f :+ f v

def foldl {β : Type*} (f : β → α → β) (b : β) : VertexSeq α → β
  | .singleton v => f b v
  | .cons w v => f (w.foldl f b) v

def foldr {β : Type*} (f : α → β → β) (b : β) : VertexSeq α → β
  | .singleton v => f v b
  | .cons w v    => w.foldr f (f v b)

def zip {β : Type*} : VertexSeq α → VertexSeq β → VertexSeq (α × β)
  | .singleton v, .singleton u => .singleton (v, u)
  | .singleton v, .cons _ u    => .singleton (v, u)
  | .cons _ v, .singleton u    => .singleton (v, u)
  | .cons w v, .cons y u       => .cons (w.zip y) (v, u)

def any (p : α → Prop) : VertexSeq α → Prop
  | .singleton v => p v
  | .cons w v    => w.any p ∨ p v

def all (p : α → Prop) : VertexSeq α → Prop
  | .singleton v => p v
  | .cons w v    => w.all p ∧ p v

/-- The sequence has no repeated vertex. -/
def nodup : VertexSeq α → Prop
  | .singleton _ => True
  | .cons w v    => w.nodup ∧ v ∉ w

/-- The sequence never stalls: no two consecutive vertices are equal. -/
def nonstalling : VertexSeq α → Prop
  | .singleton _ => True
  | .cons w v    => w.nonstalling ∧ w.tail ≠ v

/-- A vertex sequence is *closed* when its first and last vertex coincide. -/
def closed (w : VertexSeq α) : Prop := w.head = w.tail

@[grind] lemma nodup_nonstalling [DecidableEq α] (w : VertexSeq α) :
    w.nodup → w.nonstalling := by
  sorry

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

/-! ## Indexing and insertion -/

instance : GetElem (VertexSeq α) ℕ α (fun w i ↦ i < w.toList.length) where
  getElem w i h := w.toList[i]

/-- Insert the vertex `v` at index `i`, shifting later vertices one position
to the right. If `i` exceeds `w.toList.length`, `v` is appended at the end. -/
@[grind] def insert : VertexSeq α → ℕ → α → VertexSeq α
  | .singleton x, 0, v => .cons (.singleton v) x
  | .singleton x, _ + 1, v => .cons (.singleton x) v
  | .cons q x, i, v =>
    if i ≤ q.length then .cons (insert q i v) x
    else if i = q.length + 1 then .cons (q :+ v) x
    else .cons (q :+ x) v

/- # Structural Manipulations -/


/-- Remove immediate stalls (consecutive duplicate vertices). The result
satisfies `nonstalling`. -/
@[grind] def loopErase [DecidableEq α] : VertexSeq α → VertexSeq α
  | .singleton v => .singleton v
  | .cons w v =>
      if w.tail = v then loopErase w
      else .cons (loopErase w) v

@[grind] lemma loopErase_nonstalling [DecidableEq α] (w : VertexSeq α) :
    w.loopErase.nonstalling := by
  sorry

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

@[grind] lemma cycleErase_nodup [DecidableEq α] (w : VertexSeq α) :
    w.cycleErase.nodup := by
  sorry

/-! ## Functor instance -/

instance : Functor VertexSeq where map := VertexSeq.map

@[simp] lemma map_id (w : VertexSeq α) : w.map id = w := by
  induction w with
  | singleton _ => rfl
  | cons w v ih => simp [map, ih]

lemma map_comp {β γ : Type*} (f : α → β) (g : β → γ) (w : VertexSeq α) :
    w.map (g ∘ f) = (w.map f).map g := by
  induction w with
  | singleton _ => rfl
  | cons w v ih => simp [map, ih]

instance : LawfulFunctor VertexSeq where
  map_const := rfl
  id_map := map_id
  comp_map f g w := map_comp f g w

end VertexSeq
