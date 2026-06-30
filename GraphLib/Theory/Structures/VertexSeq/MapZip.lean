/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Predicates

/-!
# Vertex sequences: map, fold, zip

The higher-order traversals over a vertex sequence and the `Functor` instance,
together with the membership and `nodup`/`nonstalling` lemmas they need.

## Main definitions

* `VertexSeq.map`, `VertexSeq.foldl`, `VertexSeq.foldr` — the standard
  traversals.
* `VertexSeq.zip` — pointwise pairing of two sequences.
* `VertexSeq.any`, `VertexSeq.all` — existential/universal predicates.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## map, foldl, foldr, zip, any, all -/

@[grind] def map {β : Type*} (f : α → β) : VertexSeq α → VertexSeq β
  | .singleton v => singleton (f v)
  | .cons w v => w.map f :+ f v

@[simp, grind =] lemma toList_map {β : Type*} (f : α → β) (w : VertexSeq α) :
    (w.map f).toList = w.toList.map f := by
  induction w with
  | singleton v => rfl
  | cons w v ih =>
      simp [map, toList, ih, List.concat_eq_append]

@[simp, grind =] lemma head_map {β : Type*} (f : α → β) (w : VertexSeq α) :
    (w.map f).head = f w.head := by
  induction w with
  | singleton v => rfl
  | cons w v ih => exact ih

@[simp, grind =] lemma tail_map {β : Type*} (f : α → β) (w : VertexSeq α) :
    (w.map f).tail = f w.tail := by
  induction w <;> rfl

@[simp, grind =] lemma length_map {β : Type*} (f : α → β) (w : VertexSeq α) :
    (w.map f).length = w.length := by
  induction w with
  | singleton v => rfl
  | cons w v ih => simp [map, length, ih]

@[grind] def foldl {β : Type*} (f : β → α → β) (b : β) : VertexSeq α → β
  | .singleton v => f b v
  | .cons w v => f (w.foldl f b) v

@[grind] def foldr {β : Type*} (f : α → β → β) (b : β) : VertexSeq α → β
  | .singleton v => f v b
  | .cons w v    => w.foldr f (f v b)

@[grind] def zip {β : Type*} : VertexSeq α → VertexSeq β → VertexSeq (α × β)
  | .singleton v, .singleton u => .singleton (v, u)
  | .singleton v, .cons _ u    => .singleton (v, u)
  | .cons _ v, .singleton u    => .singleton (v, u)
  | .cons w v, .cons y u       => .cons (w.zip y) (v, u)

/-- The tail of a `zip` is the pair of tails. -/
@[simp, grind =] lemma tail_zip {β : Type*} (w : VertexSeq α) (w' : VertexSeq β) :
    (w.zip w').tail = (w.tail, w'.tail) := by
  fun_induction zip w w' <;> grind

@[grind] def any (p : α → Prop) : VertexSeq α → Prop
  | .singleton v => p v
  | .cons w v    => w.any p ∨ p v

@[grind] def all (p : α → Prop) : VertexSeq α → Prop
  | .singleton v => p v
  | .cons w v    => w.all p ∧ p v

/-! ## Membership and preservation -/

/-- Membership in a mapped sequence is membership in the original sequence
through the mapping function. -/
@[grind] lemma mem_map {β : Type*} (f : α → β) (w : VertexSeq α) (b : β) :
    b ∈ w.map f ↔ ∃ a : α, a ∈ w ∧ f a = b := by
  induction w <;> grind

/-- Mapping through an injective function preserves `nodup`. -/
@[grind] lemma nodup_map {β : Type*} (f : α → β) (hf : Function.Injective f)
    (w : VertexSeq α) (h : w.nodup) : (w.map f).nodup := by
  induction w <;> grind

/-- Membership in a zip projects to membership in the left operand. -/
@[grind] lemma fst_mem_of_mem_zip {β : Type*} (w : VertexSeq α) (w' : VertexSeq β)
    {x : α × β} (h : x ∈ w.zip w') : x.1 ∈ w := by
  fun_induction zip w w' <;> grind

/-- Zipping with a `nodup` left operand yields a `nodup` sequence of pairs. -/
@[grind] lemma nodup_zip {β : Type*} (w : VertexSeq α) (w' : VertexSeq β)
    (hw : w.nodup) : (w.zip w').nodup := by
  fun_induction zip w w' with
  | case1 => grind
  | case2 => grind
  | case3 => grind
  | case4 w v y u ih =>
      simp [nodup] at hw ⊢
      exact ⟨ih hw.1, fun hmem => hw.2 (fst_mem_of_mem_zip w y hmem)⟩

/-- Zipping with a non-stalling left operand yields a non-stalling sequence
(the first components of consecutive pairs already differ). -/
@[grind] lemma nonstalling_zip {β : Type*} (w : VertexSeq α) (w' : VertexSeq β)
    (hw : w.nonstalling) : (w.zip w').nonstalling := by
  fun_induction zip w w' <;> grind

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
