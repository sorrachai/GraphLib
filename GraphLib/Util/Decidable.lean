/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Sets

/-!
# Decidability helpers for `Sym2` and `Set`

Small, graph-independent deciders that Mathlib does not provide in the form needed by a
library whose objects are `Set`-valued rather than type-valued. Everything here is
stated in the root namespace, since nothing in it mentions graphs; these are natural
candidates for upstreaming.

## Main results

* `Sym2.decidableForallMem` — `∀ v ∈ e, p v` is decidable for `e : Sym2 α`.
* `Set.decidableSubsetOfFintype` — `s ⊆ t` is decidable when `s` is finite (as data)
  and `t` has decidable membership.
* `Set.decidableSubsingletonOfFintype` — `s.Subsingleton` is decidable for a finite `s`.

## Design choices

* **`[Fintype ↥s]`, not `[Fintype α]`.** Mathlib's deciders for `⊆` and `Subsingleton`
  (`Fintype.decidableSubsingleton`) quantify over a finite *type*. A library in which
  a graph is a `vertexSet : Set α` for an arbitrary `α` never has that, but it does have
  finiteness of the individual sets involved, which is all these proofs need.
* **Decidability, not `Classical`.** Each result is stated so that its `Decidable`
  instance actually evaluates: `Set.toFinset` needs only `[Fintype ↥s]` and computes.
-/

variable {α : Type*}

/-! ## `Sym2` -/

/-- A bounded universal quantifier over the two endpoints of an unordered pair is
decidable. Mathlib provides `Sym2.Mem.decidable` but no decider for `∀ v ∈ e, p v`.

The elimination has to go through `Sym2.recOnSubsingleton`: the goal is `Decidable`-,
hence `Sort`-valued, so the `Prop`-valued recursor `Sym2.ind` does not apply. -/
instance Sym2.decidableForallMem {p : α → Prop} [DecidablePred p] (e : Sym2 α) :
    Decidable (∀ v ∈ e, p v) :=
  Sym2.recOnSubsingleton (motive := fun e => Decidable (∀ v ∈ e, p v)) e
    fun x y => decidable_of_iff (p x ∧ p y) Sym2.forall_mem_pair.symm

/-! ## `Set` -/

/-- Inclusion of a finite `Set` into another, as a bounded quantifier over a `Finset`. -/
lemma Set.subset_iff_forall_mem_toFinset (s t : Set α) [Fintype s] :
    s ⊆ t ↔ ∀ x ∈ s.toFinset, x ∈ t := by
  simp [Set.subset_def]

/-- Inclusion is decidable when the smaller set is finite and the larger one has
decidable membership. -/
instance Set.decidableSubsetOfFintype (s t : Set α) [Fintype s]
    [DecidablePred (· ∈ t)] : Decidable (s ⊆ t) :=
  decidable_of_iff _ (Set.subset_iff_forall_mem_toFinset s t).symm

/-- Being a subsingleton, as a cardinality bound on the `Finset` view. -/
lemma Set.subsingleton_iff_toFinset_card_le_one (s : Set α) [Fintype s] :
    s.Subsingleton ↔ s.toFinset.card ≤ 1 := by
  rw [Finset.card_le_one]
  exact ⟨fun h a ha b hb => h (Set.mem_toFinset.1 ha) (Set.mem_toFinset.1 hb),
    fun h a ha b hb => h a (Set.mem_toFinset.2 ha) b (Set.mem_toFinset.2 hb)⟩

/-- `Set.Subsingleton` is decidable for a set with finite coercion. -/
instance Set.decidableSubsingletonOfFintype (s : Set α) [Fintype s] [DecidableEq α] :
    Decidable s.Subsingleton :=
  decidable_of_iff _ (Set.subsingleton_iff_toFinset_card_le_one s).symm

/-- Membership in the coercion of a `Finset` is decidable. Stated as an instance because
`(↑s : Set α)` and `s` have different head symbols, so instance search does not reach
`Finset.decidableMem` on its own in every position. -/
instance Finset.decidablePredMemCoe [DecidableEq α] (s : Finset α) :
    DecidablePred (· ∈ (↑s : Set α)) :=
  fun a => decidable_of_iff (a ∈ s) Finset.mem_coe.symm
