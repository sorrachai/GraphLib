/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Closure
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Union

/-!
# Dilworth's and Mirsky's Theorems

This file proves Dilworth's theorem and its dual, Mirsky's theorem, for finite subsets of a
partially ordered set, together with the general order-theoretic lemmas the proofs rest on.

## Main declarations

General:

* `IsAntichain.upperClosure_inter_lowerClosure`: an antichain is exactly the intersection of its
  upper and lower closures.
* `IsMaxAntichain.upperClosure_union_lowerClosure`: the upper and lower closures of a maximal
  antichain cover the whole order.
* `exists_injOn_mem_of_inter_subsingleton`: the choice core shared by both weak dualities. Given a
  cover `C` of `A` such that `A` meets each member of `C` in at most one point, there is an
  injection-on-`A` selecting for each `a ∈ A` a member of `C` containing it.
* `IsAntichain.exists_injOn_mem_chains` / `IsChain.exists_injOn_mem_antichains`: weak duality in
  injection form. An antichain injects into any chain cover of it, and dually.

Finite (cardinality) statements:

* `antichain_le_chain_cover` / `chain_le_antichain_cover`: weak duality for `Finset` cardinalities.
* `IsAntichain.exists_bijOn_chains_le` / `IsAntichain.exists_bijOn_chains_ge`: the one-sided
  covering lemma. If at most `|A|` chains cover a set lying below (resp. above) the antichain `A`,
  the weak-duality injection is a bijection and each `a ∈ A` is the greatest (resp. least) element
  of its chain.
* `dilworth`: **Dilworth's theorem**, strong duality: some antichain and some chain cover have
  equal size. With `antichain_le_chain_cover` this is the min-max equality.
* `mirsky`: **Mirsky's theorem**, the order dual, for antichain covers and chains.

## Implementation notes

The min-max content is split, as for Hall's marriage theorem, into a weak-duality inequality and a
strong-duality existence statement; the pair `(t, C)` produced by `dilworth` is automatically a
maximum antichain and a minimum chain cover by weak duality, so no extremal quantities
(`Finset.min'`/`Finset.max'` over families of sets) are ever defined.

Three structural choices keep the proofs short:

* Covers are `Finset (Finset α)` in the theorem statements (the classical reading of "number of
  chains"), but all intermediate lemmas speak about *functions* `f : α → Finset α` that are
  injective/bijective on the antichain with `a ∈ f a` — distinctness of the produced chains is then
  a consequence of the antichain property rather than a side condition to bookkeep.
* Everything happens inside one ambient `[PartialOrder α]`; sub-posets are plain `Finset`s and
  never subtypes, so the induction (`Finset.strongInduction` along `⊂`) needs no coercions.
* The proof of `dilworth` is the classical induction: pick a maximum-cardinality antichain `A`;
  if some maximum antichain has both strict lower and strict upper closure inside `s`, recurse on
  the two closures and glue the resulting chain covers through `A` using the one-sided covering
  lemma; otherwise remove the two-element chain `{x, y}` (a maximal element over a minimal one),
  which strictly decreases the maximum antichain size, and recurse.

## Tags

poset, dilworth, mirsky, chain, antichain, upper closure, lower closure

Hi everyone,

This file formalizes Dilworth's and Mirsky's theorems. For Dilworth I use Galvin's induction (via
the one-sided covering lemma `chainCover_glue`), which keeps the argument self-contained and avoids
the boilerplate of routing through bipartite matching / Kőnig's theorem.

A few structural choices I want to flag up front. I am happy to revisit any of them if there is a
more idiomatic approach, but here is my current reasoning:

1. **Mirsky is not proved as the formal dual of Dilworth.** One could ask for the two proofs to
share a single mechanism or to be derived from each other via `OrderDual`. I deliberately did not
do this: the theorems are dual in *statement* but not in *difficulty*. Dilworth needs the Galvin
bottleneck, whereas Mirsky has a genuinely simpler proof (peel off the minimal elements, one
antichain per layer). Forcing Mirsky through Dilworth's machinery would make it longer, not shorter.
The two proofs already share their foundations (the closure lemmas and weak duality in injection
form), so what differs is only the induction, and I think keeping each proof on its natural
induction is the right call. Happy to be convinced otherwise.

2. **`[DecidableEq α]` on the main theorems.** This is forced by the statement, not just for
convenience: the cover condition `s = C.biUnion id` needs `DecidableEq α` for `Finset.biUnion`. It
can be avoided by stating coverage membership-wise instead, but that reads less cleanly. I kept the
`biUnion` form since `[DecidableEq α]` is standard for `Finset` results; I'm happy to switch to the
membership form if reviewers prefer a typeclass-free public API.

3. **Extremal extraction & covers.** I grab the maximum antichain with
`exists_max_image Finset.card` (with the empty antichain as the nonempty witness). Covers are
`Finset (Finset α)` in the public statements (the classical reading of "number of chains"), but the
intermediate lemmas work with functions `α → Finset α` that are injective/bijective on the
antichain (`Set.InjOn` / `Set.BijOn`), so distinctness of the produced chains falls out of the
property instead of being tracked by hand. If there is a more idiomatic pattern for this in the
current `Finset` API, I'm all ears.

Looking forward to your feedback!
-/

open Finset

variable {α : Type*}

/-! ### Closures of antichains -/

/-- An antichain is the intersection of its upper and lower closures. -/
theorem IsAntichain.upperClosure_inter_lowerClosure [PartialOrder α] {A : Set α}
    (hA : IsAntichain (· ≤ ·) A) :
    (upperClosure A : Set α) ∩ (lowerClosure A : Set α) = A := by
  refine Set.Subset.antisymm (fun p hp => ?_)
    (fun p hp => ⟨subset_upperClosure hp, subset_lowerClosure hp⟩)
  obtain ⟨e₁, he₁, h₁⟩ := mem_upperClosure.mp (SetLike.mem_coe.mp hp.1)
  obtain ⟨e₂, he₂, h₂⟩ := mem_lowerClosure.mp (SetLike.mem_coe.mp hp.2)
  obtain rfl : e₁ = e₂ := hA.eq he₁ he₂ (h₁.trans h₂)
  have : p = e₁ := le_antisymm h₂ h₁
  rwa [this]

/-- The upper and lower closures of a maximal antichain cover the whole order. -/
theorem IsMaxAntichain.upperClosure_union_lowerClosure [Preorder α] {A : Set α}
    (hA : IsMaxAntichain (· ≤ ·) A) :
    (upperClosure A : Set α) ∪ (lowerClosure A : Set α) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  by_contra hp
  rw [Set.mem_union, not_or] at hp
  have h₁ : ∀ a ∈ A, ¬a ≤ p := fun a ha hle =>
    hp.1 (SetLike.mem_coe.mpr (mem_upperClosure.mpr ⟨a, ha, hle⟩))
  have h₂ : ∀ a ∈ A, ¬p ≤ a := fun a ha hle =>
    hp.2 (SetLike.mem_coe.mpr (mem_lowerClosure.mpr ⟨a, ha, hle⟩))
  have hpA : p ∉ A := fun h => h₁ p h le_rfl
  have hins : IsAntichain (· ≤ ·) (insert p A) :=
    hA.isAntichain.insert (fun b hb _ => h₁ b hb) (fun b hb _ => h₂ b hb)
  have : p ∈ A := by
    rw [hA.2 hins (Set.subset_insert p A)]
    exact Set.mem_insert p A
  exact hpA this

/-! ### Weak duality, injection form

These hold for an arbitrary relation, an arbitrary index type, and arbitrary (possibly infinite)
sets: no order axioms and no finiteness enter. The shared core is that a family of sets each meeting
`A` in at most one point admits an injective choice of index on `A`. The cardinality bounds further
down are the specialization to `ι := Finset α`, `c := (↑·)`. -/

/-- **Injective transversal.** If the blocks `c i` for `i ∈ C` cover `A` and each meets `A` in at
most one point, then for each `a ∈ A` one can choose an index `f a ∈ C` with `a ∈ c (f a)`,
injectively in `a`. -/
lemma exists_injOn_mem_of_inter_subsingleton {ι : Type*} [Nonempty ι] {A : Set α}
    {c : ι → Set α} {C : Set ι} (hcover : ∀ a ∈ A, ∃ i ∈ C, a ∈ c i)
    (hinter : ∀ i ∈ C, (A ∩ c i).Subsingleton) :
    ∃ f : α → ι, Set.MapsTo f A C ∧ Set.InjOn f A ∧ ∀ a ∈ A, a ∈ c (f a) := by
  choose! f hfC hfmem using hcover
  exact ⟨f, fun a ha => hfC a ha,
    fun a ha b hb hfab => hinter (f a) (hfC a ha) ⟨ha, hfmem a ha⟩ ⟨hb, hfab ▸ hfmem b hb⟩, hfmem⟩

/-- **Weak duality for chains, injective form:** an antichain `A` injects into any cover of it by
chains, each `a ∈ A` landing in a chain containing it. -/
theorem IsAntichain.exists_injOn_mem_chains {r : α → α → Prop} {ι : Type*} [Nonempty ι] {A : Set α}
    {c : ι → Set α} {C : Set ι} (hA : IsAntichain r A) (hcover : ∀ a ∈ A, ∃ i ∈ C, a ∈ c i)
    (hchains : ∀ i ∈ C, IsChain r (c i)) :
    ∃ f : α → ι, Set.MapsTo f A C ∧ Set.InjOn f A ∧ ∀ a ∈ A, a ∈ c (f a) :=
  exists_injOn_mem_of_inter_subsingleton hcover fun i hi =>
    subsingleton_of_isChain_of_isAntichain
      (IsChain.mono Set.inter_subset_right (hchains i hi)) (hA.subset Set.inter_subset_left)

/-- **Weak duality for antichains, injective form:** a chain `A` injects into any cover of it by
antichains, each `a ∈ A` landing in an antichain containing it. -/
theorem IsChain.exists_injOn_mem_antichains {r : α → α → Prop} {ι : Type*} [Nonempty ι] {A : Set α}
    {c : ι → Set α} {C : Set ι} (hA : IsChain r A) (hcover : ∀ a ∈ A, ∃ i ∈ C, a ∈ c i)
    (hantis : ∀ i ∈ C, IsAntichain r (c i)) :
    ∃ f : α → ι, Set.MapsTo f A C ∧ Set.InjOn f A ∧ ∀ a ∈ A, a ∈ c (f a) :=
  exists_injOn_mem_of_inter_subsingleton hcover fun i hi =>
    subsingleton_of_isChain_of_isAntichain
      (IsChain.mono Set.inter_subset_left hA) ((hantis i hi).subset Set.inter_subset_right)

/-! ### Weak duality, cardinality form

The classical `Finset` statements, obtained by specializing the injective form to the family
`(↑· : Finset α → Set α)`: an injection of `↑t` into `↑C` is exactly `t.card ≤ C.card`. -/

/-- **Weak duality (Dilworth):** the size of any antichain in `s` is bounded by the size of any
chain cover of `s`. Stated for an arbitrary relation `r`; no order axioms are needed. -/
lemma antichain_le_chain_cover {r : α → α → Prop} [DecidableEq α] {s t : Finset α}
    {C : Finset (Finset α)} (ht_sub : t ⊆ s) (h_anti : IsAntichain r (t : Set α))
    (hC_cover : s ⊆ C.biUnion id) (hC_chains : ∀ c ∈ C, IsChain r (c : Set α)) :
    t.card ≤ C.card := by
  obtain ⟨f, hmaps, hinj, -⟩ := h_anti.exists_injOn_mem_chains (ι := Finset α)
    (c := fun i : Finset α => (i : Set α)) (C := (C : Set (Finset α)))
    (fun a ha => by
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (hC_cover (ht_sub (Finset.mem_coe.mp ha)))
      exact ⟨i, Finset.mem_coe.mpr hi, Finset.mem_coe.mpr hai⟩)
    fun i hi => hC_chains i (Finset.mem_coe.mp hi)
  exact Finset.card_le_card_of_injOn f hmaps hinj

/-- **Weak duality (Mirsky):** the size of any chain in `s` is bounded by the size of any antichain
cover of `s`. Stated for an arbitrary relation `r`; no order axioms are needed. -/
lemma chain_le_antichain_cover {r : α → α → Prop} [DecidableEq α] {s t : Finset α}
    {C : Finset (Finset α)} (ht_sub : t ⊆ s) (h_chain : IsChain r (t : Set α))
    (hC_cover : s ⊆ C.biUnion id) (hC_antis : ∀ c ∈ C, IsAntichain r (c : Set α)) :
    t.card ≤ C.card := by
  obtain ⟨f, hmaps, hinj, -⟩ := h_chain.exists_injOn_mem_antichains (ι := Finset α)
    (c := fun i : Finset α => (i : Set α)) (C := (C : Set (Finset α)))
    (fun a ha => by
      obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (hC_cover (ht_sub (Finset.mem_coe.mp ha)))
      exact ⟨i, Finset.mem_coe.mpr hi, Finset.mem_coe.mpr hai⟩)
    fun i hi => hC_antis i (Finset.mem_coe.mp hi)
  exact Finset.card_le_card_of_injOn f hmaps hinj

/-! ### The one-sided covering lemma -/

/-- The weak-duality injection of an antichain into a chain cover of equal size is a bijection: each
chain meets `A` in at most one point (so the choice is injective) and `C.card ≤ A.card` upgrades it
to a surjection. The extremality of each `a` in its chain is added in the two corollaries below. -/
theorem IsAntichain.exists_bijOn_chains [PartialOrder α] {A : Finset α} {C : Finset (Finset α)}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c)
    (hchains : ∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) (hcard : C.card ≤ A.card) :
    ∃ f : α → Finset α, Set.BijOn f (A : Set α) (C : Set (Finset α)) ∧ ∀ a ∈ A, a ∈ f a := by
  choose! f hfC hfmem using hcover
  have hmaps : Set.MapsTo f (A : Set α) (C : Set (Finset α)) := fun a ha =>
    Finset.mem_coe.mpr (hfC a (Finset.mem_coe.mp ha))
  have hinj : Set.InjOn f (A : Set α) := by
    intro a ha b hb hfab
    rw [Finset.mem_coe] at ha hb
    by_contra hne
    have hbfa : b ∈ f a := hfab ▸ hfmem b hb
    rcases hchains (f a) (hfC a ha) (Finset.mem_coe.mpr (hfmem a ha))
      (Finset.mem_coe.mpr hbfa) hne with h | h
    · exact hne (hA.eq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)
    · exact hne (hA.eq' (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)
  exact ⟨f, ⟨hmaps, hinj, Finset.surjOn_of_injOn_of_card_le f hmaps hinj hcard⟩, hfmem⟩

/-- **One-sided covering, lower version:** if at most `|A|` chains cover a set of elements each
lying below the antichain `A`, then the chains biject with `A`, each `a ∈ A` being the greatest
element of its chain. -/
theorem IsAntichain.exists_bijOn_chains_le [PartialOrder α] {A : Finset α} {C : Finset (Finset α)}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c)
    (hchains : ∀ c ∈ C, IsChain (· ≤ ·) (c : Set α))
    (hbelow : ∀ c ∈ C, ∀ x ∈ c, ∃ a ∈ A, x ≤ a) (hcard : C.card ≤ A.card) :
    ∃ f : α → Finset α, Set.BijOn f (A : Set α) (C : Set (Finset α)) ∧
      ∀ a ∈ A, a ∈ f a ∧ ∀ x ∈ f a, x ≤ a := by
  obtain ⟨f, hbij, hfmem⟩ := hA.exists_bijOn_chains hcover hchains hcard
  refine ⟨f, hbij, fun a ha => ⟨hfmem a ha, fun x hx => ?_⟩⟩
  have hfaC : f a ∈ C := Finset.mem_coe.mp (hbij.mapsTo (Finset.mem_coe.mpr ha))
  rcases eq_or_ne x a with rfl | hxa
  · exact le_rfl
  rcases hchains (f a) hfaC (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr (hfmem a ha)) hxa with h | h
  · exact h
  · obtain ⟨a', ha', hxa'⟩ := hbelow (f a) hfaC x hx
    rwa [← hA.eq (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr ha') (h.trans hxa')] at hxa'

/-- **One-sided covering, upper version:** if at most `|A|` chains cover a set of elements each
lying above the antichain `A`, then the chains biject with `A`, each `a ∈ A` being the least element
of its chain. -/
theorem IsAntichain.exists_bijOn_chains_ge [PartialOrder α] {A : Finset α} {C : Finset (Finset α)}
    (hA : IsAntichain (· ≤ ·) (A : Set α)) (hcover : ∀ a ∈ A, ∃ c ∈ C, a ∈ c)
    (hchains : ∀ c ∈ C, IsChain (· ≤ ·) (c : Set α))
    (habove : ∀ c ∈ C, ∀ x ∈ c, ∃ a ∈ A, a ≤ x) (hcard : C.card ≤ A.card) :
    ∃ f : α → Finset α, Set.BijOn f (A : Set α) (C : Set (Finset α)) ∧
      ∀ a ∈ A, a ∈ f a ∧ ∀ x ∈ f a, a ≤ x := by
  obtain ⟨f, hbij, hfmem⟩ := hA.exists_bijOn_chains hcover hchains hcard
  refine ⟨f, hbij, fun a ha => ⟨hfmem a ha, fun x hx => ?_⟩⟩
  have hfaC : f a ∈ C := Finset.mem_coe.mp (hbij.mapsTo (Finset.mem_coe.mpr ha))
  rcases eq_or_ne x a with rfl | hxa
  · exact le_rfl
  rcases hchains (f a) hfaC (Finset.mem_coe.mpr (hfmem a ha)) (Finset.mem_coe.mpr hx)
    (Ne.symm hxa) with h | h
  · exact h
  · obtain ⟨a', ha', ha'x⟩ := habove (f a) hfaC x hx
    rwa [hA.eq (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr ha) (ha'x.trans h)] at ha'x

/-! ### Dilworth's theorem -/

open Classical in
/-- **Gluing step of Dilworth's induction.** Let `B` be an antichain contained in `s` and saturated
in `s` (every element of `s` is comparable to some element of `B`). If the lower closure
`{p ∈ s | ∃ a ∈ B, p ≤ a}` and the upper closure `{p ∈ s | ∃ a ∈ B, a ≤ p}` each admit a chain
cover with exactly `|B|` chains, then so does `s`: each `a ∈ B` is the top of its chain in the lower
cover and the bottom of its chain in the upper cover (one-sided covering), so the two chains glue
along `a` into a single chain, and these glued chains cover `s`. -/
theorem chainCover_glue [PartialOrder α] [DecidableEq α] {s B : Finset α}
    {C₁ C₂ : Finset (Finset α)} (hBsub : B ⊆ s) (hBanti : IsAntichain (· ≤ ·) (B : Set α))
    (hsat : ∀ p ∈ s, ∃ a ∈ B, p ≤ a ∨ a ≤ p)
    (hcov₁ : (s.filter fun p => ∃ a ∈ B, p ≤ a) = C₁.biUnion id)
    (hch₁ : ∀ c ∈ C₁, IsChain (· ≤ ·) (c : Set α)) (hC₁card : C₁.card = B.card)
    (hcov₂ : (s.filter fun p => ∃ a ∈ B, a ≤ p) = C₂.biUnion id)
    (hch₂ : ∀ c ∈ C₂, IsChain (· ≤ ·) (c : Set α)) (hC₂card : C₂.card = B.card) :
    ∃ C : Finset (Finset α), s = C.biUnion id ∧
      (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧ C.card = B.card := by
  set D₁ := s.filter (fun p => ∃ a ∈ B, p ≤ a) with hD₁def
  set D₂ := s.filter (fun p => ∃ a ∈ B, a ≤ p) with hD₂def
  have hBD₁ : B ⊆ D₁ := fun a ha => Finset.mem_filter.mpr ⟨hBsub ha, a, ha, le_rfl⟩
  have hBD₂ : B ⊆ D₂ := fun a ha => Finset.mem_filter.mpr ⟨hBsub ha, a, ha, le_rfl⟩
  obtain ⟨f₁, hf₁bij, hf₁⟩ := hBanti.exists_bijOn_chains_le
    (fun a ha => by have := hBD₁ ha; rw [hcov₁] at this; simpa using this) hch₁
    (fun c hc x hx => by
      have hxD : x ∈ D₁ := by rw [hcov₁]; exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
      exact (Finset.mem_filter.mp hxD).2)
    hC₁card.le
  obtain ⟨f₂, hf₂bij, hf₂⟩ := hBanti.exists_bijOn_chains_ge
    (fun a ha => by have := hBD₂ ha; rw [hcov₂] at this; simpa using this) hch₂
    (fun c hc x hx => by
      have hxD : x ∈ D₂ := by rw [hcov₂]; exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
      exact (Finset.mem_filter.mp hxD).2)
    hC₂card.le
  have hf₁C : ∀ a ∈ B, f₁ a ∈ C₁ := fun a ha =>
    Finset.mem_coe.mp (hf₁bij.mapsTo (Finset.mem_coe.mpr ha))
  have hf₂C : ∀ a ∈ B, f₂ a ∈ C₂ := fun a ha =>
    Finset.mem_coe.mp (hf₂bij.mapsTo (Finset.mem_coe.mpr ha))
  -- through each `a ∈ B` runs one chain of the new cover
  set K : α → Finset α := fun a => f₁ a ∪ f₂ a with hKdef
  have hKchain : ∀ a ∈ B, IsChain (· ≤ ·) (K a : Set α) := by
    intro a haB u hu v hv huv
    rw [Finset.mem_coe, hKdef, Finset.mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hch₁ (f₁ a) (hf₁C a haB) (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
    · exact Or.inl (le_trans ((hf₁ a haB).2 u hu) ((hf₂ a haB).2 v hv))
    · exact Or.inr (le_trans ((hf₁ a haB).2 v hv) ((hf₂ a haB).2 u hu))
    · exact hch₂ (f₂ a) (hf₂C a haB) (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
  have hKmem : ∀ a ∈ B, a ∈ K a := fun a ha => Finset.mem_union_left _ ((hf₁ a ha).1)
  have hKinj : Set.InjOn K (B : Set α) := by
    intro a ha b hb hab
    refine subsingleton_of_isChain_of_isAntichain
      (IsChain.mono Set.inter_subset_right (hKchain a (Finset.mem_coe.mp ha)))
      (hBanti.subset Set.inter_subset_left)
      ⟨ha, Finset.mem_coe.mpr (hKmem a (Finset.mem_coe.mp ha))⟩ ⟨hb, ?_⟩
    rw [hab]
    exact Finset.mem_coe.mpr (hKmem b (Finset.mem_coe.mp hb))
  refine ⟨B.image K, Finset.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_),
    fun c hc => ?_, Finset.card_image_of_injOn hKinj⟩
  · obtain ⟨a, haB, hpa | hap⟩ := hsat p hp
    · have hpD : p ∈ D₁ := Finset.mem_filter.mpr ⟨hp, a, haB, hpa⟩
      rw [hcov₁] at hpD
      obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hpD
      obtain ⟨a', ha'B, rfl⟩ := hf₁bij.surjOn (Finset.mem_coe.mpr hc)
      exact Finset.mem_biUnion.mpr ⟨K a',
        Finset.mem_image_of_mem K (Finset.mem_coe.mp ha'B), Finset.mem_union_left _ hpc⟩
    · have hpD : p ∈ D₂ := Finset.mem_filter.mpr ⟨hp, a, haB, hap⟩
      rw [hcov₂] at hpD
      obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hpD
      obtain ⟨a', ha'B, rfl⟩ := hf₂bij.surjOn (Finset.mem_coe.mpr hc)
      exact Finset.mem_biUnion.mpr ⟨K a',
        Finset.mem_image_of_mem K (Finset.mem_coe.mp ha'B), Finset.mem_union_right _ hpc⟩
  · obtain ⟨c, hcC, hpc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a, haB, rfl⟩ := Finset.mem_image.mp hcC
    rcases Finset.mem_union.mp hpc with h | h
    · have hsub : f₁ a ⊆ D₁ := by
        rw [hcov₁]; exact Finset.subset_biUnion_of_mem id (hf₁C a haB)
      exact Finset.filter_subset _ _ (hsub h)
    · have hsub : f₂ a ⊆ D₂ := by
        rw [hcov₂]; exact Finset.subset_biUnion_of_mem id (hf₂C a haB)
      exact Finset.filter_subset _ _ (hsub h)
  · obtain ⟨a, haB, rfl⟩ := Finset.mem_image.mp hc
    exact hKchain a haB

/-- **Dilworth's theorem (strong duality):** in any finite subset `s` of a partial order, some
antichain and some chain cover have the same size. Together with `antichain_le_chain_cover` this
expresses that the largest antichain and the smallest chain cover have a common size. -/
theorem dilworth [PartialOrder α] [DecidableEq α] (s : Finset α) :
    ∃ (t : Finset α) (C : Finset (Finset α)),
      t ⊆ s ∧ IsAntichain (· ≤ ·) (t : Set α) ∧
      s = C.biUnion id ∧ (∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) ∧
      C.card = t.card := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
  -- a maximum-cardinality antichain `A` of `s`
  obtain ⟨A, hAmem, hAmax⟩ :=
    (s.powerset.filter fun t : Finset α => IsAntichain (· ≤ ·) (t : Set α))
      |>.exists_max_image Finset.card
        ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset s, by
          rw [Finset.coe_empty]; exact IsAntichain.empty⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hAmem
  obtain ⟨hAsub, hAanti⟩ := hAmem
  have hAmax' : ∀ t' : Finset α, t' ⊆ s → IsAntichain (· ≤ ·) (t' : Set α) →
      t'.card ≤ A.card := fun t' h1 h2 =>
    hAmax t' (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h1, h2⟩)
  by_cases hcase : ∃ B, B ⊆ s ∧ IsAntichain (· ≤ ·) (B : Set α) ∧ B.card = A.card ∧
      s.filter (fun p => ∃ a ∈ B, p ≤ a) ≠ s ∧ s.filter (fun p => ∃ a ∈ B, a ≤ p) ≠ s
  · -- a maximum antichain `B` whose lower and upper closures are both proper: recurse on both
    -- closures and glue the two chain covers through `B`.
    obtain ⟨B, hBsub, hBanti, hBcard, hD₁ne, hD₂ne⟩ := hcase
    obtain ⟨t₁, C₁, ht₁sub, ht₁anti, hcov₁, hch₁, _⟩ :=
      ih _ ((Finset.filter_subset _ _).ssubset_of_ne hD₁ne)
    obtain ⟨t₂, C₂, ht₂sub, ht₂anti, hcov₂, hch₂, _⟩ :=
      ih _ ((Finset.filter_subset _ _).ssubset_of_ne hD₂ne)
    have hBD₁ : B ⊆ s.filter (fun p => ∃ a ∈ B, p ≤ a) :=
      fun a ha => Finset.mem_filter.mpr ⟨hBsub ha, a, ha, le_rfl⟩
    have hBD₂ : B ⊆ s.filter (fun p => ∃ a ∈ B, a ≤ p) :=
      fun a ha => Finset.mem_filter.mpr ⟨hBsub ha, a, ha, le_rfl⟩
    -- both covers have exactly `|B|` chains (weak duality, and `B` is a maximum antichain)
    have hC₁card : C₁.card = B.card := by
      have h1 : B.card ≤ C₁.card :=
        antichain_le_chain_cover hBD₁ hBanti (fun x hx => hcov₁ ▸ hx) hch₁
      have h2 : t₁.card ≤ A.card := hAmax' t₁ (ht₁sub.trans (Finset.filter_subset _ _)) ht₁anti
      omega
    have hC₂card : C₂.card = B.card := by
      have h1 : B.card ≤ C₂.card :=
        antichain_le_chain_cover hBD₂ hBanti (fun x hx => hcov₂ ▸ hx) hch₂
      have h2 : t₂.card ≤ A.card := hAmax' t₂ (ht₂sub.trans (Finset.filter_subset _ _)) ht₂anti
      omega
    -- `B`, being of maximum cardinality, is saturated in `s`
    have hsat : ∀ p ∈ s, ∃ a ∈ B, p ≤ a ∨ a ≤ p := by
      intro p hp
      by_contra hno
      push Not at hno
      have hpB : p ∉ B := fun hpB => (hno p hpB).1 le_rfl
      have hins : IsAntichain (· ≤ ·) ((insert p B : Finset α) : Set α) := by
        rw [Finset.coe_insert]
        exact hBanti.insert (fun b hb _ hle => (hno b (Finset.mem_coe.mp hb)).2 hle)
          (fun b hb _ hle => (hno b (Finset.mem_coe.mp hb)).1 hle)
      have := hAmax' (insert p B) (Finset.insert_subset hp hBsub) hins
      rw [Finset.card_insert_of_notMem hpB, hBcard] at this
      omega
    obtain ⟨C, hcov, hch, hcard⟩ :=
      chainCover_glue hBsub hBanti hsat hcov₁ hch₁ hC₁card hcov₂ hch₂ hC₂card
    exact ⟨B, C, hBsub, hBanti, hcov, hch, hcard⟩
  · -- every maximum antichain has full lower or upper closure: remove a two-element chain
    -- `{x, y}` (a maximal element over a minimal one), which decreases the width.
    push Not at hcase
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨∅, ∅, Finset.Subset.refl _,
        by rw [Finset.coe_empty]; exact IsAntichain.empty, by simp, by simp, rfl⟩
    obtain ⟨x, hx⟩ := s.exists_maximal hs
    obtain ⟨y, hy⟩ := (s.filter (· ≤ x)).exists_minimal
      ⟨x, Finset.mem_filter.mpr ⟨hx.1, le_rfl⟩⟩
    have hys : y ∈ s := (Finset.mem_filter.mp hy.1).1
    have hyx : y ≤ x := (Finset.mem_filter.mp hy.1).2
    have hy_min : ∀ z ∈ s, z ≤ y → y ≤ z := fun z hz hzy =>
      hy.2 (Finset.mem_filter.mpr ⟨hz, hzy.trans hyx⟩) hzy
    set p : Finset α := insert x {y} with hpdef
    have hxp : x ∈ p := Finset.mem_insert_self x {y}
    have hyp : y ∈ p := Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    have hp_sub : p ⊆ s := Finset.insert_subset hx.1 (Finset.singleton_subset_iff.mpr hys)
    have hp_chain : IsChain (· ≤ ·) (p : Set α) := by
      rw [hpdef, Finset.coe_insert, Finset.coe_singleton]
      refine IsChain.singleton.insert fun b hb _ => Or.inr ?_
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hyx
    -- the width strictly drops after removing `{x, y}`
    have hwidth : ∀ t' ⊆ s \ p, IsAntichain (· ≤ ·) (t' : Set α) → t'.card < A.card := by
      intro t' ht'sub ht'anti
      rcases lt_or_eq_of_le (hAmax' t' (ht'sub.trans (Finset.sdiff_subset)) ht'anti) with h | h
      · exact h
      exfalso
      rcases eq_or_ne (s.filter (fun q => ∃ a ∈ t', q ≤ a)) s with hD | hD
      · -- the lower closure is full: it captures the maximal element `x`
        have hx' : x ∈ s.filter (fun q => ∃ a ∈ t', q ≤ a) := by rw [hD]; exact hx.1
        obtain ⟨a, hat', hxa⟩ := (Finset.mem_filter.mp hx').2
        have haS : a ∈ s := (Finset.mem_sdiff.mp (ht'sub hat')).1
        have hax : a = x := le_antisymm (hx.2 haS hxa) hxa
        exact (Finset.mem_sdiff.mp (ht'sub hat')).2 (by rw [hax]; exact hxp)
      · -- otherwise the upper closure is full: it captures the minimal element `y`
        have hU := hcase t' (ht'sub.trans (Finset.sdiff_subset)) ht'anti h hD
        have hy' : y ∈ s.filter (fun q => ∃ a ∈ t', a ≤ q) := by rw [hU]; exact hys
        obtain ⟨a, hat', hay⟩ := (Finset.mem_filter.mp hy').2
        have haS : a ∈ s := (Finset.mem_sdiff.mp (ht'sub hat')).1
        have hay' : a = y := le_antisymm hay (hy_min a haS hay)
        exact (Finset.mem_sdiff.mp (ht'sub hat')).2 (by rw [hay']; exact hyp)
    obtain ⟨t'', C'', ht''sub, ht''anti, hcov'', hch'', hcard''⟩ :=
      ih (s \ p) (Finset.sdiff_ssubset hp_sub ⟨x, hxp⟩)
    have hpC'' : p ∉ C'' := by
      intro h
      have hx'' : x ∈ s \ p := by
        rw [hcov'']; exact Finset.mem_biUnion.mpr ⟨p, h, hxp⟩
      exact (Finset.mem_sdiff.mp hx'').2 hxp
    have hcovIns : s = (insert p C'').biUnion id := by
      rw [Finset.biUnion_insert, ← hcov'', id_eq]
      exact (Finset.union_sdiff_of_subset hp_sub).symm
    have hchainsIns : ∀ c ∈ insert p C'', IsChain (· ≤ ·) (c : Set α) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hp_chain
      · exact hch'' c hc
    refine ⟨A, insert p C'', hAsub, hAanti, hcovIns, hchainsIns, ?_⟩
    have hwd : A.card ≤ (insert p C'').card :=
      antichain_le_chain_cover hAsub hAanti (fun z hz => hcovIns ▸ hz) hchainsIns
    have hlt : t''.card < A.card := hwidth t'' ht''sub ht''anti
    rw [Finset.card_insert_of_notMem hpC''] at hwd ⊢
    omega

/-! ### Mirsky's theorem

The proof below (peel off the minimal elements, one antichain per round) predates the manuscript
this file follows and will be aligned with its dual treatment when that proof is supplied. -/

/-- A nonempty finite chain has a least element. -/
theorem exists_min_mem_of_isChain [Preorder α] {c : Finset α}
    (hc : IsChain (· ≤ ·) (c : Set α)) (hne : c.Nonempty) : ∃ m ∈ c, ∀ y ∈ c, m ≤ y := by
  obtain ⟨m, hm⟩ := c.exists_minimal hne
  refine ⟨m, hm.1, fun y hy => ?_⟩
  rcases eq_or_ne m y with rfl | hmy
  · exact le_rfl
  · rcases hc (Finset.mem_coe.mpr hm.1) (Finset.mem_coe.mpr hy) hmy with h | h
    · exact h
    · exact hm.2 hy h

/-- **Mirsky's theorem (strong duality):** in any finite subset `s` of a partial order, some chain
and some antichain cover have the same size. Together with `chain_le_antichain_cover` this
expresses that the longest chain and the smallest antichain cover have a common size. -/
theorem mirsky [PartialOrder α] [DecidableEq α] (s : Finset α) :
    ∃ (t : Finset α) (C : Finset (Finset α)),
      t ⊆ s ∧ IsChain (· ≤ ·) (t : Set α) ∧
      s = C.biUnion id ∧ (∀ c ∈ C, IsAntichain (· ≤ ·) (c : Set α)) ∧
      C.card = t.card := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, ∅, Finset.Subset.refl _,
      by rw [Finset.coe_empty]; exact Set.subsingleton_empty.isChain, by simp, by simp, rfl⟩
  · -- `M` is the set of minimal elements of `s`: a nonempty antichain.
    set M : Finset α := s.filter (fun x => ∀ y ∈ s, y ≤ x → x ≤ y) with hMdef
    have hM_sub : M ⊆ s := Finset.filter_subset _ _
    have hM_mem : ∀ x, x ∈ M ↔ x ∈ s ∧ ∀ y ∈ s, y ≤ x → x ≤ y := fun x => by
      rw [hMdef, Finset.mem_filter]
    obtain ⟨m₀, hm₀⟩ := s.exists_minimal hs
    have hM_ne : M.Nonempty := ⟨m₀, (hM_mem m₀).mpr ⟨hm₀.1, fun y hy hle => hm₀.2 hy hle⟩⟩
    have hM_anti : IsAntichain (· ≤ ·) (M : Set α) := by
      intro a ha b hb hab hle
      rw [Finset.mem_coe, hM_mem] at ha hb
      exact hab (le_antisymm hle (hb.2 a ha.1 hle))
    -- Recurse on `s \ M`.
    have hs'_ss : s \ M ⊂ s := Finset.sdiff_ssubset hM_sub hM_ne
    obtain ⟨t', C', ht'sub, ht'chain, hs'cover, hC'anti, hC'card⟩ := ih (s \ M) hs'_ss
    have hM_notin : M ∉ C' := by
      intro hMC'
      obtain ⟨z, hz⟩ := hM_ne
      have : z ∈ s \ M := by rw [hs'cover, Finset.mem_biUnion]; exact ⟨M, hMC', hz⟩
      exact (Finset.mem_sdiff.mp this).2 hz
    -- Build a chain of size `t'.card + 1` by extending `t'` downwards with a minimal element.
    obtain ⟨t, ht_sub, ht_chain, ht_card⟩ :
        ∃ t : Finset α, t ⊆ s ∧ IsChain (· ≤ ·) (t : Set α) ∧ t.card = t'.card + 1 := by
      rcases t'.eq_empty_or_nonempty with rfl | ht'ne
      · obtain ⟨m, hm⟩ := hM_ne
        exact ⟨{m}, by simpa using hM_sub hm,
          by rw [Finset.coe_singleton]; exact Set.subsingleton_singleton.isChain, by simp⟩
      · obtain ⟨x₀, hx₀mem, hx₀least⟩ := exists_min_mem_of_isChain ht'chain ht'ne
        have hx₀s' := ht'sub hx₀mem
        have hx₀s : x₀ ∈ s := (Finset.mem_sdiff.mp hx₀s').1
        have hx₀notM : x₀ ∉ M := (Finset.mem_sdiff.mp hx₀s').2
        obtain ⟨m, hm_le, hm_mem⟩ :
            ∃ m, m ≤ x₀ ∧ (m ∈ s ∧ ∀ y ∈ s, y ≤ m → m ≤ y) := by
          obtain ⟨m, hm_mem_filter, hmin⟩ := (s.filter (· ≤ x₀)).exists_minimal
            ⟨x₀, Finset.mem_filter.mpr ⟨hx₀s, le_rfl⟩⟩
          rw [Finset.mem_filter] at hm_mem_filter
          obtain ⟨hms, hmx₀⟩ := hm_mem_filter
          exact ⟨m, hmx₀, hms, fun y hys hym =>
            hmin (Finset.mem_filter.mpr ⟨hys, le_trans hym hmx₀⟩) hym⟩
        have hmM : m ∈ M := (hM_mem m).mpr hm_mem
        have hm_ne_x₀ : m ≠ x₀ := fun h => hx₀notM (h ▸ hmM)
        have hm_notin_t' : m ∉ t' := fun hmt' =>
          hm_ne_x₀ (le_antisymm hm_le (hx₀least m hmt'))
        refine ⟨insert m t', ?_, ?_, ?_⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hm_mem.1
          · exact (Finset.mem_sdiff.mp (ht'sub hz)).1
        · rw [Finset.coe_insert]
          refine ht'chain.insert (fun b hb _ => Or.inl ?_)
          rw [Finset.mem_coe] at hb
          exact le_trans hm_le (hx₀least b hb)
        · rw [Finset.card_insert_of_notMem hm_notin_t']
    refine ⟨t, insert M C', ht_sub, ht_chain, ?_, ?_, ?_⟩
    · rw [Finset.biUnion_insert, ← hs'cover, id_eq]
      exact (Finset.union_sdiff_of_subset hM_sub).symm
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact hM_anti
      · exact hC'anti c hc
    · rw [Finset.card_insert_of_notMem hM_notin, hC'card, ht_card]
