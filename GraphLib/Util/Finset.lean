/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import GraphLib.Util.Decidable

/-!
# Finite iteration and bounded infima

Two graph-independent pieces of `Finset` theory, in the root namespace.

The first says that an *inflationary* operator on `Finset`s that never leaves a bounding
`Finset` `B` reaches a fixed point within `B.card` steps. This is the constructive
substitute for a least-fixed-point construction: `Finset β` is not `WellFoundedGT` for
infinite `β`, and Mathlib's `OrderHom.lfp` is `sInf`-based and noncomputable, so neither
supplies the explicit bound that an executable closure needs.

The second identifies an infimum of `Set.encard` over the sets satisfying a predicate `P`
with a minimum over a filtered powerset, whenever every `P`-set is contained in a fixed
finite `B`. This is the bridge between a `Set`-valued, `ℕ∞`-valued *specification* of a
"least size of a set with property `P`" and its executable counterpart, and it is stated
once here rather than four times over in the connectivity development.

## Main definitions

* `Finset.minENat` — the least element of a `Finset ℕ`, valued in `ℕ∞`, with `⊤` on the
  empty set.

## Main results

* `Finset.iterate_isFixed_of_inflationary` — the stabilization statement above.
* `Set.iInf_encard_eq_minENat_powerset` — the infimum bridge.
* `Set.exists_finset_card_eq_iInf_encard` — a minimizer, as a `Finset`.
* `Set.iInf_encard_eq_top_iff` — the infimum is `⊤` exactly when no `P`-set exists.

## Design choices

* **A hand-rolled `Finset.minENat` rather than `Finset.inf` or `Finset.min`.** The
  lattice structure that instance search finds on `ℕ∞` comes from the *noncomputable*
  `CompleteLinearOrder ℕ∞` — the very instance that makes `κ` noncomputable — so
  `Finset.inf … (fun n => (n : ℕ∞))` does not compute. `Finset.min` computes but lands
  in `WithTop ℕ`, whose order instances are not the `ℕ∞` ones, which would put a defeq
  obligation on every rewrite in the bridge. `minENat` takes the minimum in `ℕ` and
  adjoins `⊤` by hand: executable, and literally `ℕ∞`-valued.
* **The bound `B` is an explicit argument, not inferred.** The bridge is used with
  several bounding sets (`V(G)`, `E(G)`), and making `B` explicit keeps the hypothesis
  `∀ s, P s → s ⊆ ↑B` — the mathematical content of "the search space is finite" —
  visible at every call site.
-/

variable {β : Type*}

namespace Finset

/-! ## Stabilization of an inflationary iteration -/

section Iterate

variable {f : Finset β → Finset β} {B T : Finset β}

/-- An inflationary operator only grows its argument along iteration. -/
lemma subset_iterate (hle : ∀ T, T ⊆ f T) : ∀ n, T ⊆ f^[n] T := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (hle _)

/-- An operator preserving a bounding `Finset` keeps every iterate inside it. -/
lemma iterate_subset (hB : ∀ T ⊆ B, f T ⊆ B) (hT : T ⊆ B) : ∀ n, f^[n] T ⊆ B := by
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hB _ ih

/-- As long as the iteration keeps changing, each step gains at least one element. -/
lemma card_le_card_iterate (hle : ∀ T, T ⊆ f T) {n : ℕ}
    (h : ∀ k < n, f^[k] T ≠ f^[k + 1] T) : n ≤ (f^[n] T).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : f^[n] T ⊂ f^[n + 1] T := by
      refine ssubset_of_subset_of_ne ?_ (h n (by omega))
      rw [Function.iterate_succ_apply']
      exact hle _
    have := Finset.card_lt_card hstep
    have := ih fun k hk => h k (by omega)
    omega

/-- Since the iterates stay inside `B` and grow strictly until they repeat, they must
repeat within `B.card` steps. -/
lemma exists_iterate_eq_succ (hle : ∀ T, T ⊆ f T) (hB : ∀ T ⊆ B, f T ⊆ B) (hT : T ⊆ B) :
    ∃ k ≤ B.card, f^[k] T = f^[k + 1] T := by
  by_contra hcon
  push Not at hcon
  have h1 : B.card + 1 ≤ (f^[B.card + 1] T).card :=
    card_le_card_iterate hle fun k hk => hcon k (by omega)
  have h2 : (f^[B.card + 1] T).card ≤ B.card :=
    Finset.card_le_card (iterate_subset hB hT _)
  omega

/-- Once the iteration repeats it is constant from then on. -/
lemma iterate_eq_of_fixed {k m : ℕ} (h : f^[k] T = f^[k + 1] T) (hk : k ≤ m) :
    f^[m] T = f^[k] T := by
  have hfix : f (f^[k] T) = f^[k] T := by
    rw [← Function.iterate_succ_apply' f k T, ← h]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm k d, Function.iterate_add_apply, Function.iterate_fixed hfix]

/-- **Stabilization.** An inflationary operator preserving a bounding `Finset` `B` has
`f^[B.card + 1] T` as a fixed point, for every starting set `T ⊆ B`.

This is what makes an iterate-a-fixed-number-of-times closure correct: the result is
closed under `f`, so no further iteration could add anything. -/
theorem iterate_isFixed_of_inflationary (hle : ∀ T, T ⊆ f T) (hB : ∀ T ⊆ B, f T ⊆ B)
    (hT : T ⊆ B) : f (f^[B.card + 1] T) = f^[B.card + 1] T := by
  obtain ⟨k, hk, hkeq⟩ := exists_iterate_eq_succ hle hB hT
  rw [iterate_eq_of_fixed hkeq (by omega), ← Function.iterate_succ_apply' f k T, ← hkeq]

end Iterate

/-! ## The `ℕ∞`-valued minimum of a finite set of naturals -/

/-- The least element of a `Finset ℕ`, valued in `ℕ∞`, with the empty set sent to `⊤`.

This is the computable counterpart of `⨅ n ∈ s, (n : ℕ∞)`. It cannot be phrased as
`Finset.inf … (fun n => (n : ℕ∞))`: the lattice structure instance search finds on `ℕ∞`
is the one derived from `CompleteLinearOrder ℕ∞`, which is noncomputable — the same
instance that makes `κ` noncomputable in the first place. Going through `Finset.min'`
on `ℕ` and adjoining `⊤` by hand keeps the definition executable while landing in `ℕ∞`,
so the `⊤`-on-empty convention of the specification is matched exactly. -/
def minENat (s : Finset ℕ) : ℕ∞ :=
  if h : s.Nonempty then (s.min' h : ℕ) else ⊤

@[simp] lemma minENat_empty : (∅ : Finset ℕ).minENat = ⊤ := by
  simp [minENat]

@[simp] lemma minENat_eq_top_iff {s : Finset ℕ} : s.minENat = ⊤ ↔ s = ∅ := by
  unfold minENat
  split_ifs with h
  · simp [Finset.nonempty_iff_ne_empty.1 h]
  · simp [Finset.not_nonempty_iff_eq_empty.1 h]

/-- The minimum is a lower bound. -/
lemma minENat_le {s : Finset ℕ} {n : ℕ} (hn : n ∈ s) : s.minENat ≤ (n : ℕ∞) := by
  have h : s.Nonempty := ⟨n, hn⟩
  simp only [minENat, dif_pos h, Nat.cast_le]
  exact s.min'_le n hn

/-- The minimum is the *greatest* lower bound, as an `iff`; the empty case is covered,
both sides being vacuous there. -/
lemma le_minENat_iff {s : Finset ℕ} {m : ℕ∞} :
    m ≤ s.minENat ↔ ∀ n ∈ s, m ≤ (n : ℕ∞) := by
  unfold minENat
  split_ifs with h
  · exact ⟨fun hm n hn => hm.trans (by exact_mod_cast s.min'_le n hn),
      fun hm => hm _ (s.min'_mem h)⟩
  · simp [Finset.not_nonempty_iff_eq_empty.1 h]

/-- The minimum of a nonempty `Finset` is attained. -/
lemma exists_mem_eq_minENat {s : Finset ℕ} (h : s.Nonempty) :
    ∃ n ∈ s, s.minENat = (n : ℕ∞) :=
  ⟨s.min' h, s.min'_mem h, by simp [minENat, dif_pos h]⟩

end Finset

namespace Set

/-! ## Bounded infima of `encard` -/

section BoundedInfimum

variable (B : Finset β) (P : Set β → Prop) [DecidablePred fun s : Finset β => P ↑s]

/-- **The infimum bridge.** If every set satisfying `P` is contained in the finite set
`B`, then the least `encard` of a `P`-set is the least cardinality of a `P`-subset of
`B`, computed as a minimum over the filtered powerset.

Both sides are `⊤` when no set satisfies `P`, so no nonemptiness hypothesis is needed:
the empty `⨅` and `Finset.minENat` of the empty set agree on that convention. -/
theorem iInf_encard_eq_minENat_powerset (hP : ∀ s : Set β, P s → s ⊆ ↑B) :
    ⨅ (s : Set β) (_ : P s), s.encard
      = ((B.powerset.filter fun s : Finset β => P ↑s).image Finset.card).minENat := by
  refine le_antisymm (Finset.le_minENat_iff.2 fun n hn => ?_) (le_iInf₂ fun s hs => ?_)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hn
    rw [Finset.mem_filter] at ht
    rw [← Set.encard_coe_eq_coe_finsetCard t]
    exact iInf₂_le (↑t : Set β) ht.2
  · have hfin : s.Finite := Set.Finite.subset B.finite_toSet (hP s hs)
    have hmem : hfin.toFinset ∈ B.powerset.filter fun t : Finset β => P ↑t := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Set.Finite.toFinset_subset.2 (hP s hs), by rwa [hfin.coe_toFinset]⟩
    rw [hfin.encard_eq_coe_toFinset_card]
    exact Finset.minENat_le (Finset.mem_image_of_mem _ hmem)

omit [DecidablePred fun s : Finset β => P ↑s] in
/-- The infimum is attained by an explicit `Finset` as soon as some set satisfies `P`.

No decidability is needed to *state* this, and none is needed of the caller: the filtered
powerset appears only inside the proof. -/
theorem exists_finset_card_eq_iInf_encard (hP : ∀ s : Set β, P s → s ⊆ ↑B)
    (hne : ∃ s : Set β, P s) :
    ∃ s : Finset β, s ⊆ B ∧ P ↑s ∧
      (s.card : ℕ∞) = ⨅ (t : Set β) (_ : P t), t.encard := by
  classical
  obtain ⟨t, ht⟩ := hne
  have hfin : t.Finite := Set.Finite.subset B.finite_toSet (hP t ht)
  have hFne : (B.powerset.filter fun s : Finset β => P ↑s).Nonempty := by
    refine ⟨hfin.toFinset, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Set.Finite.toFinset_subset.2 (hP t ht), by rwa [hfin.coe_toFinset]⟩
  obtain ⟨n, hn, hmin⟩ := Finset.exists_mem_eq_minENat (hFne.image Finset.card)
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hn
  rw [Finset.mem_filter, Finset.mem_powerset] at hs
  exact ⟨s, hs.1, hs.2, by rw [iInf_encard_eq_minENat_powerset B P hP, hmin]⟩

omit [DecidablePred fun s : Finset β => P ↑s] in
/-- The infimum is `⊤` exactly when nothing satisfies `P`. Combined with
`iInf_encard_eq_inf_powerset` this makes "is there any `P`-set at all?" a `Finset`
emptiness check. -/
theorem iInf_encard_eq_top_iff (hP : ∀ s : Set β, P s → s ⊆ ↑B) :
    (⨅ (s : Set β) (_ : P s), s.encard) = ⊤ ↔ ¬ ∃ s : Set β, P s := by
  constructor
  · rintro htop ⟨s, hs⟩
    have hfin : s.Finite := Set.Finite.subset B.finite_toSet (hP s hs)
    have hle : (⨅ (t : Set β) (_ : P t), t.encard) ≤ s.encard := iInf₂_le s hs
    rw [htop, top_le_iff, hfin.encard_eq_coe_toFinset_card] at hle
    exact (ENat.coe_ne_top _) hle
  · intro hne
    simp only [iInf_eq_top]
    exact fun s hs => absurd ⟨s, hs⟩ hne

end BoundedInfimum

end Set
