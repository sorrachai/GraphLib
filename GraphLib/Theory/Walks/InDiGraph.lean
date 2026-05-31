/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import GraphLib.Theory.Walks.Basic
import GraphLib.Graph.Subgraph

/-!
# Walks in a `SimpleDiGraph`

This file specialises the graph-agnostic walk theory of
`GraphLib.Theory.Walks.Basic` to walks in a simple directed graph. A
`VertexSeq` or `Walk` is "in `G`" when its starting vertex belongs to
`V(G)` and every directed edge it traverses — taken in walking order —
belongs to `E(G)`; this is captured by the predicate
`VertexSeq.IsVertexSeqInDi`. The file then shows that the predicate is
preserved under the basic walk operations (`append`, `dropTail`,
`takeUntil`, `loopErase`/`toPath`) and is monotone with respect to
passing to a supergraph.

## Main definitions

* `VertexSeq.IsVertexSeqInDi G w` — `w` is a vertex sequence in the
  simple directed graph `G`.
* `VertexSeq.dirEdgeSet w` — the directed edges traversed by `w`, as a
  `Set (α × α)`.
* `Walk.dirEdgeSet w` — the directed edges traversed by the walk `w`.

## Main statements

* `VertexSeq.isVertexSeqInDi_iff` — `w` is in `G` iff `w.head ∈ V(G)` and
  `w.dirEdgeSet ⊆ E(G)`.
* `Walk.isVertexSeqInDi_singleton_append`, `Walk.isVertexSeqInDi_dropTail`,
  `Walk.isVertexSeqInDi_takeUntil`, `Walk.isVertexSeqInDi_append`,
  `Walk.isVertexSeqInDi_walkAppend` — the predicate is closed under the
  corresponding walk operations.
* `Walk.isVertexSeqInDi_toPath` — loop-erasing a walk preserves the
  predicate, so every walk in `G` admits a path in `G` between the same
  endpoints.
* `Walk.isVertexSeqInDi_mono` — the predicate is monotone in the graph.

## Design choices

* **Mirror of `InSimpleGraph.lean`.** This file is the directed analogue
  of `GraphLib.Theory.Walks.InSimpleGraph`. The only substantive
  difference is that edges are ordered pairs `(u, v) : α × α` rather
  than `Sym2 α`. The underlying combinatorics (`takeUntil`,
  `loopErase`, …) come from `Basic.lean` and are shared verbatim.
* **No `reverse` lemma.** Walking is directional, so reversing a walk
  produces a sequence whose consecutive pairs are the original edges
  with swapped endpoints; these need not belong to `E(G)`. The
  `reverse` family of lemmas from `InSimpleGraph.lean` therefore has
  no analogue here. A statement about walks in the *reverse* digraph
  would require an `SimpleDiGraph.reverse` constructor first.
* **`Di` suffix on conflicting names.** `IsVertexSeqInDi` and
  `dirEdgeSet` are renamed (rather than overloaded in the `VertexSeq`
  namespace) because Lean cannot dispatch `def`/`inductive` on a
  parameter type alone. This keeps the simple-graph and simple-digraph
  specialisations interoperable in a single import.
* **`grind`-driven proofs.** As in `InSimpleGraph.lean`, most lemmas
  close by `grind` with the inductive constructors as `@[grind]`
  patterns; closure lemmas are tagged `@[grind →]` for downstream
  chaining.
-/

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

open scoped GraphLib
open GraphLib

namespace VertexSeq

/-- `IsVertexSeqInDi G w` records that the vertex sequence `w` is a
sequence in the simple directed graph `G`: every vertex of `w` lies in
`V(G)` and every two consecutive vertices `(u, v)` (in walking order)
form a directed edge of `G`. Defined inductively matching the
`singleton`/`cons` shape of `VertexSeq`. -/
@[grind] inductive IsVertexSeqInDi (G : SimpleDiGraph α) : VertexSeq α → Prop
  /-- A singleton sequence is in `G` iff its vertex is a vertex of `G`. -/
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqInDi G (.singleton v)
  /-- Right-extending a sequence in `G` by a vertex `u` keeps it in `G`
  provided the directed edge `(w.tail, u)` is an edge of `G`. -/
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqInDi G w)
      (he : (w.tail, u) ∈ E(G)) :
      IsVertexSeqInDi G (.cons w u)

/-- The set of directed edges traversed by the vertex sequence `w`, in
walking order. Empty for a singleton; obtained inductively by adjoining
the new edge `(w.tail, u)` in the `cons` case. -/
abbrev dirEdgeSet (w : VertexSeq α) : Set (α × α) :=
  match w with
  | .singleton _ => ∅
  | .cons w u => w.dirEdgeSet ∪ {(w.tail, u)}

/-- Working characterisation of `IsVertexSeqInDi`: `w` is a sequence in
`G` iff its starting vertex belongs to `V(G)` and every directed edge
it traverses belongs to `E(G)`. -/
lemma isVertexSeqInDi_iff (G : SimpleDiGraph α) (w : VertexSeq α) :
    IsVertexSeqInDi G w ↔ w.head ∈ V(G) ∧ w.dirEdgeSet ⊆ E(G) := by
  induction w <;> grind

/-- Truncating a sequence at the first occurrence of `v` only drops
directed edges: the dir-edge set of `w.takeUntil v h` is contained in
the dir-edge set of `w`. -/
lemma dirEdgeSet_takeUntil_subset (w : VertexSeq α) (v : α) (h : v ∈ w.toList) :
    (w.takeUntil v h).dirEdgeSet ⊆ w.dirEdgeSet := by
  induction w generalizing v
  · intro a ha; simp [takeUntil] at ha
  · by_cases h2 : v ∈ w_1.toList
    · grind
    · simp [takeUntil, h2]

/-- Loop-erasing a sequence only drops directed edges: the dir-edge set
of `w.loopErase` is contained in the dir-edge set of `w`. Used
downstream to lift dir-edge-set hypotheses from a walk to its associated
path. -/
lemma dirEdgeSet_loopErase_subset (w : VertexSeq α) :
    w.loopErase.dirEdgeSet ⊆ w.dirEdgeSet := by
  suffices h : ∀ n : ℕ, ∀ w : VertexSeq α,
      w.length = n → w.loopErase.dirEdgeSet ⊆ w.dirEdgeSet by grind
  intro n; refine Nat.strong_induction_on n ?_
  intro n ih w hlen; cases w
  · intro a ha; simp [loopErase, dirEdgeSet] at ha
  · by_cases hmem : v ∈ w_1.toList
    · grind [dirEdgeSet_takeUntil_subset, length_takeUntil_le]
    · intro a ha
      have ha' : a = (w_1.loopErase.tail, v) ∨ a ∈ w_1.loopErase.dirEdgeSet := by
        simpa [loopErase, hmem] using ha
      grind [tail_loopErase]

end VertexSeq

namespace Walk
open VertexSeq

/-- The set of directed edges traversed by the walk `w`, defined to be
the dir-edge set of its underlying vertex sequence. -/
abbrev dirEdgeSet (w : Walk α) : Set (α × α) := w.val.dirEdgeSet

/-- Loop-erasing a walk only drops directed edges: the dir-edge set of
`w.toPath` is contained in the dir-edge set of `w`. -/
lemma dirEdgeSet_toPath_subset (w : Walk α) :
    w.toPath.val.dirEdgeSet ⊆ w.dirEdgeSet := by
  simpa [dirEdgeSet] using VertexSeq.dirEdgeSet_loopErase_subset w.val

/-- Working characterisation of `IsVertexSeqInDi` for a `Walk`: `w` is in
`G` iff its starting vertex belongs to `V(G)` and every directed edge it
traverses belongs to `E(G)`. -/
lemma isVertexSeqInDi_iff (G : SimpleDiGraph α) (w : Walk α) :
    IsVertexSeqInDi G w.val ↔ w.head ∈ V(G) ∧ w.dirEdgeSet ⊆ E(G) := by
  grind [VertexSeq.isVertexSeqInDi_iff]

/-- If `w` is a sequence in `G` and there is a directed edge
`(u, w.head) ∈ E(G)`, then prepending the singleton `u` to `w` yields a
sequence in `G`. -/
@[grind →]
lemma isVertexSeqInDi_singleton_append (G : SimpleDiGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqInDi G w) (u : α) (hedg : (u, w.head) ∈ E(G)) :
    IsVertexSeqInDi G ((VertexSeq.singleton u).append w) := by
  revert hedg
  induction hw with
  | singleton v hv =>
      intro hedg
      refine IsVertexSeqInDi.cons (VertexSeq.singleton u) v ?_ (by simpa using hedg)
      have hu : u ∈ V(G) := (G.incidence (by simpa using hedg)).1
      exact IsVertexSeqInDi.singleton u hu
  | cons w0 u0 hw0 he ih =>
      intro hedg
      have happ : ((VertexSeq.singleton u).append (w0.cons u0))
          = ((VertexSeq.singleton u).append w0).cons u0 := rfl
      rw [happ]
      have hedg' : (u, w0.head) ∈ E(G) := by simpa using hedg
      refine IsVertexSeqInDi.cons _ _ (ih hedg') ?_
      simpa using he

/-- Dropping the last vertex of a sequence preserves the "in `G`"
property. -/
@[grind →]
lemma isVertexSeqInDi_dropTail (G : SimpleDiGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqInDi G w) :
    IsVertexSeqInDi G w.dropTail := by
  cases hw with
  | singleton v hv => simpa [VertexSeq.dropTail] using IsVertexSeqInDi.singleton v hv
  | cons w0 u hw0 _ => simpa [VertexSeq.dropTail] using hw0

/-- Dropping the last vertex of a walk preserves both the "in `G`"
property and the `IsWalk` condition. -/
lemma isVertexSeqInDi_and_isWalk_dropTail (G : SimpleDiGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqInDi G w ∧ IsWalk w) :
    IsVertexSeqInDi G w.dropTail ∧ IsWalk w.dropTail := by
  refine ⟨isVertexSeqInDi_dropTail G w hw.1, ?_⟩
  cases hw.2 with
  | singleton v => simpa [VertexSeq.dropTail] using IsWalk.singleton v
  | cons w0 u hw0 _ => simpa [VertexSeq.dropTail] using hw0

/-- Truncating a sequence at the first occurrence of `v` preserves the
"in `G`" property. -/
@[grind →]
lemma isVertexSeqInDi_takeUntil (G : SimpleDiGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw_in : IsVertexSeqInDi G w) :
    IsVertexSeqInDi G (w.takeUntil v h) := by
  induction w generalizing v with
  | singleton x =>
      have hvx : v = x := by simpa [VertexSeq.toList] using h
      subst hvx
      exact hw_in
  | cons w0 x ih =>
      have hw0_in : IsVertexSeqInDi G w0 := by cases hw_in; assumption
      by_cases h2 : v ∈ w0.toList
      · change IsVertexSeqInDi G ((w0.cons x).takeUntil v h)
        rw [show (w0.cons x).takeUntil v h = w0.takeUntil v h2 by
          simp [VertexSeq.takeUntil, h2]]
        exact ih v h2 hw0_in
      · have hv_eq : v = x := by
          have hmem : v ∈ (w0.cons x).toList := h
          simp [VertexSeq.toList] at hmem
          tauto
        subst hv_eq
        change IsVertexSeqInDi G ((w0.cons v).takeUntil v h)
        rw [show (w0.cons v).takeUntil v h = w0.cons v by
          simp [VertexSeq.takeUntil, h2]]
        exact hw_in

/-- Truncating a walk at the first occurrence of `v` preserves both the
"in `G`" property and the `IsWalk` condition. -/
lemma isVertexSeqInDi_and_isWalk_takeUntil (G : SimpleDiGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw : IsVertexSeqInDi G w ∧ IsWalk w) :
    IsVertexSeqInDi G (w.takeUntil v h) ∧ IsWalk (w.takeUntil v h) :=
  ⟨isVertexSeqInDi_takeUntil G w v h hw.1, isWalk_takeUntil w v h hw.2⟩

/-- Being a sequence in a subgraph implies being a sequence in the
ambient graph (monotonicity in the graph argument). -/
@[grind →]
lemma isVertexSeqInDi_mono {H G : SimpleDiGraph α} (w : VertexSeq α)
    (hw : IsVertexSeqInDi H w) (hsub : SimpleDiGraph.subgraphOf H G) :
    IsVertexSeqInDi G w := by
  induction hw with
  | singleton v hv => exact IsVertexSeqInDi.singleton v (hsub.1 hv)
  | cons w0 u hw0 he ih => exact IsVertexSeqInDi.cons w0 u ih (hsub.2 he)

/-- Monotonicity of "is a walk in `G`" along subgraph inclusion. -/
lemma isVertexSeqInDi_and_isWalk_mono {H G : SimpleDiGraph α} (w : VertexSeq α)
    (hw : IsVertexSeqInDi H w ∧ IsWalk w) (hsub : SimpleDiGraph.subgraphOf H G) :
    IsVertexSeqInDi G w ∧ IsWalk w :=
  ⟨isVertexSeqInDi_mono w hw.1 hsub, hw.2⟩

/-- Concatenating two sequences in `G` along a connecting directed edge
gives a sequence in `G`. -/
lemma isVertexSeqInDi_append (G : SimpleDiGraph α)
    (w1 w2 : VertexSeq α)
    (h1 : IsVertexSeqInDi G w1) (h2 : IsVertexSeqInDi G w2)
    (hedg : (w1.tail, w2.head) ∈ E(G)) :
    IsVertexSeqInDi G (w1.append w2) := by
  induction h2 generalizing w1 with
  | singleton v hv =>
      rw [show w1.append (VertexSeq.singleton v) = w1.cons v from rfl]
      refine IsVertexSeqInDi.cons w1 v h1 ?_
      simpa using hedg
  | cons w0 u hw0 he ih =>
      rw [show w1.append (w0.cons u) = (w1.append w0).cons u from rfl]
      refine IsVertexSeqInDi.cons (w1.append w0) u (ih w1 h1 hedg) ?_
      have : (w1.append w0).tail = w0.tail := VertexSeq.tail_append w1 w0
      rw [this]; exact he

/-- Concatenating two walks in `G` meeting at a common vertex gives a
walk in `G`. -/
lemma isVertexSeqInDi_walkAppend (G : SimpleDiGraph α)
    (w1 w2 : Walk α)
    (h1 : IsVertexSeqInDi G w1.val) (h2 : IsVertexSeqInDi G w2.val)
    (h : w1.tail = w2.head) :
    IsVertexSeqInDi G (Walk.append w1 w2 h).val := by
  unfold Walk.append
  by_cases hlen : w1.length = 0
  · simp only [hlen, dite_true]; exact h2
  · simp only [hlen, dite_false]
    refine isVertexSeqInDi_append G w1.val.dropTail w2.val
      (isVertexSeqInDi_dropTail G w1.val h1) h2 ?_
    obtain ⟨w0, u, hwseq⟩ : ∃ (w0 : VertexSeq α) (u : α), w1.val = w0.cons u := by
      match hseq : w1.val with
      | .singleton v =>
          exfalso
          apply hlen
          change w1.val.length = 0
          rw [hseq]; rfl
      | .cons w0 u => exact ⟨w0, u, rfl⟩
    have hh1 : IsVertexSeqInDi G (w0.cons u) := hwseq ▸ h1
    have hedg' : (w0.tail, u) ∈ E(G) := by
      cases hh1 with
      | cons _ _ _ he => exact he
    have hdrop_tail : w1.val.dropTail.tail = w0.tail := by rw [hwseq]; rfl
    have hhead_eq : w2.val.head = u := by
      change w2.head = u
      rw [← h]
      change w1.val.tail = u
      rw [hwseq]; rfl
    rw [hdrop_tail, hhead_eq]
    exact hedg'

/-- Loop-erasing a walk preserves the "in `G`" property: every walk in
`G` yields a path in `G` between the same endpoints. -/
lemma isVertexSeqInDi_toPath (G : SimpleDiGraph α) (w : Walk α)
    (hw : IsVertexSeqInDi G w.val) :
    IsVertexSeqInDi G w.toPath.val.val := by
  rw [VertexSeq.isVertexSeqInDi_iff] at hw
  rw [VertexSeq.isVertexSeqInDi_iff]
  refine ⟨?_, ?_⟩
  · have : w.toPath.head = w.head := head_toPath w
    change w.toPath.head ∈ V(G)
    rw [this]
    exact hw.1
  · exact (dirEdgeSet_toPath_subset w).trans hw.2

end Walk
