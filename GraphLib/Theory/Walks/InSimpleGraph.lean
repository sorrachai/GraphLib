/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Walks.Basic
import GraphLib.Graph.Subgraph

/-!
# Walks in a `SimpleGraph`

This file specialises the graph-agnostic walk theory of
`GraphLib.Theory.Walks.Basic` to walks in a simple graph. A `VertexSeq`
or `Walk` is "in `G`" when its starting vertex belongs to `V(G)` and every
edge it traverses belongs to `E(G)`; this is captured by the predicate
`VertexSeq.IsVertexSeqIn`. The file then shows that the predicate is
preserved under all the basic walk operations (`append`, `reverse`,
`dropTail`, `takeUntil`, `loopErase`/`toPath`) and is monotone with
respect to passing to a supergraph.

## Main definitions

* `VertexSeq.IsVertexSeqIn G w` — `w` is a vertex sequence in `G`.
* `VertexSeq.edgeSet w` — the edges traversed by `w`, as a `Set (Sym2 α)`.
* `Walk.edgeSet w` — the edges traversed by the walk `w`.

The subgraph relation `SimpleGraph.subgraphOf` used in the monotonicity
results below is defined in `GraphLib.Graph.Subgraph`.

## Main statements

* `VertexSeq.isVertexSeqIn_iff` — `w` is in `G` iff `w.head ∈ V(G)` and
  `w.edgeSet ⊆ E(G)`. This is the working characterisation used by the
  rest of the file.
* `Walk.isVertexSeqIn_singleton_append`, `Walk.isVertexSeqIn_reverse`,
  `Walk.isVertexSeqIn_dropTail`, `Walk.isVertexSeqIn_takeUntil`,
  `Walk.isVertexSeqIn_append`, `Walk.isVertexSeqIn_walkAppend` — the
  predicate is closed under the corresponding walk operations.
* `Walk.isVertexSeqIn_toPath` — loop-erasing a walk preserves the
  predicate, so every walk in `G` admits a path in `G` between the same
  endpoints.
* `Walk.isVertexSeqIn_mono` — the predicate is monotone in the graph.

## Design choices

* **Specialisation, not duplication.** `GraphLib.Theory.Walks.Basic`
  develops the combinatorics of `VertexSeq`/`Walk` without reference to
  any graph. This file adds the simple-graph adjacency layer on top. The
  same pattern is intended for analogous files (`InGraph.lean`,
  `InDiGraph.lean`, `InSimpleDiGraph.lean`) that specialise the core
  walk API to other graph types; sharing the underlying combinatorics
  keeps the analytic proofs (loop-erasure, reversal, ...) written once.
* **Predicate, not refinement.** "Walk in `G`" is recorded as a
  `Prop`-valued predicate on a bare `VertexSeq`/`Walk`, not as a new type
  bundling the graph hypothesis. Conversions between unrestricted and
  restricted walks are then free, which is convenient when the graph is
  modified during a proof (e.g. edge deletion in algorithm correctness).
* **`edgeSet` parallels `toList`.** Just as `VertexSeq.toList` records
  the visited vertices, `VertexSeq.edgeSet` records the traversed edges
  as a set of `Sym2 α`. The membership condition is then phrased
  uniformly as `w.edgeSet ⊆ E(G)`, mirroring the existing edge-set
  conventions of `SimpleGraph` in this project.
* **`Set`, not `Finset`.** Edge sets are taken as `Set (Sym2 α)` to align
  with `SimpleGraph.edgeSet` (also a `Set`). This avoids gratuitous
  `Finset` machinery when no finiteness is required; downstream files
  that need a finite edge set can convert when relevant.
* **`grind`-driven proofs.** As in `Basic.lean`, most lemmas close by
  `grind` together with the elementary lemmas already registered as
  `@[grind]`. Closure lemmas are themselves tagged `@[grind →]` so that
  later files can chain them automatically.
-/

set_option tactic.hygienic false
set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

open scoped GraphLib
open GraphLib

namespace VertexSeq

/-- `IsVertexSeqIn G w` records that the vertex sequence `w` is a sequence
in the simple graph `G`: every vertex of `w` lies in `V(G)` and every two
consecutive vertices are joined by an edge of `G`. Defined inductively
matching the `singleton`/`cons` shape of `VertexSeq`. -/
@[grind] inductive IsVertexSeqIn (G : SimpleGraph α) : VertexSeq α → Prop
  /-- A singleton sequence is in `G` iff its vertex is a vertex of `G`. -/
  | singleton (v : α) (hv : v ∈ V(G)) : IsVertexSeqIn G (.singleton v)
  /-- Right-extending a sequence in `G` by a vertex `u` keeps it in `G`
  provided the new edge `s(w.tail, u)` is an edge of `G`. -/
  | cons (w : VertexSeq α) (u : α)
      (hw : IsVertexSeqIn G w)
      (he : s(w.tail, u) ∈ E(G)) :
      IsVertexSeqIn G (.cons w u)

/-- The set of edges traversed by the vertex sequence `w`. Empty for a
singleton; obtained inductively by adjoining the new edge `s(w.tail, u)`
to the previously traversed edges in the `cons` case. -/
abbrev edgeSet (w : VertexSeq α) : Set (Sym2 α) :=
  match w with
  | .singleton _ => ∅
  | .cons w u => w.edgeSet ∪ {s(w.tail, u)}

/-- Working characterisation of `IsVertexSeqIn`: `w` is a sequence in `G`
iff its starting vertex belongs to `V(G)` and every edge it traverses
belongs to `E(G)`. -/
lemma isVertexSeqIn_iff (G : SimpleGraph α) (w : VertexSeq α) :
    IsVertexSeqIn G w ↔ w.head ∈ V(G) ∧ w.edgeSet ⊆ E(G) := by
  induction w <;> grind

/-- Truncating a sequence at the first occurrence of `v` only drops edges:
the edge set of `w.takeUntil v h` is contained in the edge set of `w`. -/
lemma edgeSet_takeUntil_subset (w : VertexSeq α) (v : α) (h : v ∈ w.toList) :
    (w.takeUntil v h).edgeSet ⊆ w.edgeSet := by
  induction w generalizing v
  · intro a ha; simp [takeUntil] at ha
  · by_cases h2 : v ∈ w_1.toList
    · grind
    · simp [takeUntil, h2]

/-- Loop-erasing a sequence only drops edges: the edge set of `w.loopErase`
is contained in the edge set of `w`. Used downstream to lift edge-set
hypotheses from a walk to its associated path. -/
lemma edgeSet_loopErase_subset (w : VertexSeq α) :
    w.loopErase.edgeSet ⊆ w.edgeSet := by
  suffices h : ∀ n : ℕ, ∀ w : VertexSeq α,
      w.length = n → w.loopErase.edgeSet ⊆ w.edgeSet by grind
  intro n; refine Nat.strong_induction_on n ?_
  intro n ih w hlen; cases w
  · intro a ha; simp [loopErase, edgeSet] at ha
  · by_cases hmem : v ∈ w_1.toList
    · grind [edgeSet_takeUntil_subset, length_takeUntil_le]
    · intro a ha
      have ha' : a = s(w_1.loopErase.tail, v) ∨ a ∈ w_1.loopErase.edgeSet := by
        simpa [loopErase, hmem] using ha
      grind [tail_loopErase]

end VertexSeq

namespace Walk
open VertexSeq

/-- The set of edges traversed by the walk `w`, defined to be the edge set
of its underlying vertex sequence. -/
abbrev edgeSet (w : Walk α) : Set (Sym2 α) := w.seq.edgeSet

/-- Loop-erasing a walk only drops edges: the edge set of `w.toPath` is
contained in the edge set of `w`. -/
lemma edgeSet_toPath_subset (w : Walk α) : w.toPath.edgeSet ⊆ w.edgeSet := by
  simpa [edgeSet] using VertexSeq.edgeSet_loopErase_subset w.seq

/-- Working characterisation of `IsVertexSeqIn` for a `Walk`: `w` is in `G`
iff its starting vertex belongs to `V(G)` and every edge it traverses
belongs to `E(G)`. -/
lemma isVertexSeqIn_iff (G : SimpleGraph α) (w : Walk α) :
    IsVertexSeqIn G w.seq ↔ w.head ∈ V(G) ∧ w.edgeSet ⊆ E(G) := by
  grind [VertexSeq.isVertexSeqIn_iff]

/-- If `w` is a sequence in `G` and there is an edge `s(u, w.head) ∈ E(G)`,
then prepending the singleton `u` to `w` yields a sequence in `G`. -/
@[grind →]
lemma isVertexSeqIn_singleton_append (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) (u : α) (hedg : s(u, w.head) ∈ E(G)) :
    IsVertexSeqIn G ((VertexSeq.singleton u).append w) := by
  revert hedg
  induction hw with
  | singleton v hv =>
      intro hedg
      refine IsVertexSeqIn.cons (VertexSeq.singleton u) v ?_ (by simpa using hedg)
      exact IsVertexSeqIn.singleton u (G.incidence (by simpa using hedg) (by simp))
  | cons w0 u0 hw0 he ih =>
      intro hedg
      have happ : ((VertexSeq.singleton u).append (w0.cons u0))
          = ((VertexSeq.singleton u).append w0).cons u0 := rfl
      rw [happ]
      have hedg' : s(u, w0.head) ∈ E(G) := by simpa using hedg
      refine IsVertexSeqIn.cons _ _ (ih hedg') ?_
      simpa using he

/-- Reversing a sequence preserves the "in `G`" property. -/
@[grind →]
lemma isVertexSeqIn_reverse (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) :
    IsVertexSeqIn G w.reverse := by
  induction hw with
  | singleton v hv => simpa using IsVertexSeqIn.singleton v hv
  | cons w0 u0 hw0 he ih =>
      have hrev : (w0.cons u0).reverse
          = (VertexSeq.singleton u0).append w0.reverse := rfl
      rw [hrev]
      refine isVertexSeqIn_singleton_append G w0.reverse ih u0 ?_
      have hh : w0.reverse.head = w0.tail := VertexSeq.head_reverse w0
      rw [hh]
      simpa [Sym2.eq_swap] using he

/-- Reversing a walk preserves both the "in `G`" property and the
`IsWalk` (non-stalling) condition. -/
lemma isVertexSeqIn_and_isWalk_reverse (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w ∧ IsWalk w) :
    IsVertexSeqIn G w.reverse ∧ IsWalk w.reverse :=
  ⟨isVertexSeqIn_reverse G w hw.1, isWalk_reverse_of w hw.2⟩

/-- Dropping the last vertex of a sequence preserves the "in `G`" property. -/
@[grind →]
lemma isVertexSeqIn_dropTail (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w) :
    IsVertexSeqIn G w.dropTail := by
  cases hw with
  | singleton v hv => simpa [VertexSeq.dropTail] using IsVertexSeqIn.singleton v hv
  | cons w0 u hw0 _ => simpa [VertexSeq.dropTail] using hw0

/-- Dropping the last vertex of a walk preserves both the "in `G`" property
and the `IsWalk` condition. -/
lemma isVertexSeqIn_and_isWalk_dropTail (G : SimpleGraph α) (w : VertexSeq α)
    (hw : IsVertexSeqIn G w ∧ IsWalk w) :
    IsVertexSeqIn G w.dropTail ∧ IsWalk w.dropTail := by
  refine ⟨isVertexSeqIn_dropTail G w hw.1, ?_⟩
  cases hw.2 with
  | singleton v => simpa [VertexSeq.dropTail] using IsWalk.singleton v
  | cons w0 u hw0 _ => simpa [VertexSeq.dropTail] using hw0

/-- Truncating a sequence at the first occurrence of `v` preserves the
"in `G`" property. -/
@[grind →]
lemma isVertexSeqIn_takeUntil (G : SimpleGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw_in : IsVertexSeqIn G w) :
    IsVertexSeqIn G (w.takeUntil v h) := by
  induction w generalizing v with
  | singleton x =>
      have hvx : v = x := by simpa [VertexSeq.toList] using h
      subst hvx
      exact hw_in
  | cons w0 x ih =>
      have hw0_in : IsVertexSeqIn G w0 := by cases hw_in; assumption
      by_cases h2 : v ∈ w0.toList
      · change IsVertexSeqIn G ((w0.cons x).takeUntil v h)
        rw [show (w0.cons x).takeUntil v h = w0.takeUntil v h2 by
          simp [VertexSeq.takeUntil, h2]]
        exact ih v h2 hw0_in
      · have hv_eq : v = x := by
          have hmem : v ∈ (w0.cons x).toList := h
          simp [VertexSeq.toList] at hmem
          rcases hmem with rfl | hmem
          · rfl
          · exact (h2 hmem).elim
        subst hv_eq
        change IsVertexSeqIn G ((w0.cons v).takeUntil v h)
        rw [show (w0.cons v).takeUntil v h = w0.cons v by
          simp [VertexSeq.takeUntil, h2]]
        exact hw_in

/-- Truncating a walk at the first occurrence of `v` preserves both the
"in `G`" property and the `IsWalk` condition. -/
lemma isVertexSeqIn_and_isWalk_takeUntil (G : SimpleGraph α)
    (w : VertexSeq α) (v : α) (h : v ∈ w.toList)
    (hw : IsVertexSeqIn G w ∧ IsWalk w) :
    IsVertexSeqIn G (w.takeUntil v h) ∧ IsWalk (w.takeUntil v h) :=
  ⟨isVertexSeqIn_takeUntil G w v h hw.1, isWalk_takeUntil w v h hw.2⟩

/-- Being a sequence in a subgraph implies being a sequence in the ambient
graph (monotonicity in the graph argument). -/
@[grind →]
lemma isVertexSeqIn_mono {H G : SimpleGraph α} (w : VertexSeq α)
    (hw : IsVertexSeqIn H w) (hsub : SimpleGraph.subgraphOf H G) :
    IsVertexSeqIn G w := by
  induction hw with
  | singleton v hv => exact IsVertexSeqIn.singleton v (hsub.1 hv)
  | cons w0 u hw0 he ih => exact IsVertexSeqIn.cons w0 u ih (hsub.2 he)

/-- Monotonicity of "is a walk in `G`" along subgraph inclusion. -/
lemma isVertexSeqIn_and_isWalk_mono {H G : SimpleGraph α} (w : VertexSeq α)
    (hw : IsVertexSeqIn H w ∧ IsWalk w) (hsub : SimpleGraph.subgraphOf H G) :
    IsVertexSeqIn G w ∧ IsWalk w :=
  ⟨isVertexSeqIn_mono w hw.1 hsub, hw.2⟩

/-- Concatenating two sequences in `G` along a connecting edge gives a
sequence in `G`. -/
lemma isVertexSeqIn_append (G : SimpleGraph α)
    (w1 w2 : VertexSeq α)
    (h1 : IsVertexSeqIn G w1) (h2 : IsVertexSeqIn G w2)
    (hedg : s(w1.tail, w2.head) ∈ E(G)) :
    IsVertexSeqIn G (w1.append w2) := by
  induction h2 generalizing w1 with
  | singleton v hv =>
      rw [show w1.append (VertexSeq.singleton v) = w1.cons v from rfl]
      refine IsVertexSeqIn.cons w1 v h1 ?_
      simpa using hedg
  | cons w0 u hw0 he ih =>
      rw [show w1.append (w0.cons u) = (w1.append w0).cons u from rfl]
      refine IsVertexSeqIn.cons (w1.append w0) u (ih w1 h1 hedg) ?_
      have : (w1.append w0).tail = w0.tail := VertexSeq.tail_append w1 w0
      rw [this]; exact he

/-- Concatenating two walks in `G` meeting at a common vertex gives a walk
in `G`. -/
lemma isVertexSeqIn_walkAppend (G : SimpleGraph α)
    (w1 w2 : Walk α)
    (h1 : IsVertexSeqIn G w1.seq) (h2 : IsVertexSeqIn G w2.seq)
    (h : w1.tail = w2.head) :
    IsVertexSeqIn G (Walk.append w1 w2 h).seq := by
  unfold Walk.append
  by_cases hlen : w1.length = 0
  · simp only [hlen, dite_true]; exact h2
  · simp only [hlen, dite_false]
    refine isVertexSeqIn_append G w1.seq.dropTail w2.seq
      (isVertexSeqIn_dropTail G w1.seq h1) h2 ?_
    obtain ⟨w0, u, hwseq⟩ : ∃ (w0 : VertexSeq α) (u : α), w1.seq = w0.cons u := by
      match hseq : w1.seq with
      | .singleton v =>
          exfalso
          apply hlen
          change w1.seq.length = 0
          rw [hseq]; rfl
      | .cons w0 u => exact ⟨w0, u, rfl⟩
    have hh1 : IsVertexSeqIn G (w0.cons u) := hwseq ▸ h1
    have hedg' : s(w0.tail, u) ∈ E(G) := by
      cases hh1 with
      | cons _ _ _ he => exact he
    have hdrop_tail : w1.seq.dropTail.tail = w0.tail := by rw [hwseq]; rfl
    have hhead_eq : w2.seq.head = u := by
      change w2.head = u
      rw [← h]
      change w1.seq.tail = u
      rw [hwseq]; rfl
    rw [hdrop_tail, hhead_eq]
    exact hedg'

/-- Loop-erasing a walk preserves the "in `G`" property: every walk in `G`
yields a path in `G` between the same endpoints. -/
lemma isVertexSeqIn_toPath (G : SimpleGraph α) (w : Walk α)
    (hw : IsVertexSeqIn G w.seq) :
    IsVertexSeqIn G w.toPath.seq := by
  rw [VertexSeq.isVertexSeqIn_iff] at hw
  rw [VertexSeq.isVertexSeqIn_iff]
  refine ⟨?_, ?_⟩
  · have : w.toPath.head = w.head := head_toPath w
    change w.toPath.head ∈ V(G)
    rw [this]
    exact hw.1
  · exact (edgeSet_toPath_subset w).trans hw.2

end Walk
