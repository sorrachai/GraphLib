/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Graph.Finite
import GraphLib.Theory.Connectivity.Cuts
import Mathlib.Data.ENat.Lattice

/-!
# Vertex and edge connectivity

The connectivity numbers `κ(G)` and `κ'(G)` measure how many vertices, respectively
edges, must be removed to destroy the connectivity of `G`.

## Main definitions

* `SimpleGraph.IsVertexSeparating G S` — deleting `S` disconnects `G` *or* leaves at most
  one vertex.
* `SimpleGraph.IsEdgeSeparating G F` — deleting `F` disconnects `G`, or `G` is trivial.
* `SimpleGraph.vertexConnectivity G` — the least size of such an `S`, written `κ(G)`.
* `SimpleGraph.edgeConnectivity G` — the least size of such an `F`, written `κ'(G)`.

## Main results

* `SimpleGraph.vertexConnectivity_ge_iff` / `SimpleGraph.edgeConnectivity_ge_iff` — the
  lower-bound characterizations; nearly everything else is a corollary.
* `SimpleGraph.vertexConnectivity_le_encard` / `SimpleGraph.edgeConnectivity_le_encard` —
  every separating set bounds the connectivity number from above.
* `SimpleGraph.vertexConnectivity_exists` / `SimpleGraph.edgeConnectivity_exists` — the
  infimum is attained, unconditionally; `SimpleGraph.vertexCutNumber_exists` and
  `SimpleGraph.edgeCutNumber_exists` are the conditional analogues for the cut numbers.

## Design choices

* **The Diestel convention.** `κ` is the least size of a vertex set whose deletion
  disconnects `G` *or leaves at most one vertex*. Without the second disjunct the
  complete graph `Kₙ` would have `κ(Kₙ) = ⊤`, since no vertex set disconnects it; with
  it, `κ(Kₙ) = n - 1`, and Whitney's inequality `κ ≤ κ' ≤ δ` holds without a case split.
  The same patch on the edge side gives the usual convention `κ'(G) = 0` for a graph with
  at most one vertex. The unpatched "least vertex cut" quantity is kept as
  `vertexCutNumber` / `edgeCutNumber` for comparison, with the degeneracy documented.
* **`Set.encard`, not `Set.ncard`.** `encard` is already `ℕ∞`-valued, so it needs no
  coercion inside the `⨅`, and it returns `⊤` rather than the junk value `0` on infinite
  sets. A `κ` built on `ncard` would report `0` — perfect disconnection — for a graph
  whose only cuts are infinite.
* **Nested `⨅`, mirroring `girth`.** The shape `⨅ (x) (_ : P x), f x` is the one used by
  `SimpleGraph.girth` in `GraphLib.Theory.Structures.SimpleGraph_only.Girth`, so the
  same infimum API (`le_iInf₂_iff`, `iInf₂_le`, `iInf_eq_top`) applies verbatim. The
  empty-index convention makes the connectivity of a graph with no separating set `⊤`
  automatically.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Separating sets -/

/-- `S` is *vertex-separating* in `G` when deleting it either disconnects `G` or leaves
at most one vertex.

The second disjunct is the Diestel convention. It is what makes `κ(Kₙ) = n - 1` rather
than `⊤`: no set of vertices disconnects a complete graph, but deleting all but one of
them leaves a single vertex. -/
def IsVertexSeparating (G : SimpleGraph α) (S : Set α) : Prop :=
  S ⊆ V(G) ∧ (¬ (G.deleteVertices S).IsPreconnected ∨ (V(G) \ S).Subsingleton)

/-- `F` is *edge-separating* in `G` when deleting it disconnects `G`, or `G` has at most
one vertex. The second disjunct gives the usual convention `κ'(G) = 0` on the trivial
graph, where no set of edges can disconnect anything. -/
def IsEdgeSeparating (G : SimpleGraph α) (F : Set (Sym2 α)) : Prop :=
  F ⊆ E(G) ∧ (¬ (G.deleteEdges F).IsPreconnected ∨ V(G).Subsingleton)

/-- Every vertex cut is vertex-separating. -/
lemma IsVertexCut.isVertexSeparating {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : G.IsVertexSeparating S := ⟨h.1, Or.inl h.2⟩

/-- Every edge cut is edge-separating. -/
lemma IsEdgeCut.isEdgeSeparating {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeCut F) : G.IsEdgeSeparating F := ⟨h.1, Or.inl h.2⟩

/-! ## The connectivity numbers -/

/-- The *vertex connectivity* `κ(G)`: the least number of vertices whose deletion either
disconnects `G` or leaves at most one vertex.

It is `⊤` exactly when no set of vertices does either — for instance in an infinite
complete graph. See `IsVertexSeparating` for the convention on complete graphs.
The computable counterpart `computeVertexConnectivity` is available in `./Computable.lean`. -/
noncomputable def vertexConnectivity (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (S : Set α) (_ : G.IsVertexSeparating S), S.encard

/-- The *edge connectivity* `κ'(G)`: the least number of edges whose deletion
disconnects `G`, with the convention `κ'(G) = 0` when `G` has at most one vertex.
The computable counterpart `computeEdgeConnectivity` is available in `./Computable.lean`. -/
noncomputable def edgeConnectivity (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (F : Set (Sym2 α)) (_ : G.IsEdgeSeparating F), F.encard

end SimpleGraph

/-- `κ(G)` is the vertex connectivity of `G`.

Declared directly inside `namespace GraphLib` rather than inside `namespace SimpleGraph`,
so that `scoped` attaches it to `GraphLib` and a plain `open scoped GraphLib` brings it
into scope alongside `V(G)` and `E(G)`. -/
scoped notation "κ(" G ")" => GraphLib.SimpleGraph.vertexConnectivity G

/-- `κ'(G)` is the edge connectivity of `G`. -/
scoped notation "κ'(" G ")" => GraphLib.SimpleGraph.edgeConnectivity G

namespace SimpleGraph

/-! ## The infimum API -/

/-- Every vertex-separating set bounds `κ(G)` from above. -/
lemma vertexConnectivity_le_encard {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexSeparating S) : κ(G) ≤ S.encard :=
  iInf₂_le S h

/-- Every edge-separating set bounds `κ'(G)` from above. -/
lemma edgeConnectivity_le_encard {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeSeparating F) : κ'(G) ≤ F.encard :=
  iInf₂_le F h

/-- Every vertex cut bounds `κ(G)` from above. -/
lemma vertexConnectivity_le_encard_of_isVertexCut {G : SimpleGraph α} {S : Set α}
    (h : G.IsVertexCut S) : κ(G) ≤ S.encard :=
  vertexConnectivity_le_encard h.isVertexSeparating

/-- Every edge cut bounds `κ'(G)` from above. -/
lemma edgeConnectivity_le_encard_of_isEdgeCut {G : SimpleGraph α} {F : Set (Sym2 α)}
    (h : G.IsEdgeCut F) : κ'(G) ≤ F.encard :=
  edgeConnectivity_le_encard h.isEdgeSeparating

/-- The lower-bound characterization of `κ(G)`: the workhorse lemma. -/
theorem vertexConnectivity_ge_iff {G : SimpleGraph α} {n : ℕ∞} :
    n ≤ κ(G) ↔ ∀ S : Set α, G.IsVertexSeparating S → n ≤ S.encard := by
  simp [vertexConnectivity, le_iInf_iff]

/-- The lower-bound characterization of `κ'(G)`. -/
theorem edgeConnectivity_ge_iff {G : SimpleGraph α} {n : ℕ∞} :
    n ≤ κ'(G) ↔ ∀ F : Set (Sym2 α), G.IsEdgeSeparating F → n ≤ F.encard := by
  simp [edgeConnectivity, le_iInf_iff]

/-- `κ(G) = ⊤` exactly when every vertex-separating set is infinite — in particular when
there is no separating set at all. -/
theorem vertexConnectivity_eq_top_iff {G : SimpleGraph α} :
    κ(G) = ⊤ ↔ ∀ S : Set α, G.IsVertexSeparating S → S.Infinite := by
  simp [vertexConnectivity, iInf_eq_top]

/-- `κ'(G) = ⊤` exactly when every edge-separating set is infinite. -/
theorem edgeConnectivity_eq_top_iff {G : SimpleGraph α} :
    κ'(G) = ⊤ ↔ ∀ F : Set (Sym2 α), G.IsEdgeSeparating F → F.Infinite := by
  simp [edgeConnectivity, iInf_eq_top]

/-! ## Extremal separating sets, and attainment

The `⨅` defining `κ` ranges over a family that is never empty — deleting *all* the
vertices leaves nothing, which is a subsingleton — and an `ℕ∞`-valued infimum is always
attained, `ℕ∞` being well-ordered. So `κ(G)` and `κ'(G)` are realized by an actual
separating set, with no finiteness hypothesis anywhere: for an infinite complete graph
the minimizer is `V(G)` itself and both sides are `⊤`.

The unpatched cut numbers below do *not* enjoy this, which is the sharpest statement of
what the Diestel convention buys. -/

/-- The whole vertex set is vertex-separating: deleting it leaves no vertex at all. -/
lemma isVertexSeparating_vertexSet (G : SimpleGraph α) : G.IsVertexSeparating V(G) :=
  ⟨subset_rfl, Or.inr (by rw [Set.diff_self]; exact Set.subsingleton_empty)⟩

/-- Deleting every edge leaves no edge. -/
@[simp] lemma edgeSet_deleteEdges_self (G : SimpleGraph α) :
    E(G.deleteEdges E(G)) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ he => he.2 he.1

/-- The whole edge set is edge-separating: an edgeless graph is preconnected only if it
has at most one vertex, and that is the second disjunct. -/
lemma isEdgeSeparating_edgeSet (G : SimpleGraph α) : G.IsEdgeSeparating E(G) := by
  refine ⟨subset_rfl, ?_⟩
  by_cases hsub : V(G).Subsingleton
  · exact Or.inr hsub
  · refine Or.inl fun hp => hsub ?_
    exact (isPreconnected_iff_of_edgeSet_eq_empty G.edgeSet_deleteEdges_self).1 hp

/-- `κ(G)` is bounded by the number of vertices. -/
lemma vertexConnectivity_le_encard_vertexSet (G : SimpleGraph α) :
    κ(G) ≤ V(G).encard :=
  vertexConnectivity_le_encard G.isVertexSeparating_vertexSet

/-- `κ'(G)` is bounded by the number of edges. -/
lemma edgeConnectivity_le_encard_edgeSet (G : SimpleGraph α) : κ'(G) ≤ E(G).encard :=
  edgeConnectivity_le_encard G.isEdgeSeparating_edgeSet

/-- `κ(G)` is attained: some vertex-separating set has exactly that size. -/
theorem vertexConnectivity_exists (G : SimpleGraph α) :
    ∃ S : Set α, G.IsVertexSeparating S ∧ S.encard = κ(G) := by
  have hne : Nonempty {S : Set α // G.IsVertexSeparating S} :=
    nonempty_subtype.mpr ⟨V(G), G.isVertexSeparating_vertexSet⟩
  obtain ⟨S, hS⟩ := @ENat.exists_eq_iInf _ hne fun S => S.val.encard
  exact ⟨S.val, S.property, hS.trans iInf_subtype⟩

/-- `κ'(G)` is attained. -/
theorem edgeConnectivity_exists (G : SimpleGraph α) :
    ∃ F : Set (Sym2 α), G.IsEdgeSeparating F ∧ F.encard = κ'(G) := by
  have hne : Nonempty {F : Set (Sym2 α) // G.IsEdgeSeparating F} :=
    nonempty_subtype.mpr ⟨E(G), G.isEdgeSeparating_edgeSet⟩
  obtain ⟨F, hF⟩ := @ENat.exists_eq_iInf _ hne fun F => F.val.encard
  exact ⟨F.val, F.property, hF.trans iInf_subtype⟩

/-- On a graph with finitely many vertices the minimizer is a `Finset`. -/
theorem exists_finset_isVertexSeparating_card_eq (G : SimpleGraph α) [Finite V(G)] :
    ∃ S : Finset α, G.IsVertexSeparating ↑S ∧ (S.card : ℕ∞) = κ(G) := by
  obtain ⟨S, hS, hcard⟩ := G.vertexConnectivity_exists
  have hfin : S.Finite := Set.Finite.subset (Set.toFinite V(G)) hS.1
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rwa [hfin.coe_toFinset]
  · rw [← hcard, hfin.encard_eq_coe_toFinset_card]

/-- On a graph with finitely many vertices the edge minimizer is a `Finset`. -/
theorem exists_finset_isEdgeSeparating_card_eq (G : SimpleGraph α) [Finite V(G)] :
    ∃ F : Finset (Sym2 α), G.IsEdgeSeparating ↑F ∧ (F.card : ℕ∞) = κ'(G) := by
  obtain ⟨F, hF, hcard⟩ := G.edgeConnectivity_exists
  have hfin : F.Finite := Set.Finite.subset (SimpleGraph.edgeSet_finite G) hF.1
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rwa [hfin.coe_toFinset]
  · rw [← hcard, hfin.encard_eq_coe_toFinset_card]

/-! ## Degenerate cases -/

/-- A disconnected graph has vertex connectivity zero: the empty set already separates
it. -/
lemma vertexConnectivity_eq_zero_of_not_isPreconnected {G : SimpleGraph α}
    (h : ¬ G.IsPreconnected) : κ(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using vertexConnectivity_le_encard (S := ∅) ⟨Set.empty_subset _, Or.inl (by simpa)⟩

/-- A disconnected graph has edge connectivity zero. -/
lemma edgeConnectivity_eq_zero_of_not_isPreconnected {G : SimpleGraph α}
    (h : ¬ G.IsPreconnected) : κ'(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using edgeConnectivity_le_encard (F := ∅) ⟨Set.empty_subset _, Or.inl (by simpa)⟩

/-- A graph with at most one vertex has vertex connectivity zero. -/
lemma vertexConnectivity_eq_zero_of_subsingleton {G : SimpleGraph α}
    (h : V(G).Subsingleton) : κ(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using vertexConnectivity_le_encard (S := ∅)
    ⟨Set.empty_subset _, Or.inr (by simpa using h)⟩

/-- A graph with at most one vertex has edge connectivity zero. -/
lemma edgeConnectivity_eq_zero_of_subsingleton {G : SimpleGraph α}
    (h : V(G).Subsingleton) : κ'(G) = 0 := by
  refine le_antisymm ?_ (by simp)
  simpa using edgeConnectivity_le_encard (F := ∅) ⟨Set.empty_subset _, Or.inr h⟩

/-- A graph of positive vertex connectivity is connected. -/
lemma isConnected_of_zero_lt_vertexConnectivity {G : SimpleGraph α}
    (h : 0 < κ(G)) : G.IsConnected := by
  refine ⟨?_, ?_⟩
  · rw [Set.nonempty_iff_ne_empty]
    intro hempty
    exact absurd (vertexConnectivity_eq_zero_of_subsingleton
      (by rw [hempty]; exact Set.subsingleton_empty)) h.ne'
  · by_contra hpre
    exact absurd (vertexConnectivity_eq_zero_of_not_isPreconnected hpre) h.ne'

/-! ## The unpatched cut numbers

These are the literal readings of "the least size of a cut". They are recorded for
comparison and are *degenerate on complete graphs*: `Kₙ` has no vertex cut at all, so
`vertexCutNumber Kₙ = ⊤`. Prefer `vertexConnectivity` / `edgeConnectivity`. -/

/-- The least size of a vertex cut of `G`, the literal reading of Definition 3.1.(i).

Degenerate on complete graphs, which have no vertex cut: `vertexCutNumber Kₙ = ⊤`,
whereas `κ(Kₙ) = n - 1`.
The computable counterpart `computeVertexCutNumber` is available in `./Computable.lean`. -/
noncomputable def vertexCutNumber (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (S : Set α) (_ : G.IsVertexCut S), S.encard

/-- The least size of an edge cut of `G`. Degenerate on graphs with at most one vertex,
which have no edge cut.
The computable counterpart `computeEdgeCutNumber` is available in `./Computable.lean`. -/
noncomputable def edgeCutNumber (G : SimpleGraph α) : ℕ∞ :=
  ⨅ (F : Set (Sym2 α)) (_ : G.IsEdgeCut F), F.encard

/-- The patched connectivity is at most the literal cut number: every cut is separating,
so the infimum ranges over a larger family. Equality holds whenever `G` has a cut at all
that is no bigger than the best subsingleton-leaving set — in particular for every
non-complete graph. -/
lemma vertexConnectivity_le_vertexCutNumber (G : SimpleGraph α) :
    κ(G) ≤ G.vertexCutNumber :=
  le_iInf₂ fun _ hS => vertexConnectivity_le_encard_of_isVertexCut hS

/-- The patched edge connectivity is at most the literal edge cut number. -/
lemma edgeConnectivity_le_edgeCutNumber (G : SimpleGraph α) :
    κ'(G) ≤ G.edgeCutNumber :=
  le_iInf₂ fun _ hF => edgeConnectivity_le_encard_of_isEdgeCut hF

/-! ### Attainment, conditionally

Unlike `κ` and `κ'`, the cut numbers range over a family that can be empty — `Kₙ` has no
vertex cut — so attainment needs the existence of a cut as a hypothesis. Note that the
weaker-looking `≠ ⊤` is *not* the right hypothesis: it implies the existence of a cut
(see `exists_isVertexCut_of_vertexCutNumber_ne_top`) but is strictly stronger, since a
graph all of whose cuts are infinite has a cut and cut number `⊤`. -/

/-- The least vertex cut is attained, provided there is a vertex cut. -/
theorem vertexCutNumber_exists {G : SimpleGraph α} (h : ∃ S : Set α, G.IsVertexCut S) :
    ∃ S : Set α, G.IsVertexCut S ∧ S.encard = G.vertexCutNumber := by
  have hne : Nonempty {S : Set α // G.IsVertexCut S} := nonempty_subtype.mpr h
  obtain ⟨S, hS⟩ := @ENat.exists_eq_iInf _ hne fun S => S.val.encard
  exact ⟨S.val, S.property, hS.trans iInf_subtype⟩

/-- The least edge cut is attained, provided there is an edge cut. -/
theorem edgeCutNumber_exists {G : SimpleGraph α}
    (h : ∃ F : Set (Sym2 α), G.IsEdgeCut F) :
    ∃ F : Set (Sym2 α), G.IsEdgeCut F ∧ F.encard = G.edgeCutNumber := by
  have hne : Nonempty {F : Set (Sym2 α) // G.IsEdgeCut F} := nonempty_subtype.mpr h
  obtain ⟨F, hF⟩ := @ENat.exists_eq_iInf _ hne fun F => F.val.encard
  exact ⟨F.val, F.property, hF.trans iInf_subtype⟩

/-- A finite vertex cut number is witnessed by a vertex cut. -/
lemma exists_isVertexCut_of_vertexCutNumber_ne_top {G : SimpleGraph α}
    (h : G.vertexCutNumber ≠ ⊤) : ∃ S : Set α, G.IsVertexCut S := by
  by_contra hcon
  push Not at hcon
  exact h (by simp [vertexCutNumber, hcon])

/-- A finite edge cut number is witnessed by an edge cut. -/
lemma exists_isEdgeCut_of_edgeCutNumber_ne_top {G : SimpleGraph α}
    (h : G.edgeCutNumber ≠ ⊤) : ∃ F : Set (Sym2 α), G.IsEdgeCut F := by
  by_contra hcon
  push Not at hcon
  exact h (by simp [edgeCutNumber, hcon])

end SimpleGraph

end GraphLib
