/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Theory.Connectivity.Reachable
import Mathlib.Data.Set.Card

/-!
# Connected components

The connected components of `G` are the equivalence classes of reachability. This file
represents them as sets of vertices and collects the facts that make
"`G` has more than one component" a usable statement.

## Main definitions

* `SimpleGraph.componentOf G v` — the component of `v`: the vertices reachable from `v`.
* `SimpleGraph.components G` — the set of connected components of `G`.
* `SimpleGraph.IsConnectedComponent G C` — `C` is a connected component of `G`.
* `SimpleGraph.numComponents G` — the number of connected components, in `ℕ∞`.

## Main results

* `SimpleGraph.sUnion_components` — the components cover `V(G)`.
* `SimpleGraph.pairwiseDisjoint_components` — distinct components are disjoint.
* `SimpleGraph.isConnected_iff_components_eq_singleton` — `G` is connected exactly when
  it has one component, namely `V(G)`.
* `SimpleGraph.not_isPreconnected_iff_components_nontrivial` — preconnectedness fails
  exactly when there are at least two components.

## Design choices

* **Components are sets of vertices, not a quotient.** `vertexSet` is a `Set α` rather
  than a whole type, so Mathlib's `Quot`-based `ConnectedComponent` would force subtype
  coercions through every statement in this set-based library. Reachability classes as
  `Set α` keep everything first-order. The quotient is still available if wanted, via
  `SimpleGraph.reachableSetoid`.
* **`components` is indexed by `V(G)`, not by `α`.** Indexing by all of `α` would put
  `∅` into `components` whenever `α` has a non-vertex, breaking both
  `pairwiseDisjoint_components` and every component count by exactly one.
* **Counting uses `Set.encard`, never `Set.ncard`.** `Set.ncard` takes the junk value `0`
  on an infinite set, which would make the natural reading of "`G` has more than one
  component" — `1 < G.components.ncard` — *false* for a graph with infinitely many
  components. `Set.encard` is `ℕ∞`-valued and returns `⊤` there, so `numComponents` is
  correct on infinite graphs. Where a bare `Prop` suffices, prefer `Set.Nontrivial` and
  the reachability-level characterizations below, which avoid cardinals altogether.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Components -/

/-- The *connected component* of `v` in `G`: the set of vertices reachable from `v`.

This is empty when `v ∉ V(G)`, since reachability relates nothing outside the vertex
set; see `componentOf_eq_empty_of_not_mem`. -/
def componentOf (G : SimpleGraph α) (v : α) : Set α := {u | G.Reachable v u}

/-- Membership in a component is reachability, by definition. -/
@[simp, grind =] lemma mem_componentOf_iff {G : SimpleGraph α} {u v : α} :
    u ∈ G.componentOf v ↔ G.Reachable v u := Iff.rfl

/-- The set of *connected components* of `G`: the reachability class of each vertex.
Distinct vertices of the same component contribute the same set, so the components
appear exactly once each. -/
def components (G : SimpleGraph α) : Set (Set α) := (fun v => G.componentOf v) '' V(G)

/-- `C` is a *connected component* of `G` when it is the component of some vertex. -/
def IsConnectedComponent (G : SimpleGraph α) (C : Set α) : Prop := C ∈ G.components

/-- The number of connected components of `G`, as an `ℕ∞` — `⊤` when there are infinitely
many. Prefer this to `Set.ncard`, whose junk value `0` on infinite sets makes
"more than one component" statements silently false. -/
noncomputable def numComponents (G : SimpleGraph α) : ℕ∞ := G.components.encard

/-! ## Basic properties of `componentOf` -/

/-- Every vertex lies in its own component. -/
@[grind →] lemma mem_componentOf_self (G : SimpleGraph α) {v : α} (hv : v ∈ V(G)) :
    v ∈ G.componentOf v := Reachable.refl G hv

/-- A component consists of vertices of `G`. -/
lemma componentOf_subset_vertexSet (G : SimpleGraph α) (v : α) :
    G.componentOf v ⊆ V(G) := fun _ h => h.right_mem

/-- Vertices outside `G` have an empty component. -/
lemma componentOf_eq_empty_of_not_mem {G : SimpleGraph α} {v : α} (hv : v ∉ V(G)) :
    G.componentOf v = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => hv h.left_mem

/-- A component is non-empty exactly when its base point is a vertex. -/
lemma componentOf_nonempty_iff {G : SimpleGraph α} {v : α} :
    (G.componentOf v).Nonempty ↔ v ∈ V(G) := by
  refine ⟨fun ⟨_, hu⟩ => hu.left_mem, fun hv => ⟨v, mem_componentOf_self G hv⟩⟩

/-- Reachable vertices have the same component. -/
lemma componentOf_eq_of_reachable {G : SimpleGraph α} {u v : α} (h : G.Reachable u v) :
    G.componentOf u = G.componentOf v :=
  Set.ext fun _ => ⟨fun hw => h.symm.trans hw, fun hw => h.trans hw⟩

/-- Two vertices of `G` have the same component exactly when they are reachable. -/
lemma componentOf_eq_iff_reachable {G : SimpleGraph α} {u v : α} (hu : u ∈ V(G)) :
    G.componentOf u = G.componentOf v ↔ G.Reachable u v := by
  refine ⟨fun h => ?_, componentOf_eq_of_reachable⟩
  have : u ∈ G.componentOf v := h ▸ mem_componentOf_self G hu
  exact this.symm

/-- Every member of a component generates that same component. -/
lemma componentOf_eq_of_mem {G : SimpleGraph α} {u v : α} (h : u ∈ G.componentOf v) :
    G.componentOf u = G.componentOf v :=
  (componentOf_eq_of_reachable h).symm

/-! ## Basic properties of `components` -/

/-- The component of a vertex is a component. -/
lemma componentOf_mem_components (G : SimpleGraph α) {v : α} (hv : v ∈ V(G)) :
    G.componentOf v ∈ G.components := ⟨v, hv, rfl⟩

/-- Components are non-empty: this is why `components` is indexed by `V(G)`. -/
lemma nonempty_of_mem_components {G : SimpleGraph α} {C : Set α} (hC : C ∈ G.components) :
    C.Nonempty := by
  obtain ⟨v, hv, rfl⟩ := hC
  exact ⟨v, mem_componentOf_self G hv⟩

/-- The empty set is never a component. -/
lemma empty_notMem_components (G : SimpleGraph α) : ∅ ∉ G.components := fun h =>
  (nonempty_of_mem_components h).ne_empty rfl

/-- Components consist of vertices of `G`. -/
lemma subset_vertexSet_of_mem_components {G : SimpleGraph α} {C : Set α}
    (hC : C ∈ G.components) : C ⊆ V(G) := by
  obtain ⟨v, -, rfl⟩ := hC
  exact componentOf_subset_vertexSet G v

/-- A component is the component of each of its members. -/
lemma eq_componentOf_of_mem {G : SimpleGraph α} {C : Set α} {v : α}
    (hC : C ∈ G.components) (hv : v ∈ C) : C = G.componentOf v := by
  obtain ⟨u, -, rfl⟩ := hC
  exact (componentOf_eq_of_mem hv).symm

/-- The components cover the vertex set. -/
lemma sUnion_components (G : SimpleGraph α) : ⋃₀ G.components = V(G) := by
  refine Set.Subset.antisymm ?_ fun v hv => ?_
  · rintro v ⟨C, hC, hvC⟩
    exact subset_vertexSet_of_mem_components hC hvC
  · exact ⟨G.componentOf v, componentOf_mem_components G hv, mem_componentOf_self G hv⟩

/-- Distinct components are disjoint. -/
lemma pairwiseDisjoint_components (G : SimpleGraph α) :
    G.components.PairwiseDisjoint id := by
  intro C hC D hD hne
  refine Set.disjoint_left.2 fun v hvC hvD => hne ?_
  rw [eq_componentOf_of_mem hC hvC, eq_componentOf_of_mem hD hvD]

/-- `G` has no components exactly when it has no vertices. -/
@[simp] lemma components_eq_empty_iff {G : SimpleGraph α} :
    G.components = ∅ ↔ V(G) = ∅ := by
  simp [components, Set.image_eq_empty]

/-- A graph with finitely many vertices has finitely many components: they are the image
of the vertex set. -/
lemma components_finite (G : SimpleGraph α) [Finite V(G)] : G.components.Finite :=
  Set.Finite.image _ (Set.toFinite V(G))

/-! ## Components and connectedness -/

/-- In a preconnected graph, every vertex's component is the whole vertex set. -/
lemma componentOf_eq_vertexSet {G : SimpleGraph α} (h : G.IsPreconnected) {v : α}
    (hv : v ∈ V(G)) : G.componentOf v = V(G) :=
  Set.Subset.antisymm (componentOf_subset_vertexSet G v) fun _ hu => h v hv _ hu

/-- Preconnectedness is exactly "every component is everything". -/
lemma isPreconnected_iff_componentOf_eq {G : SimpleGraph α} :
    G.IsPreconnected ↔ ∀ v ∈ V(G), G.componentOf v = V(G) := by
  refine ⟨fun h v hv => componentOf_eq_vertexSet h hv, fun h u hu v hv => ?_⟩
  change v ∈ G.componentOf u
  rw [h u hu]
  exact hv

/-- A connected graph has exactly one component, namely its vertex set. -/
theorem isConnected_iff_components_eq_singleton {G : SimpleGraph α} :
    G.IsConnected ↔ G.components = {V(G)} := by
  constructor
  · rintro ⟨⟨v₀, hv₀⟩, hpre⟩
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact componentOf_eq_vertexSet hpre hv
    · rintro _ rfl
      exact (componentOf_eq_vertexSet hpre hv₀) ▸ componentOf_mem_components G hv₀
  · intro h
    have hne : V(G).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [components_eq_empty_iff.2 hemp] at h
      exact (Set.singleton_ne_empty _) h.symm
    refine ⟨hne, fun u hu v hv => ?_⟩
    have : G.componentOf u = V(G) := by
      have := componentOf_mem_components G hu
      rw [h] at this
      exact this
    change v ∈ G.componentOf u
    rw [this]
    exact hv

/-- Preconnectedness fails exactly when `G` has at least two components. -/
theorem not_isPreconnected_iff_components_nontrivial {G : SimpleGraph α} :
    ¬ G.IsPreconnected ↔ G.components.Nontrivial := by
  constructor
  · intro h
    rw [not_isPreconnected_iff] at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    exact ⟨G.componentOf u, componentOf_mem_components G hu,
      G.componentOf v, componentOf_mem_components G hv,
      fun heq => huv ((componentOf_eq_iff_reachable hu).1 heq)⟩
  · rintro ⟨C, hC, D, hD, hne⟩ hpre
    obtain ⟨u, huC⟩ := nonempty_of_mem_components hC
    obtain ⟨v, hvD⟩ := nonempty_of_mem_components hD
    refine hne ?_
    rw [eq_componentOf_of_mem hC huC, eq_componentOf_of_mem hD hvD]
    exact componentOf_eq_of_reachable
      (hpre u (subset_vertexSet_of_mem_components hC huC) v
        (subset_vertexSet_of_mem_components hD hvD))

/-- A connected graph has exactly one component. -/
lemma numComponents_eq_one_of_isConnected {G : SimpleGraph α} (h : G.IsConnected) :
    G.numComponents = 1 := by
  rw [numComponents, isConnected_iff_components_eq_singleton.1 h, Set.encard_singleton]

/-- The empty graph has no components. -/
@[simp] lemma numComponents_eq_zero_iff {G : SimpleGraph α} :
    G.numComponents = 0 ↔ V(G) = ∅ := by
  rw [numComponents, Set.encard_eq_zero, components_eq_empty_iff]

/-- A graph that is not preconnected has at least two components. -/
lemma one_lt_numComponents_of_not_isPreconnected {G : SimpleGraph α}
    (h : ¬ G.IsPreconnected) : 1 < G.numComponents :=
  Set.one_lt_encard_iff_nontrivial.2 (not_isPreconnected_iff_components_nontrivial.1 h)

end SimpleGraph

end GraphLib
