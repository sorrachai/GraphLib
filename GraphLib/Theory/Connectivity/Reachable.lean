/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Graph.Delete
import GraphLib.Theory.Structures.InSimpleGraph

/-!
# Reachability in a simple graph

Two vertices are *reachable* in `G` when some walk realized in `G` runs from one to the
other. This is the primitive on which the whole connectivity development rests:
connected components are its equivalence classes, and every notion of cut or separator
is the failure of reachability after a deletion.

## Main definitions

* `SimpleGraph.Reachable G u v` — some simple walk realized in `G` runs from `u` to `v`.
* `SimpleGraph.IsPreconnected G` — every two vertices of `G` are reachable.
* `SimpleGraph.IsConnected G` — `G` is preconnected and has at least one vertex.

## Main results

* `SimpleGraph.Reachable.refl`, `.symm`, `.trans` — reachability is an equivalence
  relation on `V(G)`.
* `SimpleGraph.reachableSetoid` — that equivalence relation, bundled.
* `SimpleGraph.Reachable.exists_isSimplePathIn` — a reachability witnessed by a walk is
  witnessed by a path.

## Design choices

* **Walks, not paths, in the definition.** Reachability is stated with `SimpleWalk` so
  that the three equivalence properties are immediate from the existing closure API:
  `IsSimplePathIn.singleton` gives reflexivity, `IsSimpleWalkIn.reverse` symmetry, and
  `IsSimpleWalkIn.glue` transitivity. A `SimplePath`-valued definition would have to
  erase cycles after every gluing, which needs `[DecidableEq α]` — an unacceptable
  hypothesis on a `Prop` that every downstream statement mentions. The path version is
  recovered as a theorem, `Reachable.exists_isSimplePathIn`, which carries the
  decidability assumption only where it is genuinely used.
* **Reflexivity is conditional.** `Reachable G v v` holds precisely for `v ∈ V(G)`: a
  walk realized in `G` has its head in `V(G)`. So reachability is an equivalence
  relation on `V(G)`, not on `α`, and no `IsRefl`/`Equivalence` instance is registered
  at type `α`. The bundled `reachableSetoid` lives on the subtype `V(G)`.
* **Connectedness requires a vertex.** Following the usual convention (and Mathlib),
  `IsConnected` includes non-emptiness, so that a connected graph has exactly one
  connected component. `IsPreconnected` is the non-emptiness-free variant.
-/

variable {α : Type*}

namespace GraphLib

open scoped GraphLib

namespace SimpleGraph

/-! ## Reachability -/

/-- `u` and `v` are *reachable* in `G` when some simple walk realized in `G` runs from
`u` to `v`.

Reachability is reflexive only at vertices of `G`, and relates nothing outside `V(G)`:
the head and tail of a realized walk are always vertices of `G`. -/
@[grind] def Reachable (G : SimpleGraph α) (u v : α) : Prop :=
  ∃ w : SimpleWalk α, G.IsSimpleWalkIn w ∧ w.head = u ∧ w.tail = v

/-! ## The endpoints are vertices -/

/-- The source of a reachability is a vertex of `G`. -/
@[grind →] theorem Reachable.left_mem {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : u ∈ V(G) := by
  obtain ⟨w, hw, rfl, -⟩ := h
  exact IsSimpleWalkIn.head_mem G hw

/-- The target of a reachability is a vertex of `G`. -/
@[grind →] theorem Reachable.right_mem {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : v ∈ V(G) := by
  obtain ⟨w, hw, -, rfl⟩ := h
  exact IsSimpleWalkIn.tail_mem G hw

/-- Nothing outside the vertex set reaches anything. -/
theorem not_reachable_of_not_mem {G : SimpleGraph α} {u v : α} (h : u ∉ V(G)) :
    ¬ G.Reachable u v := fun hr => h hr.left_mem

/-! ## Equivalence properties -/

/-- Reachability is reflexive on `V(G)`, witnessed by the one-vertex walk at `v`. The
hypothesis `v ∈ V(G)` cannot be dropped: see `reachable_self_iff`. -/
theorem Reachable.refl (G : SimpleGraph α) {v : α} (hv : v ∈ V(G)) :
    G.Reachable v v :=
  ⟨(SimplePath.singleton v).val, IsSimplePathIn.singleton G hv, rfl, rfl⟩

/-- Reachability is symmetric: reverse the witnessing walk. -/
@[symm] theorem Reachable.symm {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) : G.Reachable v u := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact ⟨w.reverse, IsSimpleWalkIn.reverse G hw, by simp, by simp⟩

/-- Reachability is transitive: glue the two witnessing walks at their shared vertex. -/
theorem Reachable.trans {G : SimpleGraph α} {u v w : α}
    (h₁ : G.Reachable u v) (h₂ : G.Reachable v w) : G.Reachable u w := by
  obtain ⟨p, hp, rfl, rfl⟩ := h₁
  obtain ⟨q, hq, hqh, rfl⟩ := h₂
  exact ⟨p.glue q hqh.symm, IsSimpleWalkIn.glue G hp hq hqh.symm,
    SimpleWalk.head_glue p q _, SimpleWalk.tail_glue p q _⟩

/-- A vertex reaches itself exactly when it is a vertex of `G`. -/
@[simp] theorem reachable_self_iff {G : SimpleGraph α} {v : α} :
    G.Reachable v v ↔ v ∈ V(G) :=
  ⟨Reachable.left_mem, Reachable.refl G⟩

/-- Reachability is symmetric, as an iff. -/
theorem reachable_comm {G : SimpleGraph α} {u v : α} :
    G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩

/-- Reachability restricted to the vertices of `G` is an equivalence relation. -/
theorem reachable_equivalence (G : SimpleGraph α) :
    Equivalence (fun u v : V(G) => G.Reachable u.1 v.1) :=
  ⟨fun u => Reachable.refl G u.2, Reachable.symm, Reachable.trans⟩

/-- The reachability setoid on the vertices of `G`, whose quotient is the set of
connected components. Reachability is *not* an equivalence relation on all of `α`, so
this is stated on the subtype `V(G)`. -/
def reachableSetoid (G : SimpleGraph α) : Setoid V(G) :=
  ⟨_, reachable_equivalence G⟩

/-! ## Construction and monotonicity -/

/-- Adjacent vertices are reachable, by the length-one walk between them. -/
theorem Adj.reachable {G : SimpleGraph α} {u v : α} (h : G.Adj u v) :
    G.Reachable u v := by
  refine ⟨⟨(VertexSeq.singleton u).cons v, by simpa [VertexSeq.nonstalling] using h.ne⟩,
    ?_, rfl, rfl⟩
  exact IsVertexSeqIn.cons (VertexSeq.singleton u) v
    (IsVertexSeqIn.singleton u h.left_mem) (by simpa using h)

/-- Reachability is monotone under passing to a supergraph. -/
theorem Reachable.mono {G H : SimpleGraph α} {u v : α} (h : H.Reachable u v)
    (hsub : SimpleGraph.subgraphOf H G) : G.Reachable u v := by
  obtain ⟨w, hw, h1, h2⟩ := h
  exact ⟨w, IsSimpleWalkIn.mono G H hw hsub, h1, h2⟩

/-- Reachability survives undeleting edges. -/
theorem Reachable.of_deleteEdges {G : SimpleGraph α} {F : Set (Sym2 α)} {u v : α}
    (h : (G.deleteEdges F).Reachable u v) : G.Reachable u v :=
  h.mono (G.deleteEdges_subgraphOf F)

/-- Reachability survives undeleting vertices. -/
theorem Reachable.of_deleteVertices {G : SimpleGraph α} {S : Set α} {u v : α}
    (h : (G.deleteVertices S).Reachable u v) : G.Reachable u v :=
  h.mono (G.deleteVertices_subgraphOf S)

/-! ## Witnessing by a path -/

/-- A reachability witnessed by a walk is witnessed by a *path*: erasing the detours of
any witnessing walk leaves a path with the same endpoints. -/
theorem Reachable.exists_isSimplePathIn {G : SimpleGraph α} {u v : α}
    (h : G.Reachable u v) :
    ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = u ∧ p.tail = v := by
  classical
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact ⟨SimplePath.cycleErase w, IsSimpleWalkIn.cycleErase G hw,
    VertexSeq.head_cycleErase w.val, VertexSeq.tail_cycleErase w.val⟩

/-- Reachability is exactly reachability by a path. -/
theorem reachable_iff_exists_isSimplePathIn (G : SimpleGraph α) (u v : α) :
    G.Reachable u v ↔ ∃ p : SimplePath α, G.IsSimplePathIn p ∧ p.head = u ∧ p.tail = v :=
  ⟨Reachable.exists_isSimplePathIn, fun ⟨p, hp, h1, h2⟩ => ⟨p.val, hp, h1, h2⟩⟩

/-! ## Connectedness -/

/-- `G` is *preconnected* when every two of its vertices are reachable from each other.
The empty graph is vacuously preconnected; see `IsConnected` for the variant that
rules it out. -/
@[grind] def IsPreconnected (G : SimpleGraph α) : Prop :=
  ∀ u ∈ V(G), ∀ v ∈ V(G), G.Reachable u v

/-- Definition 1.35. `G` is *connected* when it has at least one vertex and every two of
its vertices are joined by a walk in `G`.

Non-emptiness is part of the definition, following the usual convention: it is what makes
a connected graph have exactly one connected component. -/
@[grind] def IsConnected (G : SimpleGraph α) : Prop :=
  V(G).Nonempty ∧ G.IsPreconnected

/-- A connected graph has a vertex. -/
theorem IsConnected.nonempty {G : SimpleGraph α} (h : G.IsConnected) : V(G).Nonempty :=
  h.1

/-- A connected graph is preconnected. -/
theorem IsConnected.isPreconnected {G : SimpleGraph α} (h : G.IsConnected) :
    G.IsPreconnected := h.2

/-- Reachability between two vertices of a preconnected graph. -/
theorem IsPreconnected.reachable {G : SimpleGraph α} (h : G.IsPreconnected) {u v : α}
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) : G.Reachable u v := h u hu v hv

/-- A graph with at most one vertex is preconnected. -/
theorem isPreconnected_of_subsingleton {G : SimpleGraph α} (h : V(G).Subsingleton) :
    G.IsPreconnected := by
  intro u hu v hv
  rw [h hu hv]
  exact Reachable.refl G hv

/-- The empty graph is preconnected but not connected. -/
theorem isPreconnected_of_vertexSet_eq_empty {G : SimpleGraph α} (h : V(G) = ∅) :
    G.IsPreconnected :=
  isPreconnected_of_subsingleton (by rw [h]; exact Set.subsingleton_empty)

/-- Preconnectedness fails exactly when two vertices are mutually unreachable. -/
theorem not_isPreconnected_iff {G : SimpleGraph α} :
    ¬ G.IsPreconnected ↔ ∃ u ∈ V(G), ∃ v ∈ V(G), ¬ G.Reachable u v := by
  simp [IsPreconnected]

/-! ## Edgeless graphs

Deleting *all* the edges of `G` is the extreme case that the edge connectivity `κ'(G)`
has to reason about, so it is worth recording once: without edges, no walk can move. -/

/-- In a graph without edges, every realized vertex sequence stays put. -/
theorem IsVertexSeqIn.head_eq_tail_of_edgeSet_eq_empty {G : SimpleGraph α}
    (h : E(G) = ∅) {w : VertexSeq α} (hw : G.IsVertexSeqIn w) : w.head = w.tail := by
  induction hw with
  | singleton v hv => simp
  | cons w u hw hadj ih =>
    have hmem : s(w.tail, u) ∈ E(G) := hadj
    rw [h] at hmem
    exact absurd hmem (Set.notMem_empty _)

/-- In a graph without edges, reachability is equality on the vertex set. -/
theorem reachable_iff_of_edgeSet_eq_empty {G : SimpleGraph α} (h : E(G) = ∅) {u v : α} :
    G.Reachable u v ↔ u = v ∧ u ∈ V(G) := by
  refine ⟨fun hr => ⟨?_, hr.left_mem⟩, fun h' => h'.1 ▸ Reachable.refl G h'.2⟩
  obtain ⟨w, hw, rfl, rfl⟩ := hr
  exact IsVertexSeqIn.head_eq_tail_of_edgeSet_eq_empty h hw

/-- A graph without edges is preconnected exactly when it has at most one vertex. -/
theorem isPreconnected_iff_of_edgeSet_eq_empty {G : SimpleGraph α} (h : E(G) = ∅) :
    G.IsPreconnected ↔ V(G).Subsingleton := by
  refine ⟨fun hp u hu v hv => ((reachable_iff_of_edgeSet_eq_empty h).1 (hp u hu v hv)).1,
    isPreconnected_of_subsingleton⟩

end SimpleGraph

end GraphLib
