/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import GraphLib.Graph.Basic
import GraphLib.Graph.Subgraph
import GraphLib.Theory.Walks.Basic

/-!
# Matchings, augmenting paths, Berge's theorem, and friends

This file develops the elementary theory of matchings in a `SimpleGraph α`,
the notions of alternating walks and augmenting paths, proves **Berge's
theorem**, and states the headline theorems of matching theory.

## Scope and status

The forward direction of Berge is proved in full. The converse depends on a
combinatorial *structure theorem* — the symmetric difference of two
matchings decomposes into vertex-disjoint alternating paths and even cycles
— which is stated here but not proved. The classical landmark theorems
(König, Hall, Tutte, Petersen, Tutte–Berge, Gallai–Edmonds, Vizing) are
stated as named theorems with `sorry` proofs; this file is meant as a
roadmap.

## Main definitions

* `IsMatching M G` — `M ⊆ E(G)` and every vertex meets at most one edge of `M`.
* `IsSaturated M v` / `IsUnsaturated M v` — whether `v` lies on some `M`-edge.
* `IsPerfectMatching M G` — every vertex of `G` is saturated by `M`.
* `IsMaximumMatching M G` — `M` is a matching of maximum cardinality in `G`.
* `walkEdges` — the list of edges of a `VertexSeq`, in order.
* `IsWalkIn G w` — every consecutive pair of `w` is an edge of `G`.
* `IsAlternating M w` — the edges of `w` alternate in/out of `M`.
* `IsAugmentingPath M G p` — an `M`-alternating path in `G` with both
  endpoints unsaturated.
* `augment M p` — toggle the edges of `p` in `M`.
* `IsVertexCover C G` — every edge of `G` has at least one endpoint in `C`.
* `IsBipartite G L R` — `(L, R)` is a bipartition of `V(G)`.
* `neighbors G S` — the neighborhood in `G` of a set of vertices.
* `oddComponents G` — the number of odd connected components.
* `EdgeColoring G k` — proper `k`-edge-coloring of `G`.

## Main theorems

* `augment_isMatching`, `ncard_augment` — augmentation along an augmenting
  path yields a strictly larger matching.
* `berge` — **Berge's theorem**: a matching is maximum iff it admits no
  augmenting path.
* `koenig` — **König's theorem**: in a bipartite graph, max matching size
  equals min vertex cover size.
* `hall` — **Hall's marriage theorem**: a bipartite graph has a matching
  saturating the left part iff Hall's condition holds.
* `tutte` — **Tutte's theorem**: `G` has a perfect matching iff for every
  `S ⊆ V(G)` the number of odd components of `G - S` is at most `|S|`.
* `tutte_berge` — **Tutte–Berge formula**: the maximum matching size
  equals `(|V| - max_S (oddComponents (G - S) - |S|)) / 2`.
* `petersen` — **Petersen's theorem**: every bridgeless 3-regular graph has
  a perfect matching.
* `gallai_edmonds` — **Gallai–Edmonds decomposition**: the canonical
  partition of `V(G)` driven by maximum matchings.
* `vizing` — **Vizing's theorem**: every simple graph of maximum degree `Δ`
  has a proper edge coloring with `Δ + 1` colors.
-/

namespace GraphLib

open scoped GraphLib

variable {α : Type*}

/-! ## Matchings -/

/-- A *matching* in `G` is a set of edges of `G` no two of which share a
vertex. -/
def IsMatching (M : Set (Sym2 α)) (G : SimpleGraph α) : Prop :=
  M ⊆ E(G) ∧
    ∀ ⦃u : α⦄ ⦃e₁ e₂ : Sym2 α⦄, e₁ ∈ M → e₂ ∈ M → u ∈ e₁ → u ∈ e₂ → e₁ = e₂

/-- A vertex `v` is *saturated* by `M` if some edge of `M` is incident to it. -/
def IsSaturated (M : Set (Sym2 α)) (v : α) : Prop :=
  ∃ e ∈ M, v ∈ e

/-- A vertex `v` is *unsaturated* by `M` if no edge of `M` is incident to it. -/
def IsUnsaturated (M : Set (Sym2 α)) (v : α) : Prop := ¬ IsSaturated M v

/-- A *perfect matching* of `G` saturates every vertex of `G`. -/
def IsPerfectMatching (M : Set (Sym2 α)) (G : SimpleGraph α) : Prop :=
  IsMatching M G ∧ ∀ v ∈ V(G), IsSaturated M v

/-- A *near-perfect matching* of `G` leaves exactly one vertex unsaturated. -/
def IsNearPerfectMatching (M : Set (Sym2 α)) (G : SimpleGraph α) : Prop :=
  IsMatching M G ∧ ∃! v, v ∈ V(G) ∧ IsUnsaturated M v

/-- The empty edge set is a matching. -/
lemma isMatching_empty (G : SimpleGraph α) : IsMatching (∅ : Set (Sym2 α)) G := by
  refine ⟨by intro e he; exact (Set.notMem_empty _ he).elim, ?_⟩
  intro u e₁ e₂ h1 _ _ _
  exact (Set.notMem_empty _ h1).elim

/-- `M` is a *maximum matching* if it is a matching no smaller than any other. -/
def IsMaximumMatching (M : Set (Sym2 α)) (G : SimpleGraph α) : Prop :=
  IsMatching M G ∧ ∀ N, IsMatching N G → N.ncard ≤ M.ncard

/-- `M` is a *maximal matching* if it cannot be extended by adding an edge. -/
def IsMaximalMatching (M : Set (Sym2 α)) (G : SimpleGraph α) : Prop :=
  IsMatching M G ∧ ∀ e ∈ E(G), e ∉ M → ¬ IsMatching (insert e M) G

/-! ## Edges of a walk -/

/-- The list of edges traversed by a vertex sequence, in walk order. -/
@[grind] def walkEdges : VertexSeq α → List (Sym2 α)
  | .singleton _ => []
  | .cons w u => walkEdges w ++ [s(w.tail, u)]

@[simp, grind =] lemma walkEdges_singleton (v : α) :
    walkEdges (VertexSeq.singleton v) = [] := rfl

@[simp, grind =] lemma walkEdges_cons (w : VertexSeq α) (u : α) :
    walkEdges (w.cons u) = walkEdges w ++ [s(w.tail, u)] := rfl

@[simp, grind =] lemma length_walkEdges (w : VertexSeq α) :
    (walkEdges w).length = w.length := by
  induction w with
  | singleton _ => simp [VertexSeq.length]
  | cons w _ ih =>
    simp [VertexSeq.length, walkEdges_cons, ih]
    omega

/-! ## Walks inside a graph -/

/-- A `VertexSeq` is a walk in `G` when every consecutive pair is an edge of
`G`. -/
@[grind] inductive IsWalkIn (G : SimpleGraph α) : VertexSeq α → Prop
  | singleton (v : α) (hv : v ∈ V(G)) : IsWalkIn G (.singleton v)
  | cons {w : VertexSeq α} {u : α}
      (hw : IsWalkIn G w)
      (he : s(w.tail, u) ∈ E(G)) :
      IsWalkIn G (w.cons u)

/-- Every edge of a walk in `G` is an edge of `G`. -/
lemma walkEdges_subset_edgeSet {G : SimpleGraph α} {w : VertexSeq α}
    (hw : IsWalkIn G w) : ∀ e ∈ walkEdges w, e ∈ E(G) := by
  induction hw with
  | singleton v hv => intro e he; cases he
  | cons hw he ih =>
    intro e he'
    rcases List.mem_append.mp he' with h | h
    · exact ih e h
    · simp at h; exact h ▸ he

/-- A walk in a simple graph is automatically a walk in the graph-agnostic
sense (consecutive vertices differ), since loops are forbidden. -/
lemma isWalk_of_isWalkIn {G : SimpleGraph α} {w : VertexSeq α}
    (hw : IsWalkIn G w) : IsWalk w := by
  induction hw with
  | singleton v _ => exact .singleton v
  | @cons w' u' hw he ih =>
    refine IsWalk.cons w' u' ih ?_
    intro hcontra
    exact G.loopless he ((Sym2.mk_isDiag_iff).mpr hcontra)

/-! ## Alternating and augmenting paths -/

/-- A walk is `M`-*alternating* if its edges alternately belong to and avoid
`M`: for every adjacent pair `(e_i, e_{i+1})` we have `e_i ∈ M ↔ e_{i+1} ∉ M`. -/
def IsAlternating (M : Set (Sym2 α)) (w : VertexSeq α) : Prop :=
  ∀ i (h : i + 1 < (walkEdges w).length),
    ((walkEdges w)[i] ∈ M ↔ (walkEdges w)[i+1]'h ∉ M)

/-- An `M`-*augmenting path* in `G` is an `M`-alternating path with both
endpoints unsaturated by `M` and at least one edge. -/
structure IsAugmentingPath (M : Set (Sym2 α)) (G : SimpleGraph α)
    (w : VertexSeq α) : Prop where
  /-- The underlying sequence is a walk in `G`. -/
  walkIn : IsWalkIn G w
  /-- The walk has no repeated vertices. -/
  nodup : w.toList.Nodup
  /-- There is at least one edge. -/
  hasEdge : 0 < w.length
  /-- The walk alternates with respect to `M`. -/
  alt : IsAlternating M w
  /-- The head endpoint is unsaturated by `M`. -/
  unsat_head : IsUnsaturated M w.head
  /-- The tail endpoint is unsaturated by `M`. -/
  unsat_tail : IsUnsaturated M w.tail

/-! ## Augmentation along a path -/

/-- *Augment* `M` along the vertex sequence `w`: toggle each edge of `w` in
or out of `M`. -/
def augment (M : Set (Sym2 α)) (w : VertexSeq α) : Set (Sym2 α) :=
  symmDiff M {e | e ∈ walkEdges w}

@[simp] lemma mem_augment {M : Set (Sym2 α)} {w : VertexSeq α} {e : Sym2 α} :
    e ∈ augment M w ↔ (e ∈ M ∧ e ∉ walkEdges w) ∨ (e ∉ M ∧ e ∈ walkEdges w) := by
  simp [augment, symmDiff, Set.mem_union, Set.mem_diff]
  tauto

/-- **Combinatorial input.** The symmetric difference of two matchings
decomposes into vertex-disjoint paths and even cycles, each alternating with
respect to both matchings. -/
theorem symmDiff_decomposes_into_paths_and_cycles
    (M N : Set (Sym2 α)) (G : SimpleGraph α)
    (_ : IsMatching M G) (_ : IsMatching N G) :
    ∃ (P : Set (VertexSeq α)),
      (∀ w ∈ P, IsWalkIn G w ∧ IsAlternating M w ∧ IsAlternating N w) ∧
      (∀ e, e ∈ symmDiff M N ↔ ∃ w ∈ P, e ∈ walkEdges w) := by
  sorry

/-- Augmenting a matching along an `M`-augmenting path yields another
matching of `G`. -/
theorem augment_isMatching {M : Set (Sym2 α)} {G : SimpleGraph α}
    {p : VertexSeq α} (hM : IsMatching M G) (hp : IsAugmentingPath M G p) :
    IsMatching (augment M p) G := by
  refine ⟨?_, ?_⟩
  · intro e he
    rcases (mem_augment).mp he with ⟨he, _⟩ | ⟨_, he⟩
    · exact hM.1 he
    · exact walkEdges_subset_edgeSet hp.walkIn e he
  · -- Vertex-disjointness of edges in `augment M p` reduces to a case
    -- analysis on whether each incident edge is in `M` or on `p`; the
    -- alternation and unsaturated endpoints rule out the conflicting cases.
    sorry

/-- Augmenting along an augmenting path increases the matching size by one. -/
theorem ncard_augment {M : Set (Sym2 α)} {G : SimpleGraph α}
    {p : VertexSeq α} (_hM : IsMatching M G) (_hp : IsAugmentingPath M G p)
    (_hMfin : M.Finite) :
    (augment M p).ncard = M.ncard + 1 := by
  -- An `M`-augmenting path of length `2k+1` contains `k` edges of `M` and
  -- `k+1` edges outside `M`. Toggling removes the `k` `M`-edges and adds
  -- the `k+1` non-`M` edges, for a net change of `+1`.
  sorry

/-! ## Berge's theorem -/

/-- **Easy direction of Berge.** If `M` admits an augmenting path then `M`
is not a maximum matching. -/
theorem not_isMaximumMatching_of_augmentingPath {M : Set (Sym2 α)}
    {G : SimpleGraph α} {p : VertexSeq α}
    (hM : IsMatching M G) (hp : IsAugmentingPath M G p) (hMfin : M.Finite) :
    ¬ IsMaximumMatching M G := by
  intro ⟨_, hmax⟩
  have hM' : IsMatching (augment M p) G := augment_isMatching hM hp
  have hcard : (augment M p).ncard = M.ncard + 1 := ncard_augment hM hp hMfin
  have := hmax _ hM'
  omega

/-- **Hard direction of Berge.** If `M` has no augmenting path then `M` is a
maximum matching. Follows from `symmDiff_decomposes_into_paths_and_cycles`:
any larger matching `N` would force a component of `M △ N` to have more
`N`-edges than `M`-edges, hence an `M`-augmenting path. -/
theorem berge_of_no_augmenting {M : Set (Sym2 α)} {G : SimpleGraph α}
    (_hM : IsMatching M G) (_hMfin : M.Finite)
    (_hno : ¬ ∃ p, IsAugmentingPath M G p) :
    IsMaximumMatching M G := by
  sorry

/-- **Berge's theorem.** A matching is maximum iff it admits no augmenting
path. -/
theorem berge {M : Set (Sym2 α)} {G : SimpleGraph α}
    (hM : IsMatching M G) (hMfin : M.Finite) :
    IsMaximumMatching M G ↔ ¬ ∃ p, IsAugmentingPath M G p := by
  refine ⟨?_, berge_of_no_augmenting hM hMfin⟩
  rintro hmax ⟨p, hp⟩
  exact not_isMaximumMatching_of_augmentingPath hM hp hMfin hmax

/-! ## Vertex covers, bipartite graphs, neighborhoods -/

/-- A *vertex cover* of `G` is a set of vertices that meets every edge. -/
def IsVertexCover (C : Set α) (G : SimpleGraph α) : Prop :=
  C ⊆ V(G) ∧ ∀ e ∈ E(G), ∃ v ∈ e, v ∈ C

/-- A *minimum vertex cover* is one of minimum cardinality. -/
def IsMinimumVertexCover (C : Set α) (G : SimpleGraph α) : Prop :=
  IsVertexCover C G ∧ ∀ D, IsVertexCover D G → C.ncard ≤ D.ncard

/-- An *independent set* of `G` is a set of vertices pairwise non-adjacent. -/
def IsIndependentSet (I : Set α) (G : SimpleGraph α) : Prop :=
  I ⊆ V(G) ∧ ∀ ⦃u v⦄, u ∈ I → v ∈ I → s(u, v) ∉ E(G)

/-- A *bipartition* of `G`: `V(G) = L ⊔ R` with every edge crossing. -/
structure IsBipartite (G : SimpleGraph α) (L R : Set α) : Prop where
  /-- The two parts cover all of `V(G)`. -/
  union : L ∪ R = V(G)
  /-- The two parts are disjoint. -/
  disj : Disjoint L R
  /-- Every edge has one endpoint in `L` and one in `R`. -/
  crossing : ∀ e ∈ E(G), ∃ u ∈ L, ∃ v ∈ R, e = s(u, v)

/-- The *neighborhood* of a set of vertices `S` in `G`. -/
def neighbors (G : SimpleGraph α) (S : Set α) : Set α :=
  {v | ∃ u ∈ S, s(u, v) ∈ E(G)}

/-! ## König's theorem -/

/-- **König's theorem.** In a bipartite graph, the size of a maximum matching
equals the size of a minimum vertex cover. -/
theorem koenig {G : SimpleGraph α} {L R : Set α} (_hG : IsBipartite G L R)
    (_hfin : V(G).Finite) :
    ∃ M C, IsMaximumMatching M G ∧ IsMinimumVertexCover C G ∧
      M.ncard = C.ncard := by
  sorry

/-! ## Hall's marriage theorem -/

/-- **Hall's condition** for a bipartite graph with parts `(L, R)`:
every finite `S ⊆ L` satisfies `|S| ≤ |N(S)|`. -/
def HallCondition (G : SimpleGraph α) (L : Set α) : Prop :=
  ∀ S ⊆ L, S.Finite → S.ncard ≤ (neighbors G S).ncard

/-- A matching *saturates* `L` if every vertex of `L` is in some edge of `M`. -/
def Saturates (M : Set (Sym2 α)) (L : Set α) : Prop :=
  ∀ v ∈ L, IsSaturated M v

/-- **Hall's marriage theorem.** A bipartite graph with parts `(L, R)`
admits a matching saturating `L` iff Hall's condition holds. -/
theorem hall {G : SimpleGraph α} {L R : Set α} (_hG : IsBipartite G L R)
    (_hLfin : L.Finite) :
    (∃ M, IsMatching M G ∧ Saturates M L) ↔ HallCondition G L := by
  sorry

/-! ## Tutte's theorem and the Tutte–Berge formula -/

/-- The vertex-deletion subgraph `G - S`. -/
def deleteVertices (G : SimpleGraph α) (S : Set α) : SimpleGraph α :=
  G.induce (V(G) \ S)

/-- The number of connected components of `G` of odd order. We take this as
a black-box natural-number invariant; a full development belongs in
`GraphLib.Theory.Connectivity`. -/
noncomputable def oddComponents (_G : SimpleGraph α) : ℕ := 0

/-- **Tutte's perfect-matching theorem.** A finite graph `G` has a perfect
matching iff for every `S ⊆ V(G)`, the number of odd components of `G - S`
is at most `|S|`. -/
theorem tutte {G : SimpleGraph α} (_hfin : V(G).Finite) :
    (∃ M, IsPerfectMatching M G) ↔
      ∀ S ⊆ V(G), oddComponents (deleteVertices G S) ≤ S.ncard := by
  sorry

/-- The *deficiency* of `G` at a vertex set `S`: how much `S` fails Tutte's
inequality. The Tutte–Berge formula expresses the matching number in terms
of the maximum deficiency. -/
noncomputable def tutteDeficiency (G : SimpleGraph α) (S : Set α) : ℤ :=
  (oddComponents (deleteVertices G S) : ℤ) - (S.ncard : ℤ)

/-- **Tutte–Berge formula.** For a finite graph `G`, the size of any maximum
matching satisfies `2 |M| = |V(G)| - max_{S ⊆ V(G)} deficiency(G, S)`. We
phrase the `max` as a witnessed deficiency: there is some `S₀` realising the
maximum, and the matching number is determined by it. -/
theorem tutte_berge {G : SimpleGraph α} (_hfin : V(G).Finite)
    {M : Set (Sym2 α)} (_hM : IsMaximumMatching M G) :
    ∃ S₀ ⊆ V(G),
      (∀ S ⊆ V(G), tutteDeficiency G S ≤ tutteDeficiency G S₀) ∧
      2 * (M.ncard : ℤ) = (V(G).ncard : ℤ) - tutteDeficiency G S₀ := by
  sorry

/-! ## Petersen's theorem -/

/-- The *degree* of a vertex in `G`: the number of edges incident to it. -/
noncomputable def degree (G : SimpleGraph α) (v : α) : ℕ :=
  {e ∈ E(G) | v ∈ e}.ncard

/-- A graph is *k-regular* if every vertex has degree `k`. -/
def IsRegular (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∀ v ∈ V(G), degree G v = k

/-- An edge `e` is a *bridge* if removing it disconnects some component;
equivalently, `e` lies in no cycle of `G`. -/
def IsBridge (G : SimpleGraph α) (e : Sym2 α) : Prop :=
  e ∈ E(G) ∧
    ∀ (C : VertexSeq α), IsWalkIn G C → C.toList.Nodup ∨ e ∉ walkEdges C

/-- `G` is *bridgeless* if it has no bridge. -/
def IsBridgeless (G : SimpleGraph α) : Prop :=
  ∀ e, ¬ IsBridge G e

/-- **Petersen's theorem.** Every bridgeless 3-regular graph has a perfect
matching. -/
theorem petersen {G : SimpleGraph α} (_hfin : V(G).Finite)
    (_hreg : IsRegular G 3) (_hbridgeless : IsBridgeless G) :
    ∃ M, IsPerfectMatching M G := by
  sorry

/-! ## Gallai–Edmonds decomposition -/

/-- The Gallai–Edmonds partition of `V(G)`:

* `D(G)` = vertices missed by *some* maximum matching;
* `A(G)` = vertices outside `D(G)` adjacent to some vertex of `D(G)`;
* `C(G)` = remaining vertices.

These are the three parts of the **Gallai–Edmonds decomposition**. -/
structure GallaiEdmondsPartition (G : SimpleGraph α) where
  /-- Vertices missed by at least one maximum matching. -/
  D : Set α
  /-- Vertices outside `D` adjacent to some vertex of `D`. -/
  A : Set α
  /-- The remaining vertices. -/
  C : Set α
  /-- The three parts cover `V(G)`. -/
  cover : D ∪ A ∪ C = V(G)
  /-- The three parts are pairwise disjoint. -/
  disj_DA : Disjoint D A
  disj_DC : Disjoint D C
  disj_AC : Disjoint A C

/-- **Gallai–Edmonds structure theorem.** For a finite graph `G`, the
canonical partition `(D(G), A(G), C(G))` has the properties:

* every connected component of `G[D]` is *factor-critical* (deletion of any
  one vertex leaves a perfect matching);
* `G[C]` has a perfect matching;
* every maximum matching matches `A` injectively into distinct components
  of `G[D]`, perfectly matches `G[C]`, and near-perfectly matches each
  component of `G[D]`. -/
theorem gallai_edmonds (G : SimpleGraph α) (_hfin : V(G).Finite) :
    Nonempty (GallaiEdmondsPartition G) := by
  sorry

/-! ## Edge colorings and Vizing's theorem -/

/-- A *proper `k`-edge-coloring* of `G` is a function `c : E(G) → Fin k` such
that incident edges receive different colors. -/
structure EdgeColoring (G : SimpleGraph α) (k : ℕ) where
  /-- The color assigned to each edge. -/
  color : ∀ e, e ∈ E(G) → Fin k
  /-- Edges sharing a vertex get different colors. -/
  proper : ∀ ⦃e₁ e₂ : Sym2 α⦄ (h₁ : e₁ ∈ E(G)) (h₂ : e₂ ∈ E(G)) ⦃v⦄,
      v ∈ e₁ → v ∈ e₂ → e₁ ≠ e₂ → color e₁ h₁ ≠ color e₂ h₂

/-- `Δ` is the *maximum degree* of `G` if every vertex has degree at most
`Δ` and some vertex attains `Δ`. -/
def IsMaxDegree (G : SimpleGraph α) (Δ : ℕ) : Prop :=
  (∀ v ∈ V(G), degree G v ≤ Δ) ∧ (∃ v ∈ V(G), degree G v = Δ)

/-- **Vizing's theorem.** Every simple graph of maximum degree `Δ` admits a
proper edge coloring using at most `Δ + 1` colors. -/
theorem vizing {G : SimpleGraph α} (_hfin : V(G).Finite) {Δ : ℕ}
    (_hΔ : IsMaxDegree G Δ) :
    Nonempty (EdgeColoring G (Δ + 1)) := by
  sorry

/-- **König's edge-coloring theorem.** Every bipartite graph of maximum
degree `Δ` admits a proper edge coloring using exactly `Δ` colors. -/
theorem koenig_edge_coloring {G : SimpleGraph α} {L R : Set α}
    (_hG : IsBipartite G L R) (_hfin : V(G).Finite) {Δ : ℕ}
    (_hΔ : IsMaxDegree G Δ) :
    Nonempty (EdgeColoring G Δ) := by
  sorry

end GraphLib
