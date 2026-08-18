/-
Copyright (c) 2026 GraphLib working group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huang.JiangYi (co/ Claude Opus 5)
-/
import GraphLib.Graph.Decidable
import GraphLib.Theory.Connectivity.Connectivity
import GraphLib.Util.Finset

/-!
# The computable connectivity layer

`SimpleGraph.Reachable` is an unbounded existential over walks and `κ(G)` is an infimum
over all subsets of an arbitrary type, so nothing in the connectivity development
computes. This file supplies the executable counterparts, on a graph whose vertex set is
finite as *data* and whose edge set has decidable membership:

* reachability, as a `Finset` closure, and the `Decidable` instances it yields for
  reachability, connectedness, cuts and separating sets;
* the connected components, as a `Finset` of `Finset`s;
* the four connectivity numbers `κ(G)`, `κ'(G)` and the two cut numbers.

Nothing in the `Set` / `ℕ∞`-valued development changes: those definitions are the
specifications, and every definition here is proved *equal* to the one it computes.

## Main definitions

* `SimpleGraph.reachableFinset G u` — the vertices reachable from `u`.
* `SimpleGraph.componentFinset G` — the connected components.
* `SimpleGraph.computeNumComponents G` — their number.
* `SimpleGraph.computeVertexConnectivity G` / `computeEdgeConnectivity G` /
  `computeVertexCutNumber G` / `computeEdgeCutNumber G`.

## Main results

* `SimpleGraph.mem_reachableFinset_iff` — `v ∈ G.reachableFinset u ↔ G.Reachable u v`;
  `SimpleGraph.coe_reachableFinset` identifies the closure with `componentOf`.
* `SimpleGraph.numComponents_eq_card` and `SimpleGraph.computeNumComponents_eq`.
* `SimpleGraph.computeVertexConnectivity_eq` — `= κ(G)`; likewise for the other three.
* `Decidable` instances for `Reachable`, `IsPreconnected`, `IsConnected`, `IsVertexCut`,
  `IsEdgeCut`, `IsVertexSeparating`, `IsEdgeSeparating`, `IsConnectedComponent`.

## Design choices

* **Iteration, not recursion.** `reachableFinset` iterates one breadth-first layer
  `|V(G)| + 1` times rather than recursing to a fixed point. There is then no
  termination obligation, no equation compiler, and the definition reduces, so `#eval`
  and `decide` work. Correctness rests on `Finset.iterate_isFixed_of_inflationary`
  (`GraphLib.Util.Finset`): the iterate *is* a fixed point, hence closed under
  adjacency, and completeness follows by induction on the `IsVertexSeqIn` derivation of
  the witnessing walk — with no bound on its length, hence no `loopErase` and no
  `[DecidableEq α]` inside a `Prop`, which is what
  `GraphLib.Theory.Connectivity.Reachable` set out to avoid.
* **One generic bridge for all four numbers.** Each connectivity number is an infimum of
  `Set.encard` over sets that are, by the first conjunct of their defining predicate,
  contained in `V(G)` or `E(G)`. `Set.iInf_encard_eq_minENat_powerset` turns exactly that
  shape into a minimum over a filtered powerset, so each of the four agreement
  theorems is a one-line corollary and the `⊤` convention is preserved on the nose
  (`vertexCutNumber Kₙ = ⊤` because `Kₙ` has no vertex cut).
* **Complexity.** `reachableFinset` runs `|V(G)| + 1` layers even after stabilizing, and
  the connectivity numbers enumerate all `2^|V(G)|` subsets, testing preconnectedness of
  a deleted graph for each. This is a *specification that computes*, not an algorithm:
  `decide` is realistic up to about six vertices. See `GraphAlgorithms` for real BFS.
-/

namespace GraphLib

variable {α : Type*}

open scoped GraphLib

namespace SimpleGraph

variable {G : SimpleGraph α} [DecidableEq α] [Fintype G.vertexSet]
  [DecidablePred (· ∈ G.edgeSet)]

/-! ## One breadth-first layer

`reachStep` and `reachStart` are the construction; the exported contract is
`reachableFinset` together with `mem_reachableFinset_iff`. -/

/-- One layer of breadth-first search: adjoin every neighbour of a vertex of `T`. -/
private def reachStep (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (T : Finset α) : Finset α :=
  T ∪ T.biUnion G.computeNeighborFinset

private lemma mem_reachStep {T : Finset α} {v : α} :
    v ∈ G.reachStep T ↔ v ∈ T ∨ ∃ w ∈ T, G.Adj w v := by
  simp [reachStep, Finset.mem_biUnion]

private lemma subset_reachStep (T : Finset α) : T ⊆ G.reachStep T :=
  Finset.subset_union_left

private lemma reachStep_subset {T : Finset α} (hT : T ⊆ G.computeVertexFinset) :
    G.reachStep T ⊆ G.computeVertexFinset :=
  Finset.union_subset hT
    (Finset.biUnion_subset.2 fun w _ => G.computeNeighborFinset_subset w)

/-- The start set of the search from `u`: the singleton `{u}` if `u` is a vertex of `G`,
and `∅` otherwise — nothing outside `V(G)` reaches anything. -/
private def reachStart (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (u : α) : Finset α :=
  if u ∈ G.computeVertexFinset then {u} else ∅

private lemma mem_reachStart {u v : α} : v ∈ G.reachStart u ↔ v = u ∧ u ∈ V(G) := by
  unfold reachStart
  split_ifs with h <;> simp_all

private lemma reachStart_subset (u : α) : G.reachStart u ⊆ G.computeVertexFinset := by
  unfold reachStart
  split_ifs with h <;> simp [h]

/-! ## The reachability closure -/

/-- The vertices reachable from `u`, as a `Finset`: iterate one breadth-first layer from
`{u}` often enough to reach a fixed point. -/
def reachableFinset (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] (u : α) : Finset α :=
  (G.reachStep)^[G.computeVertexFinset.card + 1] (G.reachStart u)

lemma reachableFinset_subset (u : α) : G.reachableFinset u ⊆ G.computeVertexFinset :=
  Finset.iterate_subset (fun _ h => reachStep_subset h) (reachStart_subset u) _

lemma self_mem_reachableFinset {u : α} (hu : u ∈ V(G)) : u ∈ G.reachableFinset u :=
  Finset.subset_iterate (fun _ => subset_reachStep _) _ (mem_reachStart.2 ⟨rfl, hu⟩)

/-- The closure is a fixed point of the search step: this is the stabilization argument,
and it is what makes the closure closed under adjacency. -/
private lemma reachStep_reachableFinset (u : α) :
    G.reachStep (G.reachableFinset u) = G.reachableFinset u :=
  Finset.iterate_isFixed_of_inflationary (fun _ => subset_reachStep _)
    (fun _ h => reachStep_subset h) (reachStart_subset u)

lemma mem_reachableFinset_of_adj {u v w : α} (hw : w ∈ G.reachableFinset u)
    (hadj : G.Adj w v) : v ∈ G.reachableFinset u := by
  rw [← reachStep_reachableFinset u, mem_reachStep]
  exact Or.inr ⟨w, hw, hadj⟩

/-! ## Correctness -/

private lemma reachable_of_mem_iterate {u : α} :
    ∀ (n : ℕ) (v : α), v ∈ (G.reachStep)^[n] (G.reachStart u) → G.Reachable u v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    rw [Function.iterate_zero, id_eq, mem_reachStart] at hv
    obtain ⟨rfl, hu⟩ := hv
    exact Reachable.refl G hu
  | succ n ih =>
    intro v hv
    rw [Function.iterate_succ_apply', mem_reachStep] at hv
    rcases hv with hv | ⟨w, hw, hadj⟩
    · exact ih v hv
    · exact (ih w hw).trans hadj.reachable

lemma reachable_of_mem_reachableFinset {u v : α} (h : v ∈ G.reachableFinset u) :
    G.Reachable u v :=
  reachable_of_mem_iterate _ v h

private lemma mem_reachableFinset_of_isVertexSeqIn {u : α} :
    ∀ {w : VertexSeq α}, G.IsVertexSeqIn w → w.head = u →
      w.tail ∈ G.reachableFinset u := by
  intro w hw
  induction hw with
  | singleton x hx =>
    intro hhead
    simp only [VertexSeq.head_singleton] at hhead
    subst hhead
    exact self_mem_reachableFinset (by simpa using hx)
  | cons w x hw hadj ih =>
    intro hhead
    rw [VertexSeq.head_cons] at hhead
    exact mem_reachableFinset_of_adj (ih hhead) hadj

lemma mem_reachableFinset_of_reachable {u v : α} (h : G.Reachable u v) :
    v ∈ G.reachableFinset u := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact mem_reachableFinset_of_isVertexSeqIn hw rfl

/-- The computable closure is exactly the set of vertices reachable from `u`. -/
@[simp] lemma mem_reachableFinset_iff {u v : α} :
    v ∈ G.reachableFinset u ↔ G.Reachable u v :=
  ⟨reachable_of_mem_reachableFinset, mem_reachableFinset_of_reachable⟩

/-- The closure, as a set, is the connected component of `u`. -/
@[simp] lemma coe_reachableFinset (u : α) :
    (G.reachableFinset u : Set α) = G.componentOf u := by
  ext v
  simp [componentOf]

/-- Reachability is decidable. -/
instance instDecidableReachable (u v : α) : Decidable (G.Reachable u v) :=
  decidable_of_iff _ mem_reachableFinset_iff

/-! ## Connectedness -/

lemma isPreconnected_iff_forall_subset :
    G.IsPreconnected ↔
      ∀ u ∈ G.computeVertexFinset, G.computeVertexFinset ⊆ G.reachableFinset u := by
  simp [IsPreconnected, Finset.subset_iff]

instance instDecidableIsPreconnected : Decidable G.IsPreconnected :=
  decidable_of_iff _ isPreconnected_iff_forall_subset.symm

/-- One search suffices: if `u` is a vertex, preconnectedness is the single statement
that everything is reachable from `u`. -/
lemma isPreconnected_iff_of_mem {u : α} (hu : u ∈ V(G)) :
    G.IsPreconnected ↔ G.computeVertexFinset ⊆ G.reachableFinset u := by
  rw [isPreconnected_iff_forall_subset]
  refine ⟨fun h => h u (by simpa using hu), fun h w hw v hv => ?_⟩
  have hw' : G.Reachable u w := by simpa using h hw
  have hv' : G.Reachable u v := by simpa using h hv
  simpa using hw'.symm.trans hv'

omit [DecidablePred (· ∈ G.edgeSet)] in
lemma nonempty_vertexSet_iff : V(G).Nonempty ↔ G.computeVertexFinset.Nonempty := by
  simp [Set.Nonempty, Finset.Nonempty]

instance instDecidableIsConnected : Decidable G.IsConnected :=
  decidable_of_iff (G.computeVertexFinset.Nonempty ∧ G.IsPreconnected)
    (by rw [IsConnected, nonempty_vertexSet_iff])

/-! ## Cuts and separators -/

section Cuts

variable {S : Set α} [Fintype S] [DecidablePred (· ∈ S)]
  {F : Set (Sym2 α)} [Fintype F] [DecidablePred (· ∈ F)]

instance instDecidableIsVertexCut : Decidable (G.IsVertexCut S) :=
  decidable_of_iff (S ⊆ V(G) ∧ ¬ (G.deleteVertices S).IsPreconnected) Iff.rfl

instance instDecidableIsEdgeCut : Decidable (G.IsEdgeCut F) :=
  decidable_of_iff (F ⊆ E(G) ∧ ¬ (G.deleteEdges F).IsPreconnected) Iff.rfl

instance instDecidableIsVertexSeparating : Decidable (G.IsVertexSeparating S) :=
  decidable_of_iff
    (S ⊆ V(G) ∧ (¬ (G.deleteVertices S).IsPreconnected ∨ (V(G) \ S).Subsingleton))
    Iff.rfl

instance instDecidableIsEdgeSeparating : Decidable (G.IsEdgeSeparating F) :=
  decidable_of_iff
    (F ⊆ E(G) ∧ (¬ (G.deleteEdges F).IsPreconnected ∨ V(G).Subsingleton)) Iff.rfl

instance instDecidableIsCutVertex (v : α) : Decidable (G.IsCutVertex v) :=
  decidable_of_iff (G.IsVertexCut {v}) Iff.rfl

instance instDecidableIsCutEdge (e : Sym2 α) : Decidable (G.IsCutEdge e) :=
  decidable_of_iff (G.IsEdgeCut {e}) Iff.rfl

end Cuts

/-! ## Connected components -/

/-- The connected components of `G`, as a `Finset` of `Finset`s.

`Finset (Finset α)` rather than `Finset (Set α)`: forming the image needs `DecidableEq`
on the target, which `Set α` does not have. The price is that the comparison with
`components` goes through the coercion `Finset α → Set α`; see
`componentFinset_image_coe_eq_components`. -/
def componentFinset (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : Finset (Finset α) :=
  G.computeVertexFinset.image G.reachableFinset

@[simp] lemma mem_componentFinset {C : Finset α} :
    C ∈ G.componentFinset ↔ ∃ v ∈ V(G), G.reachableFinset v = C := by
  simp [componentFinset, Finset.mem_image]

/-- The components, viewed through the coercion `Finset α → Set α`, are exactly
`G.components`. -/
theorem componentFinset_image_coe_eq_components :
    (fun s : Finset α => (↑s : Set α)) '' (G.componentFinset : Set (Finset α))
      = G.components := by
  rw [componentFinset, Finset.coe_image, Set.image_image, coe_computeVertexFinset]
  simp [components, componentOf]

/-- The number of connected components of `G`. -/
def computeNumComponents (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : ℕ :=
  G.componentFinset.card

/-- The specification `numComponents` counts a set of *sets*, the computable version a
`Finset` of *finsets*; they agree because the coercion `Finset α → Set α` is injective,
so the image loses nothing. -/
theorem numComponents_eq_card : G.numComponents = (G.componentFinset.card : ℕ∞) := by
  rw [numComponents, ← componentFinset_image_coe_eq_components,
    Function.Injective.encard_image Finset.coe_injective,
    Set.encard_coe_eq_coe_finsetCard]

theorem computeNumComponents_eq : (G.computeNumComponents : ℕ∞) = G.numComponents :=
  numComponents_eq_card.symm

lemma isConnectedComponent_iff {C : Set α} [Fintype C] :
    G.IsConnectedComponent C ↔
      ∃ v ∈ G.computeVertexFinset, G.reachableFinset v = C.toFinset := by
  simp only [IsConnectedComponent, components, Set.mem_image, mem_computeVertexFinset]
  refine exists_congr fun v => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · exact Finset.coe_injective (by rw [coe_reachableFinset, Set.coe_toFinset, h])
  · rw [← coe_reachableFinset v, h, Set.coe_toFinset]

instance instDecidableIsConnectedComponent (C : Set α) [Fintype C] :
    Decidable (G.IsConnectedComponent C) :=
  decidable_of_iff _ isConnectedComponent_iff.symm

/-! ## The connectivity numbers

Each of the four is the least size of a set with a property whose first conjunct bounds
that set inside `V(G)` or `E(G)`, so each is an instance of the same bridge lemma
`Set.iInf_encard_eq_minENat_powerset`. -/

/-- The vertex connectivity `κ(G)`, computed by minimizing over all vertex subsets. -/
def computeVertexConnectivity (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : ℕ∞ :=
  ((G.computeVertexFinset.powerset.filter fun S : Finset α =>
    G.IsVertexSeparating ↑S).image Finset.card).minENat

/-- The edge connectivity `κ'(G)`, computed by minimizing over all edge subsets. -/
def computeEdgeConnectivity (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : ℕ∞ :=
  ((G.computeEdgeFinset.powerset.filter fun F : Finset (Sym2 α) =>
    G.IsEdgeSeparating ↑F).image Finset.card).minENat

/-- The least size of a vertex cut, computed; `⊤` when `G` has no vertex cut. -/
def computeVertexCutNumber (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : ℕ∞ :=
  ((G.computeVertexFinset.powerset.filter fun S : Finset α =>
    G.IsVertexCut ↑S).image Finset.card).minENat

/-- The least size of an edge cut, computed; `⊤` when `G` has no edge cut. -/
def computeEdgeCutNumber (G : SimpleGraph α) [DecidableEq α] [Fintype G.vertexSet]
    [DecidablePred (· ∈ G.edgeSet)] : ℕ∞ :=
  ((G.computeEdgeFinset.powerset.filter fun F : Finset (Sym2 α) =>
    G.IsEdgeCut ↑F).image Finset.card).minENat

theorem computeVertexConnectivity_eq : G.computeVertexConnectivity = κ(G) :=
  (Set.iInf_encard_eq_minENat_powerset G.computeVertexFinset G.IsVertexSeparating
    fun _ hS => by rw [coe_computeVertexFinset]; exact hS.1).symm

theorem computeEdgeConnectivity_eq : G.computeEdgeConnectivity = κ'(G) :=
  (Set.iInf_encard_eq_minENat_powerset G.computeEdgeFinset G.IsEdgeSeparating
    fun _ hF => by rw [coe_computeEdgeFinset]; exact hF.1).symm

theorem computeVertexCutNumber_eq : G.computeVertexCutNumber = G.vertexCutNumber :=
  (Set.iInf_encard_eq_minENat_powerset G.computeVertexFinset G.IsVertexCut
    fun _ hS => by rw [coe_computeVertexFinset]; exact hS.1).symm

theorem computeEdgeCutNumber_eq : G.computeEdgeCutNumber = G.edgeCutNumber :=
  (Set.iInf_encard_eq_minENat_powerset G.computeEdgeFinset G.IsEdgeCut
    fun _ hF => by rw [coe_computeEdgeFinset]; exact hF.1).symm

/-! ## Smoke tests

Concrete evaluation on two small graphs, confirming that the definitions really do
reduce in the kernel. The `Fintype` and `DecidablePred` instances have to be given by
hand: instance search does not unfold the `def` of a concrete graph to reach the set
literals inside it. -/

section Examples

/-- The path `0 - 1 - 2`. -/
private def pathG : SimpleGraph (Fin 3) where
  vertexSet := {0, 1, 2}
  edgeSet := {s(0, 1), s(1, 2)}
  incidence' := by decide
  loopless' := by decide

private instance : Fintype pathG.vertexSet :=
  inferInstanceAs (Fintype ({0, 1, 2} : Set (Fin 3)))

private instance : DecidablePred (· ∈ pathG.edgeSet) :=
  inferInstanceAs (DecidablePred (· ∈ ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))))

example : pathG.reachableFinset 0 = {0, 1, 2} := by decide
example : pathG.IsConnected := by decide
example : pathG.IsCutVertex 1 := by decide
example : ¬ pathG.IsCutVertex 0 := by decide
example : pathG.computeNumComponents = 1 := by decide

-- Removing the middle vertex, or either edge, disconnects a path.
example : pathG.computeVertexConnectivity = 1 := by decide
example : pathG.computeEdgeConnectivity = 1 := by decide
example : pathG.computeVertexCutNumber = 1 := by decide

-- …and therefore `κ(pathG) = 1`, through the agreement theorem.
example : κ(pathG) = 1 := by
  rw [← computeVertexConnectivity_eq]; decide

/-- The path `0 - 1 - 2` together with an isolated vertex `3`. -/
private def splitG : SimpleGraph (Fin 4) where
  vertexSet := {0, 1, 2, 3}
  edgeSet := {s(0, 1), s(1, 2)}
  incidence' := by decide
  loopless' := by decide

private instance : Fintype splitG.vertexSet :=
  inferInstanceAs (Fintype ({0, 1, 2, 3} : Set (Fin 4)))

private instance : DecidablePred (· ∈ splitG.edgeSet) :=
  inferInstanceAs (DecidablePred (· ∈ ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 4)))))

example : splitG.reachableFinset 3 = {3} := by decide
example : ¬ splitG.Reachable 0 3 := by decide
example : ¬ splitG.IsPreconnected := by decide
example : splitG.computeNumComponents = 2 := by decide

-- A disconnected graph is separated by the empty set.
example : splitG.computeVertexConnectivity = 0 := by decide
example : κ(splitG) = 0 := by
  rw [← computeVertexConnectivity_eq]; decide

end Examples

end SimpleGraph

end GraphLib
