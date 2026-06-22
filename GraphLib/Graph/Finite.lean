/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sym.Card
import GraphLib.Graph.Basic

/-!
# Finiteness of graphs

When the vertex set of a graph is finite, the edge set is finite as well.
This file packages those facts together with `Finset` versions of the
vertex and edge sets, and basic cardinality bounds.

The intended ergonomics: *the only finiteness assumption a user should ever
need to write is `[Finite V(G)]`* (equivalently `[Finite G.vertexSet]`).
All downstream `Finite` / `Fintype` / `Finset` instances and bookkeeping
flow from there as `instance`s registered in this file.

## Main results

* `SimpleGraph.vertexFinset` / `SimpleDiGraph.vertexFinset` — the vertex
  set as a `Finset`.
* `SimpleGraph.edgeFinset` / `SimpleDiGraph.edgeFinset` — the edge set
  as a `Finset`.
* `Finite` instances: `Finite G.edgeSet` from `Finite G.vertexSet`, for
  both `SimpleGraph` and `SimpleDiGraph`.
* `Fintype` instances on `vertexSet` and `edgeSet` (classical, via
  `Fintype.ofFinite`).
* `SimpleGraph.card_edgeFinset_le_card_choose_two` — `|E(G)| ≤ C(|V(G)|, 2)`.
* `SimpleDiGraph.card_edgeFinset_le_two_card_choose_two` —
  `|E(G)| ≤ 2·C(|V(G)|, 2)`.
-/

namespace GraphLib

open scoped GraphLib

variable {α : Type*}

/-! ## Finiteness instances for edge sets -/

/-- The `{e : Sym2 α | ∀ v ∈ e, v ∈ S}` set is finite whenever `S` is. -/
private lemma sym2_of_subset_finite (S : Set α) (hS : S.Finite) :
    {e : Sym2 α | ∀ v ∈ e, v ∈ S}.Finite := by
  classical
  have hfin : Finite S := hS
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype (Sym2 S) := inferInstance
  -- The set is contained in the image of `Sym2 S` under `Subtype.val`.
  refine Set.Finite.subset (Set.toFinite (Sym2.map (Subtype.val : S → α) '' Set.univ)) ?_
  intro e he
  induction e with
  | h x y =>
    refine ⟨s(⟨x, he x ?_⟩, ⟨y, he y ?_⟩), trivial, by simp [Sym2.map_mk]⟩ <;> simp

/-- Finiteness of the vertex set transfers to the edge set. -/
instance SimpleGraph.instFiniteEdgeSet (G : SimpleGraph α) [hfin : Finite G.vertexSet] :
    Finite G.edgeSet := by
  have hVfin : G.vertexSet.Finite := hfin
  have hsubset : G.edgeSet ⊆ {e : Sym2 α | ∀ v ∈ e, v ∈ G.vertexSet} :=
    fun e he v hv => G.incidence' e he v hv
  exact ((sym2_of_subset_finite G.vertexSet hVfin).subset hsubset).to_subtype

/-- Finiteness of the vertex set transfers to the edge set. -/
instance SimpleDiGraph.instFiniteEdgeSet (G : SimpleDiGraph α) [hfin : Finite G.vertexSet] :
    Finite G.edgeSet := by
  classical
  haveI : Fintype G.vertexSet := Fintype.ofFinite _
  haveI : Fintype (G.vertexSet × G.vertexSet) := inferInstance
  apply Finite.of_injective (β := G.vertexSet × G.vertexSet) fun e =>
    (⟨e.val.1, (G.incidence' _ e.property).1⟩,
     ⟨e.val.2, (G.incidence' _ e.property).2⟩)
  rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨c, d⟩, hc⟩ heq
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
  apply Subtype.ext
  ext <;> [exact heq.1; exact heq.2]

/-- Backwards-compatible named form. -/
theorem SimpleGraph.fin_vertexSet_fin_edgeSet (G : SimpleGraph α)
    (hfin : Finite G.vertexSet) : Finite G.edgeSet :=
  G.instFiniteEdgeSet

/-- Backwards-compatible named form. -/
theorem SimpleDiGraph.fin_vertexSet_fin_edgeSet (G : SimpleDiGraph α)
    (hfin : Finite G.vertexSet) : Finite G.edgeSet :=
  G.instFiniteEdgeSet

/-! ## Vertex finset -/

/-- The vertex set of `G` as a `Finset`, when it is finite. -/
noncomputable def SimpleGraph.vertexFinset (G : SimpleGraph α) [Finite G.vertexSet] :
    Finset α :=
  (Set.toFinite G.vertexSet).toFinset

/-- The vertex set of `G` as a `Finset`, when it is finite. -/
noncomputable def SimpleDiGraph.vertexFinset (G : SimpleDiGraph α) [Finite G.vertexSet] :
    Finset α :=
  (Set.toFinite G.vertexSet).toFinset

@[simp] lemma SimpleGraph.mem_vertexFinset (G : SimpleGraph α) [Finite G.vertexSet]
    {v : α} : v ∈ G.vertexFinset ↔ v ∈ G.vertexSet := by
  simp [vertexFinset]

@[simp] lemma SimpleDiGraph.mem_vertexFinset (G : SimpleDiGraph α) [Finite G.vertexSet]
    {v : α} : v ∈ G.vertexFinset ↔ v ∈ G.vertexSet := by
  simp [vertexFinset]

@[simp] lemma SimpleGraph.coe_vertexFinset (G : SimpleGraph α) [Finite G.vertexSet] :
    (G.vertexFinset : Set α) = G.vertexSet := by
  ext; simp

@[simp] lemma SimpleDiGraph.coe_vertexFinset (G : SimpleDiGraph α) [Finite G.vertexSet] :
    (G.vertexFinset : Set α) = G.vertexSet := by
  ext; simp

/-! ## Edge finset -/

/-- The edge set of `G` as a `Finset`. -/
noncomputable def SimpleGraph.edgeFinset (G : SimpleGraph α) [Finite G.vertexSet] :
    Finset (Sym2 α) :=
  (Set.toFinite G.edgeSet).toFinset

/-- The edge set of `G` as a `Finset`. -/
noncomputable def SimpleDiGraph.edgeFinset (G : SimpleDiGraph α) [Finite G.vertexSet] :
    Finset (α × α) :=
  (Set.toFinite G.edgeSet).toFinset

@[simp] lemma SimpleGraph.mem_edgeFinset (G : SimpleGraph α) [Finite G.vertexSet]
    {e : Sym2 α} : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet := by
  simp [edgeFinset]

@[simp] lemma SimpleDiGraph.mem_edgeFinset (G : SimpleDiGraph α) [Finite G.vertexSet]
    {e : α × α} : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet := by
  simp [edgeFinset]

@[simp] lemma SimpleGraph.coe_edgeFinset (G : SimpleGraph α) [Finite G.vertexSet] :
    (G.edgeFinset : Set (Sym2 α)) = G.edgeSet := by
  ext; simp

@[simp] lemma SimpleDiGraph.coe_edgeFinset (G : SimpleDiGraph α) [Finite G.vertexSet] :
    (G.edgeFinset : Set (α × α)) = G.edgeSet := by
  ext; simp

/-! ## Convenience: ncard and Set.Finite from Finset cardinalities -/

@[simp] lemma SimpleGraph.ncard_vertexSet (G : SimpleGraph α) [Finite G.vertexSet] :
    Set.ncard G.vertexSet = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]; rfl

@[simp] lemma SimpleDiGraph.ncard_vertexSet (G : SimpleDiGraph α) [Finite G.vertexSet] :
    Set.ncard G.vertexSet = G.vertexFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]; rfl

@[simp] lemma SimpleGraph.ncard_edgeSet (G : SimpleGraph α) [Finite G.vertexSet] :
    Set.ncard G.edgeSet = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]; rfl

@[simp] lemma SimpleDiGraph.ncard_edgeSet (G : SimpleDiGraph α) [Finite G.vertexSet] :
    Set.ncard G.edgeSet = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]; rfl

/-! ## Cardinality bounds -/

/-- The vertex finset cardinality equals the `Fintype.card` of the vertex
subtype. -/
private lemma SimpleGraph.vertexFinset_card_eq (G : SimpleGraph α) [Finite G.vertexSet]
    [Fintype G.vertexSet] :
    G.vertexFinset.card = Fintype.card G.vertexSet := by
  change ((Set.toFinite (G.vertexSet)).toFinset).card = Fintype.card G.vertexSet
  exact (Set.toFinite G.vertexSet).card_toFinset

/-- Lift an edge of `G` to a non-diagonal `Sym2` on the vertex subtype. -/
private lemma SimpleGraph.edge_lift (G : SimpleGraph α) {e : Sym2 α} (he : e ∈ G.edgeSet) :
    ∃ s : Sym2 G.vertexSet, ¬ s.IsDiag ∧ s.map Subtype.val = e := by
  induction e with
  | h x y =>
    refine ⟨s(⟨x, G.incidence' _ he x (by simp)⟩,
              ⟨y, G.incidence' _ he y (by simp)⟩), ?_, by simp [Sym2.map_mk]⟩
    have hne : ¬ (s(x, y) : Sym2 α).IsDiag := G.loopless' _ he
    simp only [Sym2.mk_isDiag_iff, Subtype.ext_iff] at hne ⊢
    exact hne

/-- The edge set of a simple graph has size at most `C(|V|, 2)`.
The proof embeds `E(G)` into the off-diagonal `Sym2` of the vertex set. -/
theorem SimpleGraph.card_edgeFinset_le_card_choose_two
    (G : SimpleGraph α) [Finite G.vertexSet] :
    G.edgeFinset.card ≤ G.vertexFinset.card.choose 2 := by
  classical
  haveI : Fintype G.vertexSet := Fintype.ofFinite _
  -- Build the injection `E(G) ↪ {s : Sym2 V(G) // ¬ s.IsDiag}`.
  let f : G.edgeFinset → {s : Sym2 G.vertexSet // ¬ s.IsDiag} := fun e =>
    ⟨(G.edge_lift (G.mem_edgeFinset.mp e.property)).choose,
     (G.edge_lift (G.mem_edgeFinset.mp e.property)).choose_spec.1⟩
  have f_inj : Function.Injective f := by
    rintro ⟨e1, he1⟩ ⟨e2, he2⟩ heq
    have h1 := (G.edge_lift (G.mem_edgeFinset.mp he1)).choose_spec.2
    have h2 := (G.edge_lift (G.mem_edgeFinset.mp he2)).choose_spec.2
    apply Subtype.ext
    have hch : (G.edge_lift (G.mem_edgeFinset.mp he1)).choose =
        (G.edge_lift (G.mem_edgeFinset.mp he2)).choose := by
      have := congrArg Subtype.val heq
      simpa [f] using this
    have := congrArg (Sym2.map Subtype.val) hch
    rw [h1, h2] at this
    exact this
  calc G.edgeFinset.card
      = Fintype.card G.edgeFinset := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {s : Sym2 G.vertexSet // ¬ s.IsDiag} :=
        Fintype.card_le_of_injective f f_inj
    _ = (Fintype.card G.vertexSet).choose 2 := Sym2.card_subtype_not_diag
    _ = G.vertexFinset.card.choose 2 := by rw [G.vertexFinset_card_eq]

/-- The vertex finset cardinality of a `SimpleDiGraph` equals the
`Fintype.card` of the vertex subtype. -/
private lemma SimpleDiGraph.vertexFinset_card_eq (G : SimpleDiGraph α) [Finite G.vertexSet]
    [Fintype G.vertexSet] :
    G.vertexFinset.card = Fintype.card G.vertexSet := by
  change ((Set.toFinite (G.vertexSet)).toFinset).card = Fintype.card G.vertexSet
  exact (Set.toFinite G.vertexSet).card_toFinset

/-- The edge set of a simple directed graph has size at most `2·C(|V|, 2)`.
The proof embeds `E(G)` into the off-diagonal of `V × V`. -/
theorem SimpleDiGraph.card_edgeFinset_le_two_card_choose_two
    (G : SimpleDiGraph α) [Finite G.vertexSet] :
    G.edgeFinset.card ≤ 2 * G.vertexFinset.card.choose 2 := by
  classical
  haveI : Fintype G.vertexSet := Fintype.ofFinite _
  -- Build the injection `E(G) ↪ {p : V × V // p.1 ≠ p.2}`.
  let f : G.edgeFinset → {p : G.vertexSet × G.vertexSet // p.1 ≠ p.2} := fun e =>
    let he := G.mem_edgeFinset.mp e.property
    ⟨(⟨e.val.1, (G.incidence' _ he).1⟩, ⟨e.val.2, (G.incidence' _ he).2⟩), by
      simp only [ne_eq, Subtype.mk.injEq]
      exact G.loopless' _ he⟩
  have f_inj : Function.Injective f := by
    rintro ⟨⟨a, b⟩, h1⟩ ⟨⟨c, d⟩, h2⟩ heq
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq, Subtype.mk.injEq] at heq
    apply Subtype.ext
    ext
    · exact heq.1
    · exact heq.2
  -- Cardinality of `{p : V × V // p.1 ≠ p.2}` is `n(n-1) = 2·C(n,2)`.
  have hcard_off :
      Fintype.card {p : G.vertexSet × G.vertexSet // p.1 ≠ p.2} =
        Fintype.card G.vertexSet * (Fintype.card G.vertexSet - 1) := by
    classical
    rw [Fintype.card_subtype]
    have hfilt :
        ((Finset.univ : Finset (G.vertexSet × G.vertexSet)).filter
            fun p => p.1 ≠ p.2) =
          (Finset.univ : Finset G.vertexSet).offDiag := by
      ext ⟨x, y⟩
      simp [Finset.mem_offDiag]
    rw [hfilt, Finset.offDiag_card]
    simp [Finset.card_univ, Nat.mul_sub_one]
  have h2c : 2 * (Fintype.card G.vertexSet).choose 2 =
      Fintype.card G.vertexSet * (Fintype.card G.vertexSet - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]
  calc G.edgeFinset.card
      = Fintype.card G.edgeFinset := (Fintype.card_coe _).symm
    _ ≤ Fintype.card {p : G.vertexSet × G.vertexSet // p.1 ≠ p.2} :=
        Fintype.card_le_of_injective f f_inj
    _ = Fintype.card G.vertexSet * (Fintype.card G.vertexSet - 1) := hcard_off
    _ = 2 * (Fintype.card G.vertexSet).choose 2 := h2c.symm
    _ = 2 * G.vertexFinset.card.choose 2 := by rw [G.vertexFinset_card_eq]

/-! ## Convenience: `[Finite V(G)]` is enough

In normal use a downstream lemma should only need to write
`[Finite V(G)]` (i.e. `[Finite G.vertexSet]`). The instances below ensure
all of the following are then synthesised automatically:

* `Finite E(G)` / `Finite G.edgeSet` (already registered as instances above).
* `Fintype G.vertexSet`, `Fintype G.edgeSet` (via `Fintype.ofFinite`).
* `Set.Finite G.vertexSet`, `Set.Finite G.edgeSet`.
* The `vertexFinset` / `edgeFinset` `Finset` views.

The lemmas in this section let the user move freely between `Set.ncard`,
`Set.Finite.toFinset.card`, and `vertexFinset.card` / `edgeFinset.card`. -/

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite V(G)`. -/
lemma SimpleGraph.vertexSet_finite (G : SimpleGraph α) [Finite G.vertexSet] :
    G.vertexSet.Finite := ‹_›

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite V(G)`. -/
lemma SimpleDiGraph.vertexSet_finite (G : SimpleDiGraph α) [Finite G.vertexSet] :
    G.vertexSet.Finite := ‹_›

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite E(G)`. -/
lemma SimpleGraph.edgeSet_finite (G : SimpleGraph α) [Finite G.vertexSet] :
    G.edgeSet.Finite :=
  G.instFiniteEdgeSet

/-- A `[Finite V(G)]` hypothesis yields `Set.Finite E(G)`. -/
lemma SimpleDiGraph.edgeSet_finite (G : SimpleDiGraph α) [Finite G.vertexSet] :
    G.edgeSet.Finite :=
  G.instFiniteEdgeSet

end GraphLib
