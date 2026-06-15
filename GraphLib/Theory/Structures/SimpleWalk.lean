/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Graph.Basic
import GraphLib.Theory.Structures.VertexSeq

/-!
# Simple walks

A `SimpleWalk α` is a `VertexSeq α` whose consecutive vertices differ — i.e.
a non-stalling sequence. This file also provides the conversions to
`SimpleGraph` and `SimpleDiGraph` (the non-stalling property is exactly what
makes the resulting graph loopless).
-/

variable {α : Type*}

/-- A simple walk: a `VertexSeq` with no immediate backtracking. -/
def SimpleWalk (α : Type*) := { w : VertexSeq α // w.nonstalling }

namespace VertexSeq

/-- The unordered edges traversed by a vertex sequence (the consecutive
pairs `s(w.tail, v)` for each `cons` step). -/
@[grind] def edges : VertexSeq α → List (Sym2 α)
  | .singleton _ => []
  | .cons w v   => w.edges.concat s(w.tail, v)

/-- The directed arcs traversed by a vertex sequence (the consecutive ordered
pairs `(w.tail, v)` for each `cons` step). -/
@[grind] def arcs : VertexSeq α → List (α × α)
  | .singleton _ => []
  | .cons w v   => w.arcs.concat (w.tail, v)

end VertexSeq

namespace SimpleWalk

open GraphLib

/-- The underlying vertex sequence. -/
abbrev val (w : SimpleWalk α) : VertexSeq α := w.1

/-- The non-stalling proof. -/
lemma nonstalling (w : SimpleWalk α) : w.val.nonstalling := w.2

/-- View a simple walk as a `SimpleGraph`. The non-stalling property
provides the looplessness axiom. -/
def toSimpleGraph (w : SimpleWalk α) : SimpleGraph α where
  vertexSet := { v | v ∈ w.val.toList }
  edgeSet := { e | e ∈ w.val.edges }
  incidence' := by
    intro e he v hv
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.edges] at he
    | cons w' u ih =>
      simp [VertexSeq.edges] at he
      rcases he with he_old | he_new
      · have hns : w'.nonstalling := hq.1
        have hv' : v ∈ w'.toList := ih hns he_old
        simp [VertexSeq.toList]
        exact Or.inl hv'
      · subst he_new
        simp [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · simp [VertexSeq.toList]
        · simp [VertexSeq.toList]
  loopless' := by
    intro e he
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.edges] at he
    | cons w' u ih =>
      simp [VertexSeq.edges] at he
      rcases he with he_old | he_new
      · exact ih hq.1 he_old
      · subst he_new
        simp [Sym2.isDiag_iff_proj_eq]
        exact hq.2

/-- View a simple walk as a `SimpleDiGraph`. The non-stalling property
provides the looplessness axiom. -/
def toSimpleDiGraph (w : SimpleWalk α) : SimpleDiGraph α where
  vertexSet := { v | v ∈ w.val.toList }
  edgeSet := { a | a ∈ w.val.arcs }
  incidence' := by
    intro a ha
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.arcs] at ha
    | cons w' u ih =>
      simp [VertexSeq.arcs] at ha
      rcases ha with ha_old | ha_new
      · obtain ⟨h1, h2⟩ := ih hq.1 ha_old
        refine ⟨?_, ?_⟩
        · simp [VertexSeq.toList]; exact Or.inl h1
        · simp [VertexSeq.toList]; exact Or.inl h2
      · subst ha_new
        refine ⟨?_, ?_⟩
        · simp [VertexSeq.toList]
        · simp [VertexSeq.toList]
  loopless' := by
    intro a ha
    obtain ⟨q, hq⟩ := w
    induction q with
    | singleton _ => simp [VertexSeq.arcs] at ha
    | cons w' u ih =>
      simp [VertexSeq.arcs] at ha
      rcases ha with ha_old | ha_new
      · exact ih hq.1 ha_old
      · subst ha_new; exact hq.2

end SimpleWalk
