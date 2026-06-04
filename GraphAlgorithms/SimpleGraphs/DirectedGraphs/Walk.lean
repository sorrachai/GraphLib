import Mathlib.Data.Finset.Basic
import GraphAlgorithms.SimpleGraphs.Walk
import GraphAlgorithms.SimpleGraphs.DirectedGraphs.SimpleDiGraphs

-- Authors: Sorrachai Yingchareonthawornchai
--          Huang, JiangYi (nnhjy <43530784+nnhjy@users.noreply.github.com>)

namespace Walk

set_option tactic.hygienic false

/-- A walk `w` is a walk in graph `G` if every consecutive pair of vertices
    forms an edge in `G`, and the starting vertex lies in the vertex set. -/
inductive IsWalkIn {V : Type*} (G : SimpleDiGraph V) : Walk V → Prop
  | singleton (v : V) (hv : v ∈ G.vertexSet)
    : IsWalkIn G ⟨.singleton v, .singleton v⟩
  | cons (w : Walk V) (u : V)
      (hw   : IsWalkIn G w)
      (hedg : (w.tail, u) ∈ G.edgeSet)
    : IsWalkIn G (w.append_single u (by have : ∀ e ∈ G.edgeSet, e.1 ≠ e.2 :=  G.loopless; grind))

/-- A walk of positive length in G has a first outgoing edge from its head.
    Usage:
    - Helper lemma to prove `BreadFirstSearch.bfs_complete_aux` -/
@[simp, grind .]
lemma isWalkIn_first_edge {V : Type*}
    (G : SimpleDiGraph V) (w : Walk V)
    (hw : Walk.IsWalkIn G w) (hlen : w.length > 0) :
    ∃ a₁ ∈ w.support, a₁ ≠ w.head ∧ (w.head, a₁) ∈ G.edgeSet := by
  induction hw with
  | singleton v hv => exact absurd hlen (by grind [VertexSeq.length])
  | cons w' u' hw_inner hedg ih =>
    by_cases h' : w'.length = 0
    · -- w' is a singleton: w'.head = w'.tail, direct edge (w.head, u')
      have heq : w'.head = w'.tail := Walk.head_eq_tail_of_length_zero w' h'
      exact ⟨u',
        by simp [Walk.support, Walk.append_single, VertexSeq.toList],
        (G.loopless _ (heq ▸ hedg)).symm, heq ▸ hedg⟩
    · -- w'.length > 0: IH gives first edge of w', lift membership to w
      -- ih : w'.length > 0 → ∃ a₁ ∈ w'.support, a₁ ≠ w'.head ∧ (w'.head, a₁) ∈ G.edgeSet
      obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ := ih (Nat.pos_of_ne_zero h')
      exact ⟨a₁,
        by simp only [support, append_single, VertexSeq.toList, List.mem_cons];
            exact Or.inr ha₁_supp, ha₁_neq, ha₁_edge⟩

end Walk

-- Analytical definition of `path` for bfs correctness analysis.
namespace Path

open Finset Walk SimpleDiGraph
variable {α : Type*} [DecidableEq α]

/-- A path is a walk whose support (the list of vertices from VertexSeq.toList)
    has no duplicate vertices — List.Nodup. -/
@[simp, grind .]
def IsPathIn (G : SimpleDiGraph α) (w : Walk α) : Prop := IsWalkIn G w ∧ w.IsPath

omit [DecidableEq α] in
/-- A prefix walk `w'` is a path-in-G whenever the extended walk `w'.append_single u'` is a
    path-in-G and `w'` is independently known to be a walk-in-G. -/
private lemma isPathIn_of_append_single_left {G : SimpleDiGraph α} {w' : Walk α} {u' : α}
    {h : u' ≠ w'.tail}
    (hwalk : IsWalkIn G w') (hpath : IsPathIn G (w'.append_single u' h)) :
    IsPathIn G w' :=
  ⟨hwalk, by
    have := hpath.2
    simp only [Walk.IsPath, Walk.support, Walk.append_single,
               VertexSeq.toList, List.nodup_cons] at this
    exact this.2⟩

/-- If w is a simple path (no repeated vertices) in G, and u is any vertex on that path,
    then the portion of the path from u onward is also a simple path in G. -/
@[simp, grind .]
lemma IsPathIn.suffix (G : SimpleDiGraph α) (w : Walk α) (u : α)
    (hu : u ∈ w.support) (hw : IsPathIn G w) :
    IsPathIn G ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.valid⟩ := by
  constructor
  · -- Part 1: IsWalkIn G (suffix).
    -- Strategy: induction on the structure of `hw.1 : IsWalkIn G w`.
    -- `u` is generalised so the IH applies at any vertex, not just the outermost one.
    induction hw.1 generalizing u with
    | singleton v hv =>
      -- w is a singleton {v}; its only vertex is v, so u = v and dropUntil returns {v} unchanged.
      -- `grind` derives u = v from hu, unfolds dropUntil, and closes with IsWalkIn.singleton.
      grind [Walk.support, VertexSeq.toList, VertexSeq.dropUntil, Walk.IsWalkIn.singleton]
    | cons w' u' hw' hedg ih =>
      -- w = w'.append_single u', so u lies either in w' or is u' itself.
      simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hu
      by_cases hu' : u ∈ w'.seq.toList
      · -- u is strictly inside w': dropUntil recurses into w' and then re-attaches u'.
        -- After simplification the goal is IsWalkIn G ((dropUntil w' u).append_single u').
        simp only [Walk.append_single, VertexSeq.dropUntil, dif_pos hu']
        expose_names; simp_all only [support, or_true]
        -- Apply IsWalkIn.cons: the suffix of w' is a walk-in-G (by IH, using the fact that w'
        -- is itself a path since w was a path), and the edge (suffix.tail, u') exists because
        -- tail_dropUntil shows the suffix tail equals w'.tail where hedg already gives the edge.
        exact IsWalkIn.cons ⟨w'.seq.dropUntil u hu', dropUntil_iswalk w'.seq u hu' w'.valid⟩ u'
          (ih u hu' (isPathIn_of_append_single_left hw' hw))
          (walk_tail_dropUntil w' u hu' ▸ hedg)
      · -- u = u' (the appended vertex): dropUntil stops immediately, yielding the singleton {u'}.
        -- u' is in G.vertexSet because hedg witnesses an outgoing edge from w'.tail to u'.
        simp only [Walk.append_single, VertexSeq.dropUntil, dif_neg hu']
        exact IsWalkIn.singleton u' (G.incidence _ hedg).2
  · -- Part 2: IsPath (suffix), i.e. no repeated vertices.
    -- dropUntil preserves List.Nodup, so the suffix support is still duplicate-free.
    unfold Walk.IsPath Walk.support
    exact VertexSeq.dropUntil_toList_nodup hu hw.2

omit [DecidableEq α]
/-- Any simple path in `G` has strictly fewer edges than vertices: `w.length < |V(G)|`.
    This is the classical fact that a simple path visits distinct vertices,
    so its support (a nodup list) has at most |V(G)| elements,
    and the support length equals `w.length + 1`. -/
@[simp, grind .]
lemma path_length_lt_card_vertices (G : SimpleDiGraph α) (w : Walk α)
    (hw : Path.IsPathIn G w) : w.length < #V(G) := by
  have h_supp_len : w.support.length = w.length + 1 := by
    simp [Walk.support, VertexSeq.toList_length_eq]
  have hsupp_sub : ∀ x ∈ w.support, x ∈ V(G) := by
    suffices h : ∀ (ww : Walk α), IsWalkIn G ww → ∀ x ∈ ww.support, x ∈ V(G) from h w hw.1
    intro ww hww
    induction hww with
    | singleton v hv => grind
    | cons w' u' hw' hedg ih =>
      intro x hx
      simp only [support, append_single, VertexSeq.toList, List.mem_cons] at hx
      rcases hx with rfl | hx <;> grind [G.incidence _ hedg]
  have h_le : w.support.length ≤ #V(G) :=
    open scoped Classical in
    calc w.support.length
        = w.support.toFinset.card := (List.toFinset_card_of_nodup hw.2).symm
      _ ≤ V(G).card               := Finset.card_le_card
            (fun x hx => hsupp_sub x (List.mem_toFinset.mp hx))
  omega

/-- Shortest path - analytical definition of distance:
    the length of minimum path between two vertices `v₁` and `v₂` in graph `G` -/
@[simp, grind .]
noncomputable def shortestPath (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  /- ⨅: the indexed infimum (greatest lower bound) operator.
     - `⨅ (x : T), f x` is `iInf f`
     - `⨅ (x : T) (_ : P x), f x` is `iInf (fun x => iInf (fun _ : P x => f x))`,
       a nested `iInf` where the inner one ranges over proofs of `P x`.
       When `P x` is False (no proof exists), `iInf` over an empty type gives `⊤`.
     Here it means the infimum (minimum) of `w.length` over all walks `w` satisfying the condition.
     When the condition is empty (no such path exists), ⨅ over an empty set
     in ℕ∞ gives ⊤ (infinity) automatically. -/
  ⨅ (w : Walk α) (_ : IsPathIn G w ∧ w.head = v₁ ∧ w.tail = v₂), (w.length : ℕ∞)

-- /-- Lemma 22.1 in CLRS: the triangle inequality for shortest paths.
--     ∀ s ∈ V(G), ∀ (u, v) ∈ E(G), shortestPath G s v ≤ shortestPath G s u + 1 -/
-- lemma shortestPath_triangle_inequality [Fintype α] (G : SimpleDiGraph α) (s u v : α)
--     (h_su : shortestPath G s u ≠ ⊤) (h_uv : (u, v) ∈ E(G)) :
--     shortestPath G s v ≤ shortestPath G s u + 1 := by
--   sorry

/-- Shortest path - analytical definition of distance:
    the length of minimum path between two vertices `v₁` and `v₂` in graph `G` -/
@[simp, grind .]
noncomputable
def weighted_distance (G : SimpleDiGraph α) (len : α → α → ℕ) (v₁ : α) (v₂ : α) : ℕ∞ :=
  ⨅ (w : Walk α) (_ : IsPathIn G w ∧ w.head = v₁ ∧ w.tail = v₂), (w.weighted_length len : ℕ∞)


end Path
