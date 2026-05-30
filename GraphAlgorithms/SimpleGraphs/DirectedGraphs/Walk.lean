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
          (G.loopless _ (heq ▸ hedg)).symm,
          heq ▸ hedg⟩
      · -- w'.length > 0: IH gives first edge of w', lift membership to w
        -- ih : w'.length > 0 → ∃ a₁ ∈ w'.support, a₁ ≠ w'.head ∧ (w'.head, a₁) ∈ G.edgeSet
        obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ := ih (Nat.pos_of_ne_zero h')
        exact ⟨a₁,
          by simp only [support, append_single, VertexSeq.toList, List.mem_cons];
              exact Or.inr ha₁_supp,
          ha₁_neq,
          ha₁_edge⟩

end Walk

-- Analytical definition of `path` for bfs correctness analysis.
namespace Path

open Walk
variable {α : Type*} [DecidableEq α]

/-- A path is a walk whose support (the list of vertices from VertexSeq.toList)
    has no duplicate vertices — List.Nodup. -/
def IsPathIn (G : SimpleDiGraph α) (w : Walk α) : Prop := IsWalkIn G w ∧ w.IsPath

/-- If w is a simple path (no repeated vertices) in G, and u is any vertex on that path,
    then the portion of the path from u onward is also a simple path in G. -/
lemma IsPathIn.suffix (G : SimpleDiGraph α) (w : Walk α) (u : α)
    (hu : u ∈ w.support) (hw : IsPathIn G w) :
    IsPathIn G ⟨w.seq.dropUntil u hu, dropUntil_iswalk w.seq u hu w.valid⟩ := by
  constructor
  · -- IsWalkIn: edges of suffix are edges of w; prove by induction on IsWalkIn w
    induction hw.1 generalizing u with   -- hw.1 : IsWalkIn G w
    | singleton v hv =>
      simp only [Walk.support, VertexSeq.toList, List.mem_singleton] at hu
      subst hu
      simp only [VertexSeq.dropUntil]
      exact Walk.IsWalkIn.singleton u hv
    | cons w' u' hw' hedg ih =>
      simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hu
      by_cases hu' : u ∈ w'.seq.toList
      · -- suffix starts inside w': dropUntil goes deeper, then re-attaches u'
        simp only [Walk.append_single, VertexSeq.dropUntil, dif_pos hu']
        expose_names; simp_all
        -- Prove the IsWalkIn for the suffix:
        -- the new walk is w'.seq.dropUntil u hu' with u' appended;
        -- the new walk is a walk in G because w' is a walk in G
        -- and the edge from w'.tail to u' is in G.
        -- #TODO: the current proof reads obsecure;
        --        can we clean it up to a few more readable lemmas?
        exact IsWalkIn.cons ⟨w'.seq.dropUntil u hu', dropUntil_iswalk w'.seq u hu' w'.valid⟩ u'
          (ih u hu' ⟨hw', by
            have hpath := hw.2
            simp only [Walk.IsPath, Walk.support,
              Walk.append_single, VertexSeq.toList, List.nodup_cons] at hpath
            exact hpath.2⟩)
          (by
            have htail :
              (
                ⟨w'.seq.dropUntil u hu', dropUntil_iswalk w'.seq u hu' w'.valid⟩ : Walk α
              ).tail = w'.tail :=
              VertexSeq.tail_dropUntil w'.seq u hu'
            exact htail ▸ hedg)
      · -- suffix starts at u': dropUntil stops immediately
        simp only [Walk.append_single, VertexSeq.dropUntil, dif_neg hu']
        exact IsWalkIn.singleton u' (G.incidence _ hedg).2
  · -- IsPath: suffix support is duplicate-free (dropUntil preserves Nodup)
    unfold Walk.IsPath Walk.support
    exact VertexSeq.dropUntil_toList_nodup hu hw.2


/-- Shortest path - analytical definition of distance:
    the length of minimum path between two vertices `v₁` and `v₂` in graph `G` -/
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
noncomputable
def weighted_distance (G : SimpleDiGraph α) (len : α → α → ℕ) (v₁ : α) (v₂ : α) : ℕ∞ :=
  ⨅ (w : Walk α) (_ : IsPathIn G w ∧ w.head = v₁ ∧ w.tail = v₂), (w.weighted_length len : ℕ∞)


end Path
