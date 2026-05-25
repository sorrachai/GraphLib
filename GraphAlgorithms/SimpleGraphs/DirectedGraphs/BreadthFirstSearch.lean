import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.SimpleGraphs.DirectedGraphs.SimpleDiGraphs
import GraphAlgorithms.SimpleGraphs.DirectedGraphs.Walk  -- already incl. GraphLib.GraphAlgorithms.Core.Walk

-- Breadth-first Search
-- Author: Huang, JiangYi (nnhjy <43530784+nnhjy@users.noreply.github.com>);

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

open SimpleDiGraph
open Walk
open Finset

namespace bfsAlgorithm_Tests

/-- Core BFS traversal that computes distances from a fixed root to all vertices.
    Processes one frontier level per recursive call, accumulating distances in `dist`.
    Termination is established via the measure `|V(G)| − |visited|`, which decreases
    strictly at each recursive call because `next` is non-empty and disjoint from `visited`.

    Parameters:
    - `G`        : the directed graph being searched
    - `visited`  : the union of all frontier sets processed so far; prevents revisiting.
                   Carries the invariant `hv : visited ⊆ V(G)` to support termination.
    - `frontier` : the set of vertices at the current BFS level (distance `d` from root)
    - `hv`       : proof that `visited ⊆ V(G)`; threaded through each recursive call
    - `d`        : the distance of the current frontier from the root
    - `dist`     : accumulated distance map; vertices not yet reached carry `⊤`
-/
def bfs (G : SimpleDiGraph α) (visited frontier : Finset α)
    (hv : visited ⊆ V(G)) -- carry invariant for termination
    (d : ℕ) (dist : α → ℕ∞) : α → ℕ∞ :=
  /- *Exhausted*: if `frontier = ∅`, no new vertices are reachable;
     all remaining vertices are unreachable and retain `⊤` in `dist`. -/
  if frontier = ∅ then dist
  else
    /- *Record*: assign distance `d` to every vertex in the current frontier. -/
    let dist' := fun v => if v ∈ frontier then (d : ℕ∞) else dist v
    /- *Expand*: compute `next`, the next frontier, as the out-neighbors of
       every vertex in `frontier`, minus all already-visited vertices:
       `next = (⋃ v ∈ frontier, N⁺(G, v)) \ visited` -/
    let next  := (Finset.biUnion frontier (fun v ↦ N⁺(G, v))) \ visited
    if next = ∅ then dist'
    else
      /- *Recurse*: advance one level — `visited` absorbs `next`,
         `frontier` becomes `next`, `d` increments by 1. -/
      bfs G (visited ∪ next) next
      (by
        apply Finset.union_subset hv
        intro x hx
        obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hx).1
        exact (Finset.mem_filter.mp ha).1)
      (d + 1) dist'
-- Termination measure: the number of vertices not yet in `visited`.
-- Every recursive call adds the non-empty set `next` to `visited`, so the measure
-- strictly decreases.  Since `visited ⊆ V(G)` (invariant `hv`), the measure is
-- bounded below by 0, guaranteeing termination in at most `|V(G)|` rounds.
termination_by (#V(G)) - visited.card
decreasing_by
  rename_i h_next_ne
  -- `visited ⊆ V(G)` ⟹ `|visited| ≤ |V(G)|`
  have hle_1 : visited.card ≤ #V(G) := Finset.card_le_card hv
  -- `next` is defined as `(⋃ v ∈ frontier, N⁺(G,v)) \ visited`, so it is
  -- disjoint from `visited` by construction.
  have hdisj : Disjoint visited next :=
    Finset.disjoint_left.mpr (fun x hxv hxn =>
      (Finset.mem_sdiff.mp hxn).2 hxv)
  -- Because `visited` and `next` are disjoint:
  -- `|visited ∪ next| = |visited| + |next|`
  have hcard := Finset.card_union_of_disjoint hdisj
  -- `next ≠ ∅` ⟹ `|next| ≥ 1`, so the new `visited` is strictly larger.
  have hpos  := (Finset.nonempty_of_ne_empty h_next_ne).card_pos
  -- `next ⊆ V(G)` (every out-neighbour lies in the vertex set), so
  -- `visited ∪ next ⊆ V(G)` ⟹ `|visited ∪ next| ≤ |V(G)|`.
  -- This upper bound is needed so that ℕ-subtraction does not underflow to 0.
  have hle_2 : (visited ∪ next).card ≤ #V(G) := by
    apply Finset.card_le_card
    apply Finset.union_subset hv
    intro x hx
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_filter.mp ha).1
  -- Fold `next` into the goal so that `hcard`, `hpos`, `hle_2` are in terms of
  -- the same `next` name and `omega` can close the arithmetic goal:
  -- `|V(G)| − |visited ∪ next|  <  |V(G)| − |visited|`
  change #V(G) - (visited ∪ next).card < #V(G) - visited.card
  omega

/-- BFS distance map from `v` to all vertices of `G`.
    Reachable vertices receive their shortest-path distance (as `(d : ℕ∞)`);
    unreachable vertices receive `⊤` (infinity). -/
def bfsDistances (G : SimpleDiGraph α) (v : α) (hv : v ∈ V(G)) : α → ℕ∞ :=
  bfs G {v} {v} (Finset.singleton_subset_iff.mpr hv) 0 (fun _ => ⊤)

end bfsAlgorithm_Tests
namespace bfsAlgorithm

/-- Core BFS traversal that computes distances from a fixed root to all vertices.
    Processes one frontier level per recursive call, accumulating distances in `dist`.

    Parameters:
    - `G`        : the directed graph being searched
    - `n`        : termination counter, initialised to `Fintype.card α`;
                   decreases by 1 each call so Lean accepts the recursion without a proof.
                   Since any shortest path visits at most `|V|` vertices,
                   `|V|` rounds always suffice.
    - `visited`  : the union of all frontier sets processed so far; prevents revisiting
    - `frontier` : the set of vertices at the current BFS level (distance `d` from root)
    - `d`        : the distance of the current frontier from the root
    - `dist`     : accumulated distance map; vertices not yet reached carry `⊤`
-/
def bfs (G : SimpleDiGraph α) :
    ℕ → Finset α → Finset α → ℕ → (α → ℕ∞) → (α → ℕ∞)
  /- **Base case** (`n = 0`): counter exhausted — return accumulated `dist` as-is.
     Unreached vertices retain `⊤`. This branch is never reached when `n` is
     initialised to `Fintype.card α`. -/
  | 0, _, _, _, dist => dist
  /- **Recursion case** when called with arguments
     `(n+1, visited, frontier, d, dist)`, do the following... -/
  | n+1, visited, frontier, d, dist =>
    /- *Exhausted*: if `frontier = ∅`, no new vertices are reachable;
       all remaining vertices are unreachable and retain `⊤` in `dist`. -/
    if frontier = ∅ then dist
    else
      /- *Record*: assign distance `d` to every vertex in the current frontier. -/
      let dist' := fun v => if v ∈ frontier then (d : ℕ∞) else dist v
      /- *Expand*: compute `next`, the next frontier, as the out-neighbors of
         every vertex in `frontier`, minus all already-visited vertices:
         `next = (⋃ v ∈ frontier, N⁺(G, v)) \ visited` -/
      let next  := (Finset.biUnion frontier (fun v ↦ N⁺(G, v))) \ visited
      /- *Recurse*: advance one level — `visited` absorbs `next`,
         `frontier` becomes `next`, `d` increments by 1. -/
      bfs G n (visited ∪ next) next (d + 1) dist'

/-- BFS distance map from `v` to all vertices of `G`.
    Reachable vertices receive their shortest-path distance (as `(d : ℕ∞)`);
    unreachable vertices receive `⊤` (infinity). -/
def bfsDistances (G : SimpleDiGraph α) (v : α) : α → ℕ∞ :=
  bfs G (#V(G)) {v} {v} 0 (fun _ => ⊤)

/-- The shortest distance from `v₁` to `v₂` in directed graph `G`.
    Returns `⊤` if `v₂` is unreachable from `v₁`. Computed via BFS. -/
def bfsDistance (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  bfsDistances G v₁ v₂

end bfsAlgorithm


-- Analytical definition of `path` for bfs correctness analysis.
namespace Path

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
      exact IsWalkIn.singleton u hv
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

end Path

namespace bfsCorrectness

-- /-- Lemma 22.2 in CLRS: BFS bounds the shortest path.
--     Suppose that BFS is run on G from a given source vertex s ∈ V.
--     Then upon termination, ∀ v ∈ V, the distance computed by BFS satisfies:
--     bfsDistances G s v ≥ shortestPath G s v -/
-- lemma bfs_bounds_shortest_path [Fintype α] (G : SimpleDiGraph α) (s v : α)
--     (h_s : s ∈ G.vertexSet) :
--     bfsAlgorithm.bfsDistances G s v ≥ Path.shortestPath G s v := by
--   sorry

-- /-- Lemma 22.3 in CLRS: During the execution of BFS on a graph G,
--     the `frontier` contains the vertices {v₁, ..., vᵣ}, where v₁ is the head and vᵣ is the tail.
--     Then dist' vᵣ ≤ dist' v₁ + 1. -/
-- lemma bfs_triangle_inequality [Fintype α] (G : SimpleDiGraph α) (root : α) (v₁ v₂ : α)
--     (h_root : root ∈ G.vertexSet) :
--     bfsAlgorithm.bfsDistances G root v₂ ≤ bfsAlgorithm.bfsDistances G root v₁ + 1 := by
--   sorry

-- /-- Corollary 22.4 in CLRS: For vertices vᵢ and vⱼ are enqueued during the execution of BFS,
--     and that vᵢ is enqueued before vⱼ. Then dist' vᵢ ≤ dist' vⱼ at the time that vⱼ is enqueued.
--     * This turns out a tautology in our implementation. -/
-- lemma bfs_enqueue_order [Fintype α] (G : SimpleDiGraph α) (root : α) (vᵢ vⱼ : α)
--     (h_root : root ∈ G.vertexSet)
--     (h_enqueue : bfsAlgorithm.bfsDistances G root vᵢ ≤ bfsAlgorithm.bfsDistances G root vⱼ) :
--     bfsAlgorithm.bfsDistances G root vᵢ ≤ bfsAlgorithm.bfsDistances G root vⱼ := by
--   sorry

/-- Helper lemma to prove `bfs_complete_aux`:
    Once a vertex is in `visited` and not in the current frontier,
    BFS never changes its recorded distance. -/
private lemma bfs_stable (G : SimpleDiGraph α)
    (n : ℕ) (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞)
    (v : α) (hv_vis : v ∈ visited) (hv_fron : v ∉ frontier) :
    bfsAlgorithm.bfs G n visited frontier d dist v = dist v := by
  induction n generalizing visited frontier d dist with
  | zero => simp [bfsAlgorithm.bfs]
  | succ n ih =>
    simp only [bfsAlgorithm.bfs]
    split_ifs with h_empty
    · -- frontier = ∅: bfs returns dist unchanged
      rfl
    · -- frontier ≠ ∅: record dist', compute next, recurse
      set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else dist u
      set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
      -- v ∉ next because next ⊆ complement of visited, but v ∈ visited
      have hv_not_next : v ∉ next :=
        fun h => (Finset.mem_sdiff.mp h).2 hv_vis
      -- Apply IH: v ∈ visited ∪ next (from hv_vis), v ∉ next (proved above)
      rw [ih (visited ∪ next) next (d + 1) dist' (Finset.mem_union_left _ hv_vis) hv_not_next]
      simp [dist', if_neg hv_fron]

/-- Helper theorem to prove `bfs_complete`:
    If a simple path of length k ending at v exists whose head lies in frontier
    and whose non-head vertices avoid visited, then BFS records v with distance ≤ d + k. -/
theorem bfs_complete_aux (G : SimpleDiGraph α) (v : α)
    (n : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    (w : Walk α) (hw : Path.IsPathIn G w) (hw_head : w.head ∈ frontier)
    (hw_tail : w.tail = v) (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (hfv : frontier ⊆ visited)
    (hn : w.length < n) :
    bfsAlgorithm.bfs G n visited frontier d init_dist v ≤ d + w.length := by
  induction n generalizing visited frontier d init_dist w with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [bfsAlgorithm.bfs]
    split_ifs with h_empty
    · -- frontier = ∅: contradicts hw_head
      simp [h_empty] at hw_head
    · -- frontier ≠ ∅
      set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
      set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
      -- Case split on walk length
      rcases Nat.eq_zero_or_pos w.length with h_len | h_len
      · -- case `w.length = 0`: w is a trivial walk, v = w.head ∈ frontier
        -- v gets distance d from dist', then bfs_stable keeps it
        have hv_front : v ∈ frontier :=
          hw_tail ▸ (Walk.head_eq_tail_of_length_zero w h_len ▸ hw_head)
          -- Alternatively, in tactic mode:
          -- by have h_eq := Walk.head_eq_tail_of_length_zero w h_len  -- w.head = w.tail
          -- rw [← hw_tail, ← h_eq]; exact hw_head
        have hv_vis : v ∈ visited := hfv hv_front
        have hv_not_next : v ∉ next := fun h => (Finset.mem_sdiff.mp h).2 hv_vis
        rw [bfs_stable G n (visited ∪ next) next (d + 1) dist' v
              (Finset.mem_union_left _ hv_vis) hv_not_next]
        simp only [dist', if_pos hv_front]
        simp [h_len]
      · -- case `w.length > 0`: let w.length = k + 1, decompose walk
        -- get the second vertex in the support (index 1) and split the walk there
        have h_support_len : w.support.length = w.length + 1 := by
          simp [Walk.support, VertexSeq.toList_length_eq]
        obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ :
            ∃ a₁ ∈ w.support, a₁ ≠ w.head ∧ (w.head, a₁) ∈ G.edgeSet := by
          exact isWalkIn_first_edge G w hw.1 h_len
        -- ── Part 1: a₁ ∈ next ────────────────────────────────────────────────────
        have ha₁_out : a₁ ∈ N⁺(G, w.head) := by
          simp only [OutNeighbors, Finset.mem_filter]
          exact ⟨(G.incidence _ ha₁_edge).2,
                (w.head, a₁), ha₁_edge, rfl, rfl, ha₁_neq⟩
        have ha₁_next : a₁ ∈ next :=
          Finset.mem_sdiff.mpr
            ⟨Finset.mem_biUnion.mpr ⟨w.head, hw_head, ha₁_out⟩,
            hw_avoid a₁ ha₁_supp ha₁_neq⟩
        -- ── Part 2: find u = first element of w.support.dropLast in next ──────────
        -- Exists: a₁ ∈ w.support.dropLast ∩ next
        -- (a₁ ∈ w.support and a₁ ≠ w.head, so it's not the last element w.head)
        -- Use List.find? to pick the FIRST such element (last in walk order)
        have ha₁_in_dropLast : a₁ ∈ w.support.dropLast := by
          apply List.mem_dropLast_of_mem_of_ne_getLast ha₁_supp
          have : w.support.getLast (List.ne_nil_of_mem ha₁_supp) = w.head :=
            VertexSeq.toList_getLast_is_head w.seq (List.ne_nil_of_mem ha₁_supp)
          rw [this]
          exact ha₁_neq
        -- find?_isSome (available as @[simp]) to obtain the form ∃ x, x ∈ xs ∧ p x
        have h_find : (w.support.dropLast.find? (· ∈ next)).isSome := by
          simp only [List.find?_isSome]
          exact ⟨a₁, ha₁_in_dropLast, by simpa using ha₁_next⟩
        obtain ⟨u, hu_def⟩ := Option.isSome_iff_exists.mp h_find
        have hu_next : u ∈ next := by
          rw [List.find?_eq_some_iff_append] at hu_def
          exact of_decide_eq_true hu_def.1
        have hu_supp : u ∈ w.support :=
          List.dropLast_subset w.support (List.mem_of_find?_eq_some hu_def)
        have hu_ne_hd : u ≠ w.head       := by
          intro h; rw [h] at hu_next
          exact (Finset.mem_sdiff.mp hu_next).2 (hfv hw_head)
        -- all elements BEFORE u in the list are not in next (u is the first)
        obtain ⟨_, as, bs, heq_split, has_not⟩ := List.find?_eq_some_iff_append.mp hu_def
        have hu_prev : ∀ x ∈ as, x ∉ next := fun x hx => by simpa using has_not x hx
        -- ── Part 3: suffix walk from u to v, verify IH conditions ─────────────────
        let w' : Walk α :=
          ⟨w.seq.dropUntil u hu_supp, dropUntil_iswalk w.seq u hu_supp w.valid⟩
        have hw'_head : w'.head = u    := VertexSeq.head_dropUntil w.seq u hu_supp
        have hw'_tail : w'.tail = v    := by
          simp only [w', Walk.tail]; rw [VertexSeq.tail_dropUntil]; exact hw_tail
        have hw'_path : Path.IsPathIn G w' := Path.IsPathIn.suffix G w u hu_supp hw
        have hw'_lt_w : w'.length < w.length :=
          VertexSeq.dropUntil_length_lt_of_ne_head hu_supp hu_ne_hd
        have hw'_len_lt : w'.length < n := by omega
        have hw'_avoid : ∀ x ∈ w'.support, x ≠ w'.head → x ∉ visited ∪ next := by
          intro x hx hxu
          have hx_supp : x ∈ w.support  := VertexSeq.mem_dropUntil w.seq u x hu_supp hx
          have hw_head_in_take : w.head ∈ (w.seq.takeUntil u hu_supp).dropTail.toList := by
            have : (w.seq.takeUntil u hu_supp).dropTail.head = w.head := by
              simp [VertexSeq.dropTail_head, VertexSeq.head_takeUntil]
            exact this ▸ VertexSeq.head_mem_toList _
          have hlist : w.support = w'.support ++ (w.seq.takeUntil u hu_supp).dropTail.toList := by
            simp only [Walk.support]
            rw [← Walk.toList_append, Walk.vertex_seq_split w.seq u hu_supp hu_ne_hd]
          have hx_ne_hd : x ≠ w.head := by
            have hnodup : (w'.support ++ (w.seq.takeUntil u hu_supp).dropTail.toList).Nodup := by
              rw [← hlist]; exact hw.2
            exact (List.nodup_append.mp hnodup).2.2 x hx w.head hw_head_in_take
          refine Finset.notMem_union.mpr ⟨hw_avoid x hx_supp hx_ne_hd, ?_⟩
          -- x comes before u in the support list (because x is in the dropUntil prefix)
          have hxu_val : x ≠ u := hw'_head ▸ hxu
          -- u = getLast w'.support
          have hu_last : w'.support.getLast (List.ne_nil_of_mem hx) = u := by
            simp only [Walk.support, VertexSeq.toList_getLast_is_head]
            exact hw'_head
          -- x ∈ w'.support.dropLast
          have hx_dL : x ∈ w'.support.dropLast := by
            apply List.mem_dropLast_of_mem_of_ne_getLast hx
            rw [hu_last]; exact hxu_val
          -- w'.support.dropLast ++ u :: T.dropLast = as ++ u :: bs
          have hTne : (w.seq.takeUntil u hu_supp).dropTail.toList ≠ [] :=
            List.ne_nil_of_mem hw_head_in_take
          have heq2 : w'.support.dropLast ++ u :: (
            w.seq.takeUntil u hu_supp
          ).dropTail.toList.dropLast = as ++ u :: bs := by
            have h1 : w.support.dropLast = w'.support.dropLast ++ u ::
                (w.seq.takeUntil u hu_supp).dropTail.toList.dropLast := by
              rw [hlist, List.dropLast_append_of_ne_nil hTne,
                  ← List.dropLast_append_getLast (List.ne_nil_of_mem hx), hu_last]
              simp [List.append_assoc]
            rw [← h1]; exact heq_split
          -- u ∉ w'.support.dropLast
          have hu_ndL : u ∉ w'.support.dropLast := by
            intro h
            have hnd : (w'.support.dropLast ++ [u]).Nodup := by
              have heq_list : w'.support.dropLast ++ [u] = w'.support := by
                rw [← hu_last, List.dropLast_append_getLast (List.ne_nil_of_mem hx)]
              rw [heq_list]; exact hw'_path.2
            exact absurd (
              (List.nodup_append.mp hnd).2.2 u h u (List.mem_singleton.mpr rfl)
            ) (fun h => h rfl)
          -- u ∉ as
          have hu_nas : u ∉ as := fun h => absurd hu_next (by simpa using has_not u h)
          -- lengths equal ⟹ w'.support.dropLast = as
          have hlen : w'.support.dropLast.length = as.length := by
            suffices h : w'.support.dropLast = as from congr_arg _ h
            rcases List.append_eq_append_iff.mp heq2 with ⟨l, h1, h2⟩ | ⟨l, h1, h2⟩
            · cases l with
              | nil => simpa using h1.symm
              | cons a rest =>
                  simp only [List.cons_append] at h2
                  have ha : u = a := (List.cons.inj h2).1
                  have hmem : a ∈ as :=
                    h1.symm ▸ List.mem_append_right w'.support.dropLast List.mem_cons_self
                  exact absurd (ha.symm ▸ hmem) hu_nas
            · cases l with
              | nil => simpa using h1
              | cons a rest =>
                  simp only [List.cons_append] at h2
                  have ha : u = a := (List.cons.inj h2).1
                  have hmem : a ∈ w'.support.dropLast :=
                    h1.symm ▸ List.mem_append_right as List.mem_cons_self
                  exact absurd (ha.symm ▸ hmem) hu_ndL
          exact hu_prev x (List.append_inj_left heq2 hlen ▸ hx_dL)
        -- ── Part 4: apply IH and arithmetic ──────────────────────────────────────
        have hbound := ih (visited ∪ next) next (d + 1) dist' w'
                          hw'_path (hw'_head ▸ hu_next) hw'_tail hw'_avoid
                          Finset.subset_union_right hw'_len_lt
        calc bfsAlgorithm.bfs G n (visited ∪ next) next (d + 1) dist' v
            ≤ ↑(d + 1) + ↑w'.length := hbound
          _ ≤ ↑d + ↑w.length        := by
                have h : w'.length + 1 ≤ w.length := Nat.succ_le_of_lt hw'_lt_w
                exact_mod_cast (show d + 1 + w'.length ≤ d + w.length by omega)

/-- Sub Goal A for `bfs_correct`:
    If a path of length `k` exists from `root` vertex to `v` in `G`,
    then BFS returns `distance ≤ k` for `v`. -/
@[simp]
theorem bfs_complete (G : SimpleDiGraph α) (root : α) (v : α) (k : ℕ)
    (hk : ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧ (w.length : ℕ∞) = k) :
    bfsAlgorithm.bfsDistance G root v ≤ k := by
  obtain ⟨w, hw, hw_head, hw_tail, hw_len⟩ := hk
  rw [← hw_len]
  simp only [bfsAlgorithm.bfsDistance, bfsAlgorithm.bfsDistances]
  have hn : w.length < #V(G) := by
    have h1 : w.support.length = w.length + 1 := by
      simp [Walk.support, VertexSeq.toList_length_eq]
    have hsupp_sub : ∀ x ∈ w.support, x ∈ V(G) := by
      suffices h : ∀ (ww : Walk α), IsWalkIn G ww → ∀ x ∈ ww.support, x ∈ V(G) from
        h w hw.1
      intro ww hww
      induction hww with
      | singleton v hv =>
        intro x hx
        simp only [support, VertexSeq.toList, List.mem_cons, List.not_mem_nil, or_false] at hx
        exact hx ▸ hv
      | cons w' u' hw' hedg ih =>
        intro x hx
        simp only [support, append_single, VertexSeq.toList, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (G.incidence _ hedg).2
        · exact ih x hx
    have h2 : w.support.length ≤ #V(G) := by
      have hnd : w.support.Nodup := hw.2
      calc w.support.length
          = w.support.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
        _ ≤ V(G).card               := by
              apply Finset.card_le_card
              intro x hx
              rw [List.mem_toFinset] at hx
              exact hsupp_sub x hx
    omega
  have haux := bfs_complete_aux G v (#V(G)) {root} {root} 0 (fun _ => ⊤) w
    hw
    (Finset.mem_singleton.mpr hw_head)
    hw_tail
    (fun x _ hne => mt Finset.mem_singleton.mp (hw_head ▸ hne))
    (Finset.Subset.refl _)
    hn
  simp only [Nat.cast_zero, zero_add] at haux
  exact_mod_cast haux

/-- Sub Goal B for `bfs_correct`:
    If `bfs G n visited frontier d dist v` = k,
    then there exists a valid path in `G` from `root` vertex to `v` of `length k`. -/
@[simp]
theorem bfs_sound (G : SimpleDiGraph α) (root : α) (v : α)
    (n : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    -- INV-1: every distance already in `init_dist` corresponds to a real path from `root`
    (h_dist : ∀ v : α, init_dist v ≠ ⊤ →
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = init_dist v)
    -- INV-2: every `frontier` vertex has a path of length `d` whose vertices lie in `visited`
    (h_front : ∀ v ∈ frontier,
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited)
    (hv : bfsAlgorithm.bfs G n visited frontier d init_dist v ≠ ⊤) :
    ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
        (w.length : ℕ∞) = bfsAlgorithm.bfs G n visited frontier d init_dist v := by
  induction n generalizing visited frontier d init_dist with
  | zero =>
    simp only [bfsAlgorithm.bfs] at hv ⊢
    exact h_dist v hv
  | succ n ih =>
    simp only [bfsAlgorithm.bfs] at hv ⊢
    split_ifs with h_empty
    · -- frontier = ∅: bfs returns init_dist unchanged
      simp only [h_empty] at hv
      exact h_dist v hv
    · -- frontier ≠ ∅: record dist', compute next, recurse
      set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
      set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
      apply ih (visited ∪ next) next (d + 1) dist'
      · -- h_dist': ∀ u, dist' u ≠ ⊤ → ∃ path ...
        intro u hu
        simp only [dist'] at hu
        split_ifs at hu with hu_front
        · -- u ∈ frontier: dist' u = d, path comes from h_front
          obtain ⟨w, hw_path, hw_head, hw_tail, hw_len, _⟩ := h_front u hu_front
          simp only [dist', if_pos hu_front]
          exact ⟨w, hw_path, hw_head, hw_tail, hw_len⟩
        · -- u ∉ frontier: dist' u = init_dist u, path comes from h_dist
          simp only [dist', if_neg hu_front]
          exact h_dist u hu
      · -- h_front': ∀ u ∈ next, ∃ path of length d+1 ...
        -- Save u ∈ next before destructuring (needed later for the support proof):
        intro u hu_next
        have hu_in_next : u ∈ next := hu_next
        rw [Finset.mem_sdiff, Finset.mem_biUnion] at hu_next
        obtain ⟨⟨v_src, hv_front, hv_neigh⟩, hu_not_vis⟩ := hu_next
        -- Extract the edge from N⁺:
        simp only [OutNeighbors, Finset.mem_filter] at hv_neigh
        obtain ⟨_, e, he_edge, he1, he2, _⟩ := hv_neigh
        have hedg : (v_src, u) ∈ G.edgeSet := by
          have : e = (v_src, u) := Prod.ext he1.symm he2.symm; rwa [← this]
        -- Get path to v_src:
        obtain ⟨w_v, hw_path, hw_head, hw_tail, hw_len, hw_supp⟩ := h_front v_src hv_front
        -- Prove u ≠ w_v.tail (required by append_single):
        have h_neq : u ≠ w_v.tail := hw_tail ▸ Ne.symm (G.loopless (v_src, u) hedg)
        -- Construct the extended walk and prove all fields:
        refine ⟨w_v.append_single u h_neq, ?_, ?_, ?_, ?_, ?_⟩
        · -- IsPathIn: IsWalkIn ∧ IsPath
          constructor
          · exact IsWalkIn.cons w_v u hw_path.1 (hw_tail ▸ hedg)
          · simp only [Walk.IsPath, Walk.append_single, Walk.support, VertexSeq.toList]
            exact List.nodup_cons.mpr ⟨fun h => hu_not_vis (hw_supp u h), hw_path.2⟩
        · -- head = root
          change (w_v.seq.cons u).head = root
          rw [VertexSeq.con_head_eq]
          -- Walk.head is abbrev for w.seq.head, so hw_head : w_v.seq.head = root
          change w_v.head = root; exact hw_head
        · -- tail = u
          rfl
        · -- length cast = d + 1
          have hlen : (w_v.append_single u h_neq).length = 1 + w_v.length := rfl
          rw [hlen]; push_cast
          rw [hw_len]; ring
        · -- support ⊆ visited ∪ next
          intro x hx
          simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_union_right _ hu_in_next
          · exact Finset.mem_union_left _ (hw_supp x hx)
      · simp only [h_empty] at hv; exact hv

theorem bfs_correct (G : SimpleDiGraph α) (v₁ v₂ : α)
    (h₁ : v₁ ∈ G.vertexSet) :
    bfsAlgorithm.bfsDistance G v₁ v₂ = Path.shortestPath G v₁ v₂ := by
  apply le_antisymm
  · -- Goal A: Distance G v₁ v₂ ≤ shortestPath G v₁ v₂
    unfold Path.shortestPath
    apply le_iInf; intro w
    apply le_iInf; intro ⟨hw_path, hw_head, hw_tail⟩
    exact bfs_complete G v₁ v₂ w.length ⟨w, hw_path, hw_head, hw_tail, rfl⟩
  · -- Goal B: shortestPath G v₁ v₂ ≤ Distance G v₁ v₂
    unfold Path.shortestPath
    by_cases hv : bfsAlgorithm.bfsDistance G v₁ v₂ = ⊤
    · rw [hv]; exact le_top
    · simp only [bfsAlgorithm.bfsDistance, bfsAlgorithm.bfsDistances] at hv ⊢
      obtain ⟨w, hw_path, hw_head, hw_tail, hw_len⟩ :=
        bfs_sound G v₁ v₂ (#V(G)) {v₁} {v₁} 0 (fun _ => ⊤)
          -- h_dist: init_dist = ⊤ everywhere, so hypothesis is vacuous
          (fun u hu => absurd rfl hu)
          -- h_front: singleton walk v₁ → v₁ of length 0
          (fun u hu => ⟨
            ⟨.singleton v₁, .singleton v₁⟩,
            ⟨IsWalkIn.singleton v₁ h₁,
              by simp [Walk.IsPath, Walk.support, VertexSeq.toList]⟩,
            rfl,
            (Finset.mem_singleton.mp hu).symm,
            by simp [Walk.length, VertexSeq.length],
            fun x hx => by
              simp only [support, VertexSeq.toList, List.mem_cons, List.not_mem_nil, or_false] at hx
              exact Finset.mem_singleton.mpr hx
          ⟩)
          hv
      exact iInf_le_of_le w (iInf_le_of_le ⟨hw_path, hw_head, hw_tail⟩ (le_of_eq hw_len))

end bfsCorrectness

-- #TODOs:
-- 1. etedn bfs to produce a search tree (or forest) and prove its properties
-- 2. extend to undirected graphs (should be straightforward,
--    just need to add the reverse edge in the BFS step)
