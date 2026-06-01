import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

import GraphAlgorithms.SimpleGraphs.DirectedGraphs.SimpleDiGraphs
import GraphAlgorithms.SimpleGraphs.DirectedGraphs.Walk  -- already incl. GraphAlgorithms.SimpleGraphs.Walk

-- Breadth-first Search
-- Author: Huang, JiangYi (nnhjy <43530784+nnhjy@users.noreply.github.com>);

set_option tactic.hygienic false
variable {α : Type*} [DecidableEq α]

open SimpleDiGraph
open Walk Path  -- from GraphAlgorithms.SimpleGraphs.DirectedGraphs.Walk
open Finset

namespace bfsAlgorithm

/-- The next BFS frontier — out-neighbours of the current frontier minus already-visited
    vertices — lies entirely within the unvisited part of V(G).
    This relies on the graph-theoretic fact that N⁺(G, v) ⊆ V(G) for every vertex v. -/
lemma bfs_next_subset_unvisited (G : SimpleDiGraph α) (frontier visited : Finset α) :
    (frontier.biUnion (fun v ↦ N⁺(G, v))) \ visited ⊆ V(G) \ visited :=
  Finset.subset_sdiff.mpr ⟨
    fun x hx => by
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hx).1
      exact (Finset.mem_filter.mp ha).1,
    Finset.disjoint_left.mpr fun x hxn hxvis =>
      (Finset.mem_sdiff.mp hxn).2 hxvis⟩

/-- Core BFS traversal that computes distances from a fixed root to all vertices.
    Processes one frontier level per recursive call, accumulating distances in `dist`.
    Termination is established via the measure `|V(G) \ visited|`, which decreases
    strictly at each recursive call because `next` is non-empty and `next ⊆ V(G) \ visited`.

    Parameters:
    - `G`        : the directed graph being searched
    - `visited`  : the union of all frontier sets processed so far; prevents revisiting
    - `frontier` : the set of vertices at the current BFS level (distance `d` from root)
    - `d`        : the distance of the current frontier from the root
    - `dist`     : accumulated distance map; vertices not yet reached carry `⊤`
-/
def bfs (G : SimpleDiGraph α) (visited frontier : Finset α)
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
      bfs G (visited ∪ next) next (d + 1) dist'
-- **Termination argument** — measure `|V(G) \ visited|` (unvisited vertex count).
-- Goal: show `|V(G) \ (visited ∪ next)| < |V(G) \ visited|`, i.e. the next call's
-- measure is strictly smaller.
termination_by (V(G) \ visited).card
decreasing_by
  rename_i h_next_ne
  -- *Containment* (`hnext_sub`): `next ⊆ V(G) \ visited`.
  -- Because every element of `next` is an out-neighbour of some frontier vertex —
  -- hence in V(G) — and was excluded from `visited` by construction
  -- (`bfs_next_subset_unvisited`).
  have hnext_sub : next ⊆ V(G) \ visited := bfs_next_subset_unvisited G frontier visited
  -- *Set identity* (`hkey`): `V(G) \ (visited ∪ next) = (V(G) \ visited) \ next`.
  -- Standard lattice law `(a \ b) \ c = a \ (b ⊔ c)` (`sdiff_sdiff_left`), with
  -- `∪ = ⊔` for `Finset`.
  have hkey  : V(G) \ (visited ∪ next) = (V(G) \ visited) \ next := by
    simp only [← Finset.sup_eq_union, ← sdiff_sdiff_left]   -- lattice law + ∪ = ⊔
  -- *Partition* (`hcard`): because `next ⊆ V(G) \ visited` (step 1),
  -- the unvisited vertices split as a disjoint union:
  --   `|(V(G) \ visited) \ next| + |next| = |V(G) \ visited|`
  -- (`Finset.card_sdiff_add_card_eq_card`).
  have hcard := Finset.card_sdiff_add_card_eq_card hnext_sub
  -- *Non-emptiness* (`hpos`): `next ≠ ∅` (the guard that enabled this branch), so `0 < |next|`.
  have hpos  := (Finset.nonempty_of_ne_empty h_next_ne).card_pos
  -- The above together give `|V(G) \ (visited ∪ next)| < |V(G) \ visited|` by `omega`.
  rw [hkey]; omega

/-- BFS distance map from `v` to all vertices of `G`.
    Reachable vertices receive their shortest-path distance (as `(d : ℕ∞)`);
    unreachable vertices receive `⊤` (infinity). -/
def bfsDistances (G : SimpleDiGraph α) (v : α) : α → ℕ∞ :=
  bfs G {v} {v} 0 (fun _ => ⊤)

/-- The shortest distance from `v₁` to `v₂` in directed graph `G`.
    Returns `⊤` if `v₂` is unreachable from `v₁`. Computed via BFS. -/
def bfsDistance (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  bfsDistances G v₁ v₂

/-- BFS returns `dist` unchanged when the frontier is empty. -/
lemma bfs_of_empty_frontier (G : SimpleDiGraph α) (visited : Finset α)
    (d : ℕ) (dist : α → ℕ∞) :
    bfs G visited ∅ d dist = dist := by
  unfold bfs; simp

/-- When the frontier is non-empty but the next frontier is empty,
    BFS records the current frontier at distance `d` and stops. -/
lemma bfs_of_empty_next (G : SimpleDiGraph α) (visited frontier : Finset α)
    (d : ℕ) (dist : α → ℕ∞)
    (h_fe : frontier ≠ ∅)
    (h_ne : (frontier.biUnion (fun v ↦ N⁺(G,v))) \ visited = ∅) :
    bfs G visited frontier d dist =
      fun u => if u ∈ frontier then (d : ℕ∞) else dist u := by
  conv_lhs => unfold bfs
  rw [if_neg h_fe]; simp only [h_ne, ite_true]

/-- When both the frontier and the next frontier are non-empty,
    BFS advances one level. -/
lemma bfs_of_nonempty_next (G : SimpleDiGraph α) (visited frontier : Finset α)
    (d : ℕ) (dist : α → ℕ∞)
    (h_fe : frontier ≠ ∅)
    (h_ne : (frontier.biUnion (fun v ↦ N⁺(G,v))) \ visited ≠ ∅) :
    bfs G visited frontier d dist =
      bfs G (visited ∪ (frontier.biUnion (fun v ↦ N⁺(G, v))) \ visited)
            ((frontier.biUnion (fun v ↦ N⁺(G, v))) \ visited)
            (d + 1)
            (fun u => if u ∈ frontier then (d : ℕ∞) else dist u) := by
  conv_lhs => unfold bfs
  rw [if_neg h_fe]; simp only [if_neg h_ne]

end bfsAlgorithm

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
    (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞)
    (v : α) (hv_vis : v ∈ visited) (hv_fron : v ∉ frontier) :
    bfsAlgorithm.bfs G visited frontier d dist v = dist v := by
  -- Induct on an upper bound m for (V(G) \ visited).card to obtain an IH
  -- that covers the recursive call's strictly smaller measure.
  suffices key : ∀ (m : ℕ) (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞),
      (V(G) \ visited).card ≤ m → v ∈ visited → v ∉ frontier →
      bfsAlgorithm.bfs G visited frontier d dist v = dist v from
    key _ _ _ _ _ le_rfl hv_vis hv_fron
  intro m
  induction m with
  | zero =>
    intro visited frontier d dist hm hv_vis hv_fron
    by_cases h_empty : frontier = ∅
    · -- frontier = ∅: bfs returns dist
      simp only [h_empty, bfsAlgorithm.bfs_of_empty_frontier]
    · -- frontier ≠ ∅; next = ∅ because V(G) ⊆ visited (card ≤ 0)
      have hnext_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅ := by
        have hvG : V(G) \ visited = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hm)
        have hnext_sub : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited ⊆ V(G) \ visited :=
          bfsAlgorithm.bfs_next_subset_unvisited G frontier visited
        exact Finset.subset_empty.mp (hvG ▸ hnext_sub)
      have hbfs := congr_fun
        (bfsAlgorithm.bfs_of_empty_next G visited frontier d dist h_empty hnext_empty) v
      simp only [hbfs, if_neg hv_fron]
  | succ m ih =>
    intro visited frontier d dist hm hv_vis hv_fron
    by_cases h_empty : frontier = ∅
    · simp only [h_empty, bfsAlgorithm.bfs_of_empty_frontier]
    · by_cases h_next_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅
      · -- next = ∅: bfs records frontier and stops; dist' v = dist v since v ∉ frontier
        have hbfs := congr_fun
          (bfsAlgorithm.bfs_of_empty_next G visited frontier d dist h_empty h_next_empty) v
        simp only [hbfs, if_neg hv_fron]
      · -- next ≠ ∅: bfs recurses; apply IH with smaller measure
        rw [congr_fun
            (bfsAlgorithm.bfs_of_nonempty_next G visited frontier d dist h_empty h_next_empty) v]
        set next  := (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited
        set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else dist u
        have hv_not_next : v ∉ next := fun h => (Finset.mem_sdiff.mp h).2 hv_vis
        have hmeasure : (V(G) \ (visited ∪ next)).card ≤ m := by
          have hnext_sub : next ⊆ V(G) \ visited :=
            bfsAlgorithm.bfs_next_subset_unvisited G frontier visited
          have hkey : V(G) \ (visited ∪ next) = (V(G) \ visited) \ next := by
            simp only [← Finset.sup_eq_union, ← sdiff_sdiff_left]
          have hcard := Finset.card_sdiff_add_card_eq_card hnext_sub
          have hpos  := (Finset.nonempty_of_ne_empty h_next_empty).card_pos
          rw [hkey]; omega
        rw [ih (visited ∪ next) next (d + 1) dist' hmeasure
              (Finset.mem_union_left _ hv_vis) hv_not_next]
        simp [dist', if_neg hv_fron]

/-- Helper theorem to prove `bfs_complete`:
    If a simple path of length k ending at v exists whose head lies in frontier
    and whose non-head vertices avoid visited, then BFS records v with distance ≤ d + k.
    `m` is an upper bound on `w.length` used as the induction variable. -/
theorem bfs_complete_aux (G : SimpleDiGraph α) (v : α)
    (m : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    (w : Walk α) (hw : Path.IsPathIn G w) (hw_head : w.head ∈ frontier)
    (hw_tail : w.tail = v) (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (hfv : frontier ⊆ visited)
    (hn : w.length < m) :
    bfsAlgorithm.bfs G visited frontier d init_dist v ≤ d + w.length := by
  induction m generalizing visited frontier d init_dist w with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ m ih =>
    unfold bfsAlgorithm.bfs
    set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
    set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
    split_ifs with h_empty
    · -- frontier = ∅: contradicts hw_head
      simp [h_empty] at hw_head
    · -- frontier ≠ ∅; case-split on whether next is empty
      by_cases h_next_empty : next = ∅
      · -- next = ∅: path must have length 0 (otherwise a₁ ∈ next, contradiction)
        simp only [h_next_empty, ite_true]
        rcases Nat.eq_zero_or_pos w.length with h_len | h_len
        · -- w.length = 0: v = w.head ∈ frontier, dist' v = d ≤ d + 0
          have hv_front : v ∈ frontier :=
            hw_tail ▸ (Walk.head_eq_tail_of_length_zero w h_len ▸ hw_head)
          simp only [dist', if_pos hv_front, h_len, Nat.cast_zero, add_zero]
          exact_mod_cast le_refl _
        · -- w.length > 0: a₁ ∈ next = ∅, contradiction
          obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ := isWalkIn_first_edge G w hw.1 h_len
          have ha₁_out : a₁ ∈ N⁺(G, w.head) := by
            simp only [OutNeighbors, Finset.mem_filter]
            exact ⟨(G.incidence _ ha₁_edge).2,
                  (w.head, a₁), ha₁_edge, rfl, rfl, ha₁_neq⟩
          have ha₁_next : a₁ ∈ next :=
            Finset.mem_sdiff.mpr
              ⟨Finset.mem_biUnion.mpr ⟨w.head, hw_head, ha₁_out⟩,
              hw_avoid a₁ ha₁_supp ha₁_neq⟩
          simp [h_next_empty] at ha₁_next
      · -- next ≠ ∅: recursive case; case-split on walk length
        simp only [if_neg h_next_empty]
        rcases Nat.eq_zero_or_pos w.length with h_len | h_len
        · -- case `w.length = 0`: v = w.head ∈ frontier, use bfs_stable
          have hv_front : v ∈ frontier :=
            hw_tail ▸ (Walk.head_eq_tail_of_length_zero w h_len ▸ hw_head)
          have hv_vis : v ∈ visited := hfv hv_front
          have hv_not_next : v ∉ next := fun h => (Finset.mem_sdiff.mp h).2 hv_vis
          rw [bfs_stable G (visited ∪ next) next (d + 1) dist' v
                (Finset.mem_union_left _ hv_vis) hv_not_next]
          simp only [dist', if_pos hv_front]
          simp [h_len]
        · -- case `w.length > 0`: decompose walk, apply IH
          -- get the second vertex in the support (index 1) and split the walk there
          have h_support_len : w.support.length = w.length + 1 := by
            simp [Walk.support, VertexSeq.toList_length_eq]
          obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ :
              ∃ a₁ ∈ w.support, a₁ ≠ w.head ∧ (w.head, a₁) ∈ G.edgeSet :=
            isWalkIn_first_edge G w hw.1 h_len
          -- ── Part 1: a₁ ∈ next ──────────────────────────────────────────────────
          have ha₁_out : a₁ ∈ N⁺(G, w.head) := by
            simp only [OutNeighbors, Finset.mem_filter]
            exact ⟨(G.incidence _ ha₁_edge).2,
                  (w.head, a₁), ha₁_edge, rfl, rfl, ha₁_neq⟩
          have ha₁_next : a₁ ∈ next :=
            Finset.mem_sdiff.mpr
              ⟨Finset.mem_biUnion.mpr ⟨w.head, hw_head, ha₁_out⟩,
              hw_avoid a₁ ha₁_supp ha₁_neq⟩
          -- ── Part 2: find u = first element of w.support.dropLast in next ────────
          have ha₁_in_dropLast : a₁ ∈ w.support.dropLast := by
            apply List.mem_dropLast_of_mem_of_ne_getLast ha₁_supp
            have : w.support.getLast (List.ne_nil_of_mem ha₁_supp) = w.head :=
              VertexSeq.toList_getLast_is_head w.seq (List.ne_nil_of_mem ha₁_supp)
            rw [this]; exact ha₁_neq
          have h_find : (w.support.dropLast.find? (· ∈ next)).isSome := by
            simp only [List.find?_isSome]
            exact ⟨a₁, ha₁_in_dropLast, by simpa using ha₁_next⟩
          obtain ⟨u, hu_def⟩ := Option.isSome_iff_exists.mp h_find
          have hu_next : u ∈ next := by
            rw [List.find?_eq_some_iff_append] at hu_def
            exact of_decide_eq_true hu_def.1
          have hu_supp : u ∈ w.support :=
            List.dropLast_subset w.support (List.mem_of_find?_eq_some hu_def)
          have hu_ne_hd : u ≠ w.head := by
            intro h; rw [h] at hu_next
            exact (Finset.mem_sdiff.mp hu_next).2 (hfv hw_head)
          obtain ⟨_, as, bs, heq_split, has_not⟩ := List.find?_eq_some_iff_append.mp hu_def
          have hu_prev : ∀ x ∈ as, x ∉ next := fun x hx => by simpa using has_not x hx
          -- ── Part 3: suffix walk from u to v ─────────────────────────────────────
          let w' : Walk α :=
            ⟨w.seq.dropUntil u hu_supp, dropUntil_iswalk w.seq u hu_supp w.valid⟩
          have hw'_head : w'.head = u    := VertexSeq.head_dropUntil w.seq u hu_supp
          have hw'_tail : w'.tail = v    := by
            simp only [w', Walk.tail]; rw [VertexSeq.tail_dropUntil]; exact hw_tail
          have hw'_path : Path.IsPathIn G w' := Path.IsPathIn.suffix G w u hu_supp hw
          have hw'_lt_w : w'.length < w.length :=
            VertexSeq.dropUntil_length_lt_of_ne_head hu_supp hu_ne_hd
          have hw'_len_lt : w'.length < m := by omega
          have hw'_avoid : ∀ x ∈ w'.support, x ≠ w'.head → x ∉ visited ∪ next := by
            intro x hx hxu
            have hx_supp : x ∈ w.support := VertexSeq.mem_dropUntil w.seq u x hu_supp hx
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
            have hxu_val : x ≠ u := hw'_head ▸ hxu
            have hu_last : w'.support.getLast (List.ne_nil_of_mem hx) = u := by
              simp only [Walk.support, VertexSeq.toList_getLast_is_head]; exact hw'_head
            have hx_dL : x ∈ w'.support.dropLast := by
              apply List.mem_dropLast_of_mem_of_ne_getLast hx
              rw [hu_last]; exact hxu_val
            have hTne : (w.seq.takeUntil u hu_supp).dropTail.toList ≠ [] :=
              List.ne_nil_of_mem hw_head_in_take
            have heq2 : w'.support.dropLast ++ u :: (
              w.seq.takeUntil u hu_supp).dropTail.toList.dropLast = as ++ u :: bs := by
              have h1 : w.support.dropLast = w'.support.dropLast ++ u ::
                  (w.seq.takeUntil u hu_supp).dropTail.toList.dropLast := by
                rw [hlist, List.dropLast_append_of_ne_nil hTne,
                    ← List.dropLast_append_getLast (List.ne_nil_of_mem hx), hu_last]
                simp [List.append_assoc]
              rw [← h1]; exact heq_split
            have hu_ndL : u ∉ w'.support.dropLast := by
              intro h
              have hnd : (w'.support.dropLast ++ [u]).Nodup := by
                have heq_list : w'.support.dropLast ++ [u] = w'.support := by
                  rw [← hu_last, List.dropLast_append_getLast (List.ne_nil_of_mem hx)]
                rw [heq_list]; exact hw'_path.2
              exact absurd (
                (List.nodup_append.mp hnd).2.2 u h u (List.mem_singleton.mpr rfl)
              ) (fun h => h rfl)
            have hu_nas : u ∉ as := fun h => absurd hu_next (by simpa using has_not u h)
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
          calc bfsAlgorithm.bfs G (visited ∪ next) next (d + 1) dist' v
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
    hw (Finset.mem_singleton.mpr hw_head) hw_tail
    (fun x _ hne => mt Finset.mem_singleton.mp (hw_head ▸ hne))
    (Finset.Subset.refl _) hn
  simp only [Nat.cast_zero, zero_add] at haux
  exact_mod_cast haux

/-- Sub Goal B for `bfs_correct`:
    If `bfs G visited frontier d dist v` returns a finite distance,
    then there exists a valid path in `G` from `root` to `v` of that length. -/
@[simp]
theorem bfs_sound (G : SimpleDiGraph α) (root : α) (v : α)
    (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    -- INV-1: every distance already in `init_dist` corresponds to a real path from `root`
    (h_dist : ∀ v : α, init_dist v ≠ ⊤ →
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = init_dist v)
    -- INV-2: every `frontier` vertex has a path of length `d` whose vertices lie in `visited`
    (h_front : ∀ v ∈ frontier,
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited)
    (hv : bfsAlgorithm.bfs G visited frontier d init_dist v ≠ ⊤) :
    ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
        (w.length : ℕ∞) = bfsAlgorithm.bfs G visited frontier d init_dist v := by
  -- Induct on an upper bound for the termination measure (V(G) \ visited).card
  suffices key : ∀ (m : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞),
      (V(G) \ visited).card ≤ m →
      (∀ v : α, init_dist v ≠ ⊤ →
          ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
            (w.length : ℕ∞) = init_dist v) →
      (∀ v ∈ frontier,
          ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
            (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited) →
      bfsAlgorithm.bfs G visited frontier d init_dist v ≠ ⊤ →
      ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = bfsAlgorithm.bfs G visited frontier d init_dist v from
    key _ _ _ _ _ le_rfl h_dist h_front hv
  intro m
  induction m with
  | zero =>
    intro visited frontier d init_dist hm h_dist h_front hv
    -- next = ∅ because V(G) ⊆ visited (card ≤ 0)
    have hnext_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅ := by
      have hvG : V(G) \ visited = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hm)
      have hs : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited ⊆ V(G) \ visited :=
        bfsAlgorithm.bfs_next_subset_unvisited G frontier visited
      exact Finset.subset_empty.mp (hvG ▸ hs)
    by_cases h_empty : frontier = ∅
    · -- frontier = ∅: bfs returns init_dist
      simp only [h_empty, bfsAlgorithm.bfs_of_empty_frontier] at hv ⊢
      exact h_dist v hv
    · -- frontier ≠ ∅, next = ∅: bfs returns fun u => if u ∈ frontier then d else init_dist u
      have hbfs := congr_fun
        (bfsAlgorithm.bfs_of_empty_next G visited frontier d init_dist h_empty hnext_empty) v
      rw [hbfs] at hv ⊢
      split_ifs at hv ⊢ with hv_front
      · exact h_front v hv_front |>.imp fun w ⟨hp, hh, ht, hl, _⟩ => ⟨hp, hh, ht, hl⟩
      · exact h_dist v hv
  | succ m ih =>
    intro visited frontier d init_dist hm h_dist h_front hv
    by_cases h_empty : frontier = ∅
    · simp only [h_empty, bfsAlgorithm.bfs_of_empty_frontier] at hv ⊢
      exact h_dist v hv
    · by_cases h_next_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅
      · -- next = ∅: bfs returns fun u => if u ∈ frontier then d else init_dist u
        have hbfs := congr_fun
          (bfsAlgorithm.bfs_of_empty_next G visited frontier d init_dist h_empty h_next_empty) v
        rw [hbfs] at hv ⊢
        split_ifs at hv ⊢ with hv_front
        · exact h_front v hv_front |>.imp fun w ⟨hp, hh, ht, hl, _⟩ => ⟨hp, hh, ht, hl⟩
        · exact h_dist v hv
      · -- next ≠ ∅: bfs recurses; apply IH with smaller measure
        have hbfs_eq := congr_fun
          (bfsAlgorithm.bfs_of_nonempty_next G visited frontier d init_dist h_empty h_next_empty) v
        rw [hbfs_eq] at hv ⊢
        set next  := (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited
        set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
        have hmeasure : (V(G) \ (visited ∪ next)).card ≤ m := by
          have hnext_sub : next ⊆ V(G) \ visited :=
            bfsAlgorithm.bfs_next_subset_unvisited G frontier visited
          have hkey : V(G) \ (visited ∪ next) = (V(G) \ visited) \ next := by
            simp only [← Finset.sup_eq_union, ← sdiff_sdiff_left]
          have hcard := Finset.card_sdiff_add_card_eq_card hnext_sub
          have hpos  := (Finset.nonempty_of_ne_empty h_next_empty).card_pos
          rw [hkey]; omega
        apply ih (visited ∪ next) next (d + 1) dist' hmeasure
        · -- h_dist': ∀ u, dist' u ≠ ⊤ → ∃ path ...
          intro u hu
          simp only [dist'] at hu
          split_ifs at hu with hu_front
          · obtain ⟨w, hw_path, hw_head, hw_tail, hw_len, _⟩ := h_front u hu_front
            simp only [dist', if_pos hu_front]
            exact ⟨w, hw_path, hw_head, hw_tail, hw_len⟩
          · simp only [dist', if_neg hu_front]
            exact h_dist u hu
        · -- h_front': ∀ u ∈ next, ∃ path of length d+1 ...
          intro u hu_next
          have hu_in_next : u ∈ next := hu_next
          rw [Finset.mem_sdiff, Finset.mem_biUnion] at hu_next
          obtain ⟨⟨v_src, hv_front, hv_neigh⟩, hu_not_vis⟩ := hu_next
          simp only [OutNeighbors, Finset.mem_filter] at hv_neigh
          obtain ⟨_, e, he_edge, he1, he2, _⟩ := hv_neigh
          have hedg : (v_src, u) ∈ G.edgeSet := by
            have : e = (v_src, u) := Prod.ext he1.symm he2.symm; rwa [← this]
          obtain ⟨w_v, hw_path, hw_head, hw_tail, hw_len, hw_supp⟩ := h_front v_src hv_front
          have h_neq : u ≠ w_v.tail := hw_tail ▸ Ne.symm (G.loopless (v_src, u) hedg)
          refine ⟨w_v.append_single u h_neq, ?_, ?_, ?_, ?_, ?_⟩
          · constructor
            · exact IsWalkIn.cons w_v u hw_path.1 (hw_tail ▸ hedg)
            · simp only [Walk.IsPath, Walk.append_single, Walk.support, VertexSeq.toList]
              exact List.nodup_cons.mpr ⟨fun h => hu_not_vis (hw_supp u h), hw_path.2⟩
          · change (w_v.seq.cons u).head = root
            rw [VertexSeq.con_head_eq]; change w_v.head = root; exact hw_head
          · rfl
          · have hlen : (w_v.append_single u h_neq).length = 1 + w_v.length := rfl
            rw [hlen]; push_cast; rw [hw_len]; ring
          · intro x hx
            simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact Finset.mem_union_right _ hu_in_next
            · exact Finset.mem_union_left _ (hw_supp x hx)
        · exact hv

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
        bfs_sound G v₁ v₂ {v₁} {v₁} 0 (fun _ => ⊤)
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
