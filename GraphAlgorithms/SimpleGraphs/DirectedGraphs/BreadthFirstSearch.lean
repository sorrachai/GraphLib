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

/-! ## Properties within BFS process: vertex set update, List, Walk, Path -/
namespace bfsBattery

/-- The next BFS frontier — out-neighbours of the current frontier minus already-visited
    vertices — lies entirely within the unvisited part of V(G).
    This relies on the graph-theoretic fact that N⁺(G, v) ⊆ V(G) for every vertex v. -/
@[simp, grind .]
lemma next_subset_unvisited (G : SimpleDiGraph α) (frontier visited : Finset α) :
    (frontier.biUnion (fun v ↦ N⁺(G, v))) \ visited ⊆ V(G) \ visited :=
  Finset.subset_sdiff.mpr ⟨
    fun x hx => by
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hx).1
      exact (Finset.mem_filter.mp ha).1,
    Finset.disjoint_left.mpr fun x hxn hxvis =>
      (Finset.mem_sdiff.mp hxn).2 hxvis⟩

/-- If all graph vertices are already visited, BFS discovers no new vertices in the next step. -/
@[simp, grind .]
lemma next_empty_of_all_visited (G : SimpleDiGraph α)
    (frontier visited : Finset α)
    (h : V(G) \ visited = ∅) :
    (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅ :=
  Finset.subset_empty.mp (h ▸ next_subset_unvisited G frontier visited)

/-- When the next frontier is nonempty, the count of unvisited vertices strictly decreases. -/
@[simp, grind .]
lemma decreasing_unvisited_vertices_count (G : SimpleDiGraph α)
    (visited next : Finset α) (m : ℕ)
    (hnext_sub : next ⊆ V(G) \ visited)
    (hnext_nonempty : next.Nonempty)
    (hm : (V(G) \ visited).card ≤ m + 1) :
    (V(G) \ (visited ∪ next)).card ≤ m := by
  -- *Set identity* (`hkey`): `V(G) \ (visited ∪ next) = (V(G) \ visited) \ next`.
  -- Standard lattice law `(a \ b) \ c = a \ (b ⊔ c)` (`sdiff_sdiff_left`), with
  -- `∪ = ⊔` for `Finset`.
  have hkey : V(G) \ (visited ∪ next) = (V(G) \ visited) \ next := by
    simp only [← Finset.sup_eq_union, ← sdiff_sdiff_left]
  -- *Partition* (`hcard`): because `next ⊆ V(G) \ visited`,
  -- the unvisited vertices split as a disjoint union:
  --   `|(V(G) \ visited) \ next| + |next| = |V(G) \ visited|`
  -- (`Finset.card_sdiff_add_card_eq_card`).
  have hcard := Finset.card_sdiff_add_card_eq_card hnext_sub
  -- *Non-emptiness* (`hpos`): `next.Nonempty`, so `0 < |next|`.
  have hpos  := hnext_nonempty.card_pos
  rw [hkey]; omega

/-- For any positive-length path starting at a frontier vertex,
    its first out-neighbor lies in the next BFS frontier. -/
@[simp]
lemma walk_first_succ_mem_next (G : SimpleDiGraph α)
    (frontier visited : Finset α) (next : Finset α)
    (hnext_def : next = (frontier.biUnion (fun u ↦ N⁺(G,u))) \ visited)
    (w : Walk α)
    (hw_walk : IsWalkIn G w) (h_len : 0 < w.length)
    (hw_head : w.head ∈ frontier)
    (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited) :
    ∃ a₁ ∈ w.support, a₁ ≠ w.head ∧ (w.head, a₁) ∈ G.edgeSet ∧ a₁ ∈ next := by
  obtain ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge⟩ := isWalkIn_first_edge G w hw_walk h_len
  have ha₁_out : a₁ ∈ N⁺(G, w.head) := by
    simp only [OutNeighbors, Finset.mem_filter]
    exact ⟨(G.incidence _ ha₁_edge).2, (w.head, a₁), ha₁_edge, rfl, rfl, ha₁_neq⟩
  exact ⟨a₁, ha₁_supp, ha₁_neq, ha₁_edge, hnext_def ▸
    Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w.head, hw_head, ha₁_out⟩,
      hw_avoid a₁ ha₁_supp ha₁_neq⟩⟩

/-- For any positive-length path starting at a frontier vertex, whose non-head vertices avoid
    `visited`, there exists a *first* vertex `u` in `w.support.dropLast` entering `next`.
    "First" is witnessed by a split `w.support.dropLast = as ++ u :: bs` where every element
    of `as` lies outside `next`. -/
@[simp]
lemma first_next_entry_of_path (G : SimpleDiGraph α)
    (frontier visited : Finset α)
    (next : Finset α)
    (hnext_def : next = (frontier.biUnion (fun u ↦ N⁺(G,u))) \ visited)
    (w : Walk α) (hw : Path.IsPathIn G w)
    (hw_head : w.head ∈ frontier) (h_len : 0 < w.length)
    (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (hfv : frontier ⊆ visited) :
    ∃ u ∈ w.support, u ∈ next ∧ u ≠ w.head ∧
    ∃ as bs : List α,
      w.support.dropLast = as ++ u :: bs ∧ ∀ x ∈ as, x ∉ next := by
  obtain ⟨a₁, ha₁_supp, ha₁_neq, _, ha₁_next⟩ :=
    walk_first_succ_mem_next G frontier visited next hnext_def w hw.1 h_len hw_head hw_avoid
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
    rw [List.find?_eq_some_iff_append] at hu_def; exact of_decide_eq_true hu_def.1
  have hu_supp : u ∈ w.support :=
    List.dropLast_subset w.support (List.mem_of_find?_eq_some hu_def)
  have hu_ne_hd : u ≠ w.head := fun h =>
    (Finset.mem_sdiff.mp (hnext_def ▸ hu_next)).2 (hfv (h ▸ hw_head))
  obtain ⟨_, as, bs, heq_split, has_not⟩ := List.find?_eq_some_iff_append.mp hu_def
  exact ⟨u, hu_supp, hu_next, hu_ne_hd, as, bs, heq_split, fun x hx => by simpa using has_not x hx⟩

/-- In a nodup list, the last element is not in the list's `dropLast`.

    Mathlib's closest candidate is `List.idxOf_getLast`, but it requires
    `getLast ∉ dropLast` as a hypothesis, making it circular.
    `List.mem_dropLast_iff_idxOf_lt` provides the semantic equivalence but
    requires separately establishing that `idxOf (getLast l) = l.length - 1`,
    which in turn needs the very fact we are proving. -/
@[simp, grind .]
private lemma list_nodup_getLast_not_mem_dropLast {α : Type*}
    {l : List α} (h : l ≠ []) (hnd : l.Nodup) : l.getLast h ∉ l.dropLast := by
  intro hmem
  have hnd' : (l.dropLast ++ [l.getLast h]).Nodup := by
    rwa [List.dropLast_append_getLast h]
  exact absurd
    ((List.nodup_append.mp hnd').2.2 _ hmem _ (List.mem_singleton.mpr rfl))
    (fun h => h rfl)

/-- If `l₁ ++ u :: l₃ = l₂ ++ u :: l₄` and `u ∉ l₁` and `u ∉ l₂`, then `l₁ = l₂`.
    That is, the position of the first occurrence of `u` uniquely determines the split.

    Mathlib has `List.append_cons_inj_of_notMem`, which gives the same conclusion but
    under different hypotheses: it requires `u ∉ l₁` and `u ∉ l₃` — both conditions on
    the *same* side of the equation. Here we have `u ∉ l₁` and `u ∉ l₂`, on *different*
    sides, matching the BFS situation where `u` is absent from the suffix walk's interior
    and from the prefix `as`, but we have no direct guarantee about `l₃` or `l₄`. -/
@[simp, grind .]
private lemma list_left_unique_split {α : Type*}
    {l₁ l₂ : List α} {u : α} {l₃ l₄ : List α}
    (heq : l₁ ++ u :: l₃ = l₂ ++ u :: l₄) (h₁ : u ∉ l₁) (h₂ : u ∉ l₂) : l₁ = l₂ := by
  rcases List.append_eq_append_iff.mp heq with ⟨l, h1, h2⟩ | ⟨l, h1, h2⟩
  · cases l with
    | nil => simpa using h1.symm
    | cons a rest =>
        simp only [List.cons_append] at h2
        have ha : u = a := (List.cons.inj h2).1
        exact absurd (h1.symm ▸ List.mem_append_right l₁ (ha ▸ List.mem_cons_self)) h₂
  · cases l with
    | nil => simpa using h1
    | cons a rest =>
        simp only [List.cons_append] at h2
        have ha : u = a := (List.cons.inj h2).1
        exact absurd (h1.symm ▸ List.mem_append_right l₂ (ha ▸ List.mem_cons_self)) h₁

/-- If `suffix ++ prefix` has a known `dropLast` split at `u`, and `u` is the last element
    of `suffix`, then `suffix.dropLast ++ u :: prefix.dropLast` equals that same split.
    This links the suffix walk's interior vertices to the original split encoding. -/
@[simp, grind .]
private lemma list_suffix_dropLast_realign {α : Type*}
    {sfx pfx : List α} {u : α} {as bs : List α}
    (hne_sfx : sfx ≠ []) (hne_pfx : pfx ≠ [])
    (hu_last : sfx.getLast hne_sfx = u)
    (hfull_split : (sfx ++ pfx).dropLast = as ++ u :: bs) :
    sfx.dropLast ++ u :: pfx.dropLast = as ++ u :: bs := by
  have h1 : (sfx ++ pfx).dropLast = sfx.dropLast ++ u :: pfx.dropLast := by
    rw [List.dropLast_append_of_ne_nil hne_pfx,
        ← List.dropLast_append_getLast hne_sfx, hu_last]
    simp [List.append_assoc]
  rw [← h1]; exact hfull_split

/-- If `u` is the first vertex of `w.support.dropLast` entering `next`,
    then the suffix walk from `u` to `v` has interior vertices avoiding `visited ∪ next`.
    This is the invariant that allows the IH to be applied in the recursive BFS step. -/
@[simp, grind .]
lemma walk_suffix_avoids_visited_union_next (G : SimpleDiGraph α)
    (visited next : Finset α) (w : Walk α)
    (hw : Path.IsPathIn G w)
    (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (u : α) (hu_supp : u ∈ w.support) (hu_ne_hd : u ≠ w.head) (hu_next : u ∈ next)
    (as bs : List α)
    (heq_split : w.support.dropLast = as ++ u :: bs)
    (hu_prev : ∀ x ∈ as, x ∉ next) :
    let w' : Walk α := ⟨w.seq.dropUntil u hu_supp, dropUntil_iswalk w.seq u hu_supp w.valid⟩
    ∀ x ∈ w'.support, x ≠ w'.head → x ∉ visited ∪ next := by
  intro w' x hx hxu
  have hw'_head : w'.head = u := VertexSeq.head_dropUntil w.seq u hu_supp
  have hw'_path : Path.IsPathIn G w' := Path.IsPathIn.suffix G w u hu_supp hw
  have hx_supp : x ∈ w.support := VertexSeq.mem_dropUntil w.seq u x hu_supp hx
  -- x ∉ visited: lift x to w.support and apply hw_avoid;
  -- x ≠ w.head because w.support is nodup and w.head lies in the prefix, not the suffix w'
  have hlist := Walk.walk_support_split w u hu_supp hu_ne_hd
  have hw_head_pfx := Walk.walk_head_mem_prefix w u hu_supp
  have hx_ne_hd : x ≠ w.head :=
    (List.nodup_append.mp (hlist ▸ hw.2)).2.2 x hx w.head hw_head_pfx
  refine Finset.notMem_union.mpr ⟨hw_avoid x hx_supp hx_ne_hd, ?_⟩
  -- x ∉ next: x lies in w'.support.dropLast, which equals as (the prefix before u),
  -- and as is disjoint from next by hu_prev
  have hxu_val : x ≠ u := hw'_head ▸ hxu
  have hu_last : w'.support.getLast (List.ne_nil_of_mem hx) = u := by
    simp only [Walk.support, VertexSeq.toList_getLast_is_head]; exact hw'_head
  have hx_dL : x ∈ w'.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast hx (hu_last ▸ hxu_val)
  have heq2 := list_suffix_dropLast_realign
    (List.ne_nil_of_mem hx) (List.ne_nil_of_mem hw_head_pfx) hu_last (hlist ▸ heq_split)
  have hu_ndL : u ∉ w'.support.dropLast := by
    have := list_nodup_getLast_not_mem_dropLast (List.ne_nil_of_mem hx) hw'_path.2
    rwa [hu_last] at this
  have hu_nas : u ∉ as := fun h => absurd hu_next (hu_prev u h)
  exact hu_prev x (list_left_unique_split heq2 hu_ndL hu_nas ▸ hx_dL)

/-- For any positive-length path from the BFS frontier that avoids visited vertices,
    there exists a strictly shorter path from some vertex in the next frontier to the
    same endpoint, whose interior avoids `visited ∪ next`.
    This is the pure graph-combinatorial content of the BFS completeness inductive step. -/
@[simp]
lemma bfs_inductive_step_witness (G : SimpleDiGraph α)
    (frontier visited : Finset α)
    (next : Finset α)
    (hnext_def : next = (frontier.biUnion (fun u ↦ N⁺(G,u))) \ visited)
    (w : Walk α) (hw : Path.IsPathIn G w)
    (hw_head : w.head ∈ frontier) (h_len : 0 < w.length)
    (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (hfv : frontier ⊆ visited) :
    ∃ w' : Walk α,
      w'.head ∈ next ∧ w'.tail = w.tail ∧ Path.IsPathIn G w' ∧
      w'.length < w.length ∧
      ∀ x ∈ w'.support, x ≠ w'.head → x ∉ visited ∪ next := by
  obtain ⟨u, hu_supp, hu_next, hu_ne_hd, as, bs, heq_split, hu_prev⟩ :=
    first_next_entry_of_path G frontier visited next hnext_def w hw hw_head h_len hw_avoid hfv
  let w' : Walk α := ⟨w.seq.dropUntil u hu_supp, dropUntil_iswalk w.seq u hu_supp w.valid⟩
  have hw'_head : w'.head = u := VertexSeq.head_dropUntil w.seq u hu_supp
  exact ⟨w', hw'_head ▸ hu_next, Walk.walk_tail_dropUntil w u hu_supp,
    Path.IsPathIn.suffix G w u hu_supp hw,
    VertexSeq.dropUntil_length_lt_of_ne_head hu_supp hu_ne_hd,
    walk_suffix_avoids_visited_union_next G visited next w hw hw_avoid
      u hu_supp hu_ne_hd hu_next as bs heq_split hu_prev⟩

/-- Appending an unvisited out-neighbor to a simple path yields a longer simple path
    from the same root, with the new vertex as its only new support element. -/
@[simp]
lemma path_extend_by_edge (G : SimpleDiGraph α)
    (root v_src u : α) (visited : Finset α)
    (w_v : Walk α) (hw_path : Path.IsPathIn G w_v)
    (hw_head : w_v.head = root) (hw_tail : w_v.tail = v_src)
    (hw_supp : ∀ x ∈ w_v.support, x ∈ visited)
    (hedg : (v_src, u) ∈ G.edgeSet) (hu_not_vis : u ∉ visited) :
    ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = u ∧
      (w.length : ℕ∞) = w_v.length + 1 ∧ ∀ x ∈ w.support, x ∈ visited ∪ {u} := by
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
    push_cast [hlen]; ring
  · intro x hx
    simp only [Walk.append_single, Walk.support, VertexSeq.toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
    · exact Finset.mem_union_left _ (hw_supp x hx)

/-- If every current-frontier vertex has a path of length `d` from root through `visited`,
    then every next-frontier vertex has a path of length `d+1` from root through `visited ∪ next`.
    This is the BFS level-invariant propagation: the soundness analogue of
    `bfs_inductive_step_witness`. -/
@[simp]
lemma next_frontier_has_paths (G : SimpleDiGraph α)
    (root : α) (visited frontier : Finset α) (d : ℕ)
    (next : Finset α)
    (hnext_def : next = (frontier.biUnion (fun u ↦ N⁺(G,u))) \ visited)
    (h_front : ∀ v ∈ frontier,
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited) :
    ∀ u ∈ next, ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = u ∧
      (w.length : ℕ∞) = d + 1 ∧ ∀ x ∈ w.support, x ∈ visited ∪ next := by
  intro u hu_next
  have hu_in_next : u ∈ next := hu_next
  simp only [hnext_def, Finset.mem_sdiff, Finset.mem_biUnion] at hu_next
  obtain ⟨⟨v_src, hv_front, hv_neigh⟩, hu_not_vis⟩ := hu_next
  simp only [OutNeighbors, Finset.mem_filter] at hv_neigh
  obtain ⟨_, e, he_edge, he1, he2, _⟩ := hv_neigh
  have hedg : (v_src, u) ∈ G.edgeSet := by grind
  obtain ⟨w_v, hw_path, hw_head, hw_tail, hw_len, hw_supp⟩ := h_front v_src hv_front
  obtain ⟨w, hw_w, hw_w_head, hw_w_tail, hw_wlen, hw_wsupp⟩ :=
    path_extend_by_edge G root v_src u visited w_v hw_path hw_head hw_tail hw_supp hedg hu_not_vis
  exact ⟨w, hw_w, hw_w_head, hw_w_tail,
    by rw [hw_wlen, hw_len],
    fun x hx => by
      rcases Finset.mem_union.mp (hw_wsupp x hx) with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mp h ▸ hu_in_next)⟩

omit [DecidableEq α] in
/-- The trivial length-0 path at the BFS root satisfies all `bfs_sound` `h_front` conditions
    for the initial call. This is the BFS initialization invariant: the singleton frontier
    `{root}` already has a valid path witness of length 0 for every vertex it contains. -/
@[simp, grind .]
lemma bfs_initial_front_invariant (G : SimpleDiGraph α) (root : α)
    (h_root : root ∈ G.vertexSet) :
    ∀ u ∈ ({root} : Finset α),
      ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = u ∧
        (w.length : ℕ∞) = 0 ∧ ∀ x ∈ w.support, x ∈ ({root} : Finset α) := by
  intro u hu
  have hu_eq : u = root := Finset.mem_singleton.mp hu
  exact ⟨
    ⟨.singleton root, .singleton root⟩,
    ⟨IsWalkIn.singleton root h_root, by simp [Walk.IsPath, Walk.support, VertexSeq.toList]⟩,
    rfl,
    hu_eq.symm,
    by simp [Walk.length, VertexSeq.length],
    fun x hx => by
      simp only [support, VertexSeq.toList, List.mem_cons, List.not_mem_nil, or_false] at hx
      exact Finset.mem_singleton.mpr hx⟩

end bfsBattery

/-! ## BFS core algorithm and the derived properties -/
namespace bfsAlgorithm

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
  have hnext_nonempty : next.Nonempty := Finset.nonempty_of_ne_empty h_next_ne
  -- *Containment* (`hnext_sub`): `next ⊆ V(G) \ visited`.
  -- Every element of `next` is an out-neighbour of some frontier vertex —
  -- hence in V(G) — and excluded from `visited` by construction (`next_subset_unvisited`).
  have hnext_sub : next ⊆ V(G) \ visited := bfsBattery.next_subset_unvisited G frontier visited
  -- *Positivity* (`hpos`): because `next` is nonempty and contained in `V(G) \ visited`,
  -- that set is also nonempty, so its cardinality is at least 1.
  have hpos : 0 < (V(G) \ visited).card :=
    Finset.card_pos.mpr (hnext_nonempty.mono hnext_sub)
  -- *Decrease* (`h`): `decreasing_unvisited_vertices_count` (instantiated at
  -- `m = |V(G) \ visited| - 1`) packages the set-identity, partition, and
  -- non-emptiness argument; `hm` closes by `omega` using `hpos`.
  -- Conclusion: `|V(G) \ (visited ∪ next)| ≤ |V(G) \ visited| - 1`.
  grind [bfsBattery.decreasing_unvisited_vertices_count G visited next ((V(G) \ visited).card - 1)
    hnext_sub hnext_nonempty (by omega)]

/-- BFS distance map from `v` to all vertices of `G`.
    Reachable vertices receive their shortest-path distance (as `(d : ℕ∞)`);
    unreachable vertices receive `⊤` (infinity). -/
@[simp, grind .]
def bfsDistances (G : SimpleDiGraph α) (v : α) : α → ℕ∞ :=
  bfs G {v} {v} 0 (fun _ => ⊤)

/-- The shortest distance from `v₁` to `v₂` in directed graph `G`.
    Returns `⊤` if `v₂` is unreachable from `v₁`. Computed via BFS. -/
@[simp, grind .]
def bfsDistance (G : SimpleDiGraph α) (v₁ : α) (v₂ : α) : ℕ∞ :=
  bfsDistances G v₁ v₂

/-- BFS returns `dist` unchanged when the frontier is empty. -/
@[simp, grind .]
lemma bfs_of_empty_frontier (G : SimpleDiGraph α) (visited : Finset α)
    (d : ℕ) (dist : α → ℕ∞) :
    bfs G visited ∅ d dist = dist := by simp [bfs]

/-- When the frontier is non-empty but the next frontier is empty,
    BFS records the current frontier at distance `d` and stops. -/
@[simp, grind .]
lemma bfs_of_empty_next (G : SimpleDiGraph α) (visited frontier : Finset α)
    (d : ℕ) (dist : α → ℕ∞)
    (h_fe : frontier ≠ ∅)
    (h_ne : (frontier.biUnion (fun v ↦ N⁺(G,v))) \ visited = ∅) :
    bfs G visited frontier d dist =
      fun u => if u ∈ frontier then (d : ℕ∞) else dist u := by simp_all [bfs]

/-- When both the frontier and the next frontier are non-empty, BFS advances one level. -/
@[simp, grind .]
lemma bfs_of_nonempty_next (G : SimpleDiGraph α) (visited frontier : Finset α)
    (d : ℕ) (dist : α → ℕ∞) (h_fe : frontier ≠ ∅)
    (h_ne : (frontier.biUnion (fun v ↦ N⁺(G,v))) \ visited ≠ ∅) :
    bfs G visited frontier d dist =
      bfs G (visited ∪ (frontier.biUnion (fun v ↦ N⁺(G, v))) \ visited)
          ((frontier.biUnion (fun v ↦ N⁺(G, v))) \ visited) (d + 1)
          (fun u => if u ∈ frontier then (d : ℕ∞) else dist u) := by grind [bfs]

/-- When BFS closes a layer (next is empty), any vertex not in the frontier keeps its distance. -/
@[simp, grind .]
lemma bfs_dist_stable_of_empty_next (G : SimpleDiGraph α)
    (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞)
    (v : α) (h_frontier : frontier ≠ ∅)
    (h_next : (frontier.biUnion (fun u ↦ N⁺(G,u))) \ visited = ∅)
    (hv_fron : v ∉ frontier) :
    bfs G visited frontier d dist v = dist v := by grind

end bfsAlgorithm

namespace bfsCorrectness

open bfsBattery bfsAlgorithm

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
@[simp, grind .]
lemma bfs_stable (G : SimpleDiGraph α)
    (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞)
    (v : α) (hv_vis : v ∈ visited) (hv_fron : v ∉ frontier) :
    bfs G visited frontier d dist v = dist v := by
  -- `bfs` is not structurally recursive, so we cannot induct on it directly.
  -- Instead, induct on an upper bound `m` for `(V(G) \ visited).card`;
  -- the recursive call shrinks this measure, so the IH applies to it.
  suffices key : ∀ (m : ℕ) (visited frontier : Finset α) (d : ℕ) (dist : α → ℕ∞),
      (V(G) \ visited).card ≤ m → v ∈ visited → v ∉ frontier →
      bfs G visited frontier d dist v = dist v from key _ _ _ _ _ le_rfl hv_vis hv_fron
  intro m
  induction m with
  | zero =>
    -- All vertices are already visited (unvisited set is empty), so `next = ∅`
    intro visited frontier d dist hm hv_vis hv_fron
    -- frontier = ∅: bfs returns `dist` unchanged;
    -- frontier ≠ ∅: `next = ∅`, so bfs closes the layer without changing `dist v` (v ∉ frontier).
    by_cases h_empty : frontier = ∅ <;> simp_all
  | succ m ih =>
    intro visited frontier d dist hm hv_vis hv_fron
    by_cases h_empty : frontier = ∅
    · -- frontier = ∅: bfs immediately returns `dist` unchanged.
      simp only [h_empty, bfs_of_empty_frontier]
    · by_cases h_next_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅
      · -- next = ∅: bfs closes the layer; `dist v` is unchanged because v ∉ frontier.
        exact bfs_dist_stable_of_empty_next G visited frontier d dist v h_empty h_next_empty hv_fron
      · -- next ≠ ∅: bfs recurses on `visited ∪ next` with the updated distance function.
        -- We apply the IH: `v` remains visited (v ∈ visited ⊆ visited ∪ next),
        -- `v ∉ next` (next excludes visited vertices), and the measure decreases strictly.
        -- After the IH reduces the recursive call, `dist' v = dist v` since v ∉ frontier.
        rw [congr_fun (bfs_of_nonempty_next G visited frontier d dist h_empty h_next_empty) v]
        grind

/-- BFS assigns exactly distance `d` to any vertex in the current frontier,
    regardless of whether the next BFS frontier is empty or not. -/
@[simp, grind .]
lemma bfs_frontier_dist (G : SimpleDiGraph α) (visited frontier : Finset α)
    (d : ℕ) (init_dist : α → ℕ∞) (v : α)
    (h_frontier : frontier ≠ ∅)
    (hv : v ∈ frontier)
    (hfv : frontier ⊆ visited) :
    bfs G visited frontier d init_dist v = d := by
  -- next = ∅: BFS closes the layer
  -- next ≠ ∅: BFS recurses (this requires `lemma bfs_stable`, see commit history)
  by_cases h_next : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅ <;> simp_all
  grind

/-- Helper lemma to prove `bfs_complete`:
    If a simple path of length k ending at v exists whose head lies in frontier
    and whose non-head vertices avoid visited, then BFS records v with distance ≤ d + k.
    `m` is an upper bound on `w.length` used as the induction variable. -/
@[simp, grind .]
lemma bfs_complete_aux (G : SimpleDiGraph α) (v : α)
    (m : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    (w : Walk α) (hw : Path.IsPathIn G w) (hw_head : w.head ∈ frontier)
    (hw_tail : w.tail = v) (hw_avoid : ∀ x ∈ w.support, x ≠ w.head → x ∉ visited)
    (hfv : frontier ⊆ visited)
    (hn : w.length < m) :
    bfs G visited frontier d init_dist v ≤ d + w.length := by
  induction m generalizing visited frontier d init_dist w with
  | zero => simp at hn
  | succ m ih =>
    by_cases h_frontier : frontier = ∅
    · simp [h_frontier] at hw_head
    · rcases Nat.eq_zero_or_pos w.length with h_len | h_len
      · -- w.length = 0: v is in the frontier; BFS assigns exactly d
        have hv_front : v ∈ frontier :=
          hw_tail ▸ (Walk.head_eq_tail_of_length_zero w h_len ▸ hw_head)
        rw [bfs_frontier_dist G visited frontier d init_dist v h_frontier hv_front hfv]
        simp [h_len]
      · -- w.length > 0: expand BFS one step; case-split on whether next is empty
        unfold bfs
        set next  := (Finset.biUnion frontier (fun u ↦ N⁺(G, u))) \ visited
        set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
        simp only [if_neg h_frontier]
        by_cases h_next : next = ∅
        · -- next = ∅: first out-neighbor of w.head would lie in next = ∅, contradiction
          obtain ⟨a₁, _, _, _, ha₁_next⟩ := walk_first_succ_mem_next
            G frontier visited next rfl w hw.1 h_len hw_head hw_avoid
          simp [h_next] at ha₁_next
        · -- next ≠ ∅: BFS recurses; get shorter suffix from next frontier and apply IH
          simp only [if_neg h_next]
          obtain ⟨w', hw'_head, hw'_tail, hw'_path, hw'_lt_w, hw'_avoid⟩ :=
            bfs_inductive_step_witness G frontier visited next rfl w hw
              hw_head h_len hw_avoid hfv
          have hbound := ih (visited ∪ next) next (d + 1) dist' w' hw'_path hw'_head
            (hw'_tail.trans hw_tail) hw'_avoid Finset.subset_union_right (by omega)
          calc bfs G (visited ∪ next) next (d + 1) dist' v
              ≤ ↑(d + 1) + ↑w'.length := hbound
            _ ≤ ↑d + ↑w.length        := by
                exact_mod_cast (show d + 1 + w'.length ≤ d + w.length by omega)

/-- Sub Goal A for `bfs_correct`:
    If a path of length `k` exists from `root` vertex to `v` in `G`,
    then BFS returns `distance ≤ k` for `v`. -/
@[simp, grind .]
theorem bfs_complete (G : SimpleDiGraph α) (root : α) (v : α) (k : ℕ)
    (hk : ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧ (w.length : ℕ∞) = k) :
    bfsDistance G root v ≤ k := by
  obtain ⟨w, hw, hw_head, hw_tail, hw_len⟩ := hk
  rw [← hw_len]
  simp only [bfsDistance, bfsDistances]
  have haux := bfs_complete_aux G v (#V(G)) {root} {root} 0 (fun _ => ⊤) w
    hw (Finset.mem_singleton.mpr hw_head) hw_tail
    (fun x _ hne => mt Finset.mem_singleton.mp (hw_head ▸ hne))
    (Finset.Subset.refl _) (Path.path_length_lt_card_vertices G w hw)
  simp only [Nat.cast_zero, zero_add] at haux
  exact_mod_cast haux

/-- Sub Goal B for `bfs_correct`:
    If `bfs G visited frontier d dist v` returns a finite distance,
    then there exists a valid path in `G` from `root` to `v` of that length. -/
@[simp]
theorem bfs_sound (G : SimpleDiGraph α) (root : α) (v : α)
    (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞)
    -- every distance already in `init_dist` corresponds to a real path from `root`
    (h_dist : ∀ v : α, init_dist v ≠ ⊤ →
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = init_dist v)
    -- every `frontier` vertex has a path of length `d` whose vertices lie in `visited`
    (h_front : ∀ v ∈ frontier,
        ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited)
    (hv : bfs G visited frontier d init_dist v ≠ ⊤) :
    ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
        (w.length : ℕ∞) = bfs G visited frontier d init_dist v := by
  -- Induct on an upper bound for the termination measure (V(G) \ visited).card
  suffices key : ∀ (m : ℕ) (visited frontier : Finset α) (d : ℕ) (init_dist : α → ℕ∞),
      (V(G) \ visited).card ≤ m →
      (∀ v : α, init_dist v ≠ ⊤ →
          ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
            (w.length : ℕ∞) = init_dist v) →
      (∀ v ∈ frontier,
          ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
            (w.length : ℕ∞) = d ∧ ∀ x ∈ w.support, x ∈ visited) →
      bfs G visited frontier d init_dist v ≠ ⊤ →
      ∃ w : Walk α, Path.IsPathIn G w ∧ w.head = root ∧ w.tail = v ∧
          (w.length : ℕ∞) = bfs G visited frontier d init_dist v from
    key _ _ _ _ _ le_rfl h_dist h_front hv
  intro m
  induction m with
  | zero =>
    intro visited frontier d init_dist hm h_dist h_front hv
    -- next = ∅ because V(G) ⊆ visited (card ≤ 0)
    have hnext_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅ := by simp_all
    by_cases h_empty : frontier = ∅
    · -- frontier = ∅: bfs returns init_dist
      simp_all
    · -- frontier ≠ ∅, next = ∅: bfs returns fun u => if u ∈ frontier then d else init_dist u
      grind
  | succ m ih =>
    intro visited frontier d init_dist hm h_dist h_front hv
    by_cases h_empty : frontier = ∅
    · simp only [h_empty, bfs_of_empty_frontier] at hv ⊢; exact h_dist v hv
    · by_cases h_next_empty : (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited = ∅
      · -- next = ∅: bfs returns fun u => if u ∈ frontier then d else init_dist u
        grind
      · -- next ≠ ∅: bfs recurses; apply IH with smaller measure
        have hbfs_eq := congr_fun
          (bfs_of_nonempty_next G visited frontier d init_dist h_empty h_next_empty) v
        rw [hbfs_eq] at hv ⊢
        set next  := (frontier.biUnion (fun u ↦ N⁺(G, u))) \ visited
        set dist' := fun u => if u ∈ frontier then (d : ℕ∞) else init_dist u
        have hmeasure : (V(G) \ (visited ∪ next)).card ≤ m := by grind
        apply ih (visited ∪ next) next (d + 1) dist' hmeasure
        · -- h_dist': ∀ u, dist' u ≠ ⊤ → ∃ path ...
          grind
        · -- h_front': BFS level-invariant propagates from frontier to next
          exact next_frontier_has_paths G root visited frontier d next rfl h_front
        · exact hv

theorem bfsDistance_correct (G : SimpleDiGraph α) (v₁ v₂ : α)
    (h₁ : v₁ ∈ G.vertexSet) :
    bfsDistance G v₁ v₂ = Path.shortestPath G v₁ v₂ := by
  apply le_antisymm
  · -- Goal A: Distance G v₁ v₂ ≤ shortestPath G v₁ v₂
    unfold Path.shortestPath
    apply le_iInf; intro w
    apply le_iInf; intro ⟨hw_path, hw_head, hw_tail⟩
    exact bfs_complete G v₁ v₂ w.length ⟨w, hw_path, hw_head, hw_tail, rfl⟩
  · -- Goal B: shortestPath G v₁ v₂ ≤ Distance G v₁ v₂
    unfold Path.shortestPath
    by_cases hv : bfsDistance G v₁ v₂ = ⊤
    · rw [hv]; exact le_top
    · simp only [bfsDistance, bfsDistances] at hv ⊢
      obtain ⟨w, hw_path, hw_head, hw_tail, hw_len⟩ :=
        bfs_sound G v₁ v₂ {v₁} {v₁} 0 (fun _ => ⊤)
          -- h_dist: init_dist = ⊤ everywhere, so hypothesis is vacuous
          (fun u hu => absurd rfl hu)
          -- h_front: trivial path at root satisfies the BFS initialization invariant
          (bfs_initial_front_invariant G v₁ h₁)
          hv
      exact iInf_le_of_le w (iInf_le_of_le ⟨hw_path, hw_head, hw_tail⟩ (le_of_eq hw_len))

end bfsCorrectness

-- #TODOs:
-- 1. etedn bfs to produce a search tree (or forest) and prove its properties
-- 2. extend to undirected graphs (should be straightforward hopefully,
--    e.g. by adding the reverse edge in the BFS steps)
