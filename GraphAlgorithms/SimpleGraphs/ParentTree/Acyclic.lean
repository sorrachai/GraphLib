import GraphAlgorithms.SimpleGraphs.ParentTree.WalkIn

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

open Finset Walk VertexSeq ParentTree

namespace ParentTreeAcyclic

/-- A neighbour whose level is no greater than `v` must be the parent of `v`. -/
lemma max_neighbour_eq_parent (G : ParentTree α) (v u : α)
    (hv : v ∈ Vₚ(G)) (hu : u ∈ Nₚ(G, v))
    (hmax : G.level u ≤ G.level v) :
    u = G.parent v := by
  rcases edge_inclusion G v u hu with huv | huv
  · have huV := edge_imp_in_v G v u hv hu
    have hu_ne : u ≠ v := by
      simp only [mem_sdiff, mem_singleton] at hu
      exact hu.2
    have hu_pos : 0 < G.level u := by
      by_contra h
      have hroot := (G.root u huV).mp (by omega)
      exact hu_ne (hroot.trans huv.symm)
    have hord := G.ordering u huV hu_pos
    rw [← huv] at hord
    omega
  · exact huv

omit [DecidableEq α] in
/-- The two vertices next to the root of a cycle are distinct. -/
lemma cycle_neighbours_ne (w : Walk α) (hc : IsCycle w) :
    w.seq.dropHead.head ≠ w.dropTail.tail := by
  rcases hc with ⟨hlen, _, hpath⟩
  change 3 ≤ w.seq.length at hlen
  have hdrop_len : w.dropTail.length + 1 = w.length := by
    cases w
    induction valid <;> grind
  have hlen' : 2 ≤ w.dropTail.length := by
    change 2 ≤ w.seq.dropTail.length
    change w.seq.dropTail.length + 1 = w.seq.length at hdrop_len
    omega
  have hfirst : w.seq.dropHead.head = w.dropTail.seq.dropHead.head := by
    exact droptail_drophead_head_eq_drophead_head w.seq (by omega)
  have hzero := list_pos_tail_is_0 w.dropTail.seq
  have hlast := list_pos_drop_head_is_minus1 w.dropTail.seq (by
    change 1 ≤ w.dropTail.length
    omega)
  intro heq
  have hinj := hpath.get_inj_iff
    (i := ⟨0, by simp [Walk.support, toList_length_eq]⟩)
    (j := ⟨w.dropTail.length - 1, by simp [Walk.support, toList_length_eq]⟩)
  change (w.dropTail.seq.toList.get ⟨0, _⟩ =
      w.dropTail.seq.toList.get ⟨w.dropTail.length - 1, _⟩) ↔ _ at hinj
  rw [hzero, hlast] at hinj
  rw [← hfirst, heq] at hinj
  grind

/-- Appending compatible walks in a parent tree preserves `IsWalkIn`. -/
lemma isWalkIn_append (G : ParentTree α) (w₁ w₂ : Walk α)
    (h₁ : IsWalkIn G w₁) (h₂ : IsWalkIn G w₂)
    (hjoin : w₁.tail = w₂.head) :
    IsWalkIn G (Walk.append w₁ w₂ hjoin) := by
  induction h₂ with
  | singleton v hv =>
      by_cases hz : w₁.length = 0
      · simp only [Walk.append, hz]
        exact IsWalkIn.singleton v hv
      · have heq : Walk.append w₁ ⟨.singleton v, .singleton v⟩ hjoin = w₁ := by
          apply Walk.ext
          simp only [Walk.append, hz]
          cases w₁
          induction valid <;> grind
        rw [heq]
        exact h₁
  | cons w u hw hedge ih =>
      have hjoin' : w₁.tail = w.head := hjoin
      have ih' := ih hjoin'
      have hedge' : u ∈ Nₚ(G, (Walk.append w₁ w hjoin').tail) := by
        rw [Walk.tail_on_tail]
        exact hedge
      have hc := IsWalkIn.cons (Walk.append w₁ w hjoin') u ih' hedge'
      have heq :
          Walk.append w₁ (w.append_single u (by grind)) hjoin =
            (Walk.append w₁ w hjoin').append_single u (by grind) := by
        apply Walk.ext
        simp only [Walk.append_single]
        simp only [Walk.append]
        split <;> grind
      rw [heq]
      exact hc

/-- Taking a prefix ending at a vertex preserves `IsWalkIn`. -/
lemma isWalkIn_takeUntil (G : ParentTree α) (w : Walk α) (v : α)
    (hv : v ∈ w.support) (hw : IsWalkIn G w) :
    IsWalkIn G ⟨w.seq.takeUntil v hv, takeUntil_iswalk w.seq v hv w.valid⟩ := by
  induction hw generalizing v with
  | singleton x hx =>
      simp only [support, VertexSeq.toList, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      subst v
      exact IsWalkIn.singleton x hx
  | cons w u hw hedge ih =>
      simp only [Walk.append_single, support, VertexSeq.toList, List.mem_cons] at hv
      simp only [Walk.append_single, VertexSeq.takeUntil]
      by_cases hv' : v ∈ w.seq.toList
      · simp only [hv', ↓reduceDIte]
        exact ih v hv'
      · simp only [hv', ↓reduceDIte]
        exact IsWalkIn.cons w u hw hedge

/-- Taking a suffix beginning at a vertex preserves `IsWalkIn`. -/
lemma isWalkIn_dropUntil (G : ParentTree α) (w : Walk α) (v : α)
    (hv : v ∈ w.support) (hw : IsWalkIn G w) :
    IsWalkIn G ⟨w.seq.dropUntil v hv, dropUntil_iswalk w.seq v hv w.valid⟩ := by
  induction hw generalizing v with
  | singleton x hx =>
      simp only [support, VertexSeq.toList, List.mem_cons,
        List.not_mem_nil, or_false] at hv
      subst v
      exact IsWalkIn.singleton x hx
  | cons w u hw hedge ih =>
      simp only [Walk.append_single, support, VertexSeq.toList, List.mem_cons] at hv
      simp only [Walk.append_single, VertexSeq.dropUntil]
      by_cases hv' : v ∈ w.seq.toList
      · simp only [hv', ↓reduceDIte]
        exact IsWalkIn.cons
          ⟨w.seq.dropUntil v hv', dropUntil_iswalk w.seq v hv' w.valid⟩ u
          (ih v hv') (by simpa using hedge)
      · simp only [hv', ↓reduceDIte]
        have htail := is_walk_in_tree_last G w hw
        have hu := edge_imp_in_v G w.tail u htail hedge
        exact IsWalkIn.singleton u hu

/-- Rerooting a cycle preserves `IsWalkIn`. -/
lemma isWalkIn_rerootCycle (G : ParentTree α) (w : Walk α)
    (hc : IsCycle w) (hw : IsWalkIn G w) (v : α) (hv : v ∈ w.support) :
    IsWalkIn G (w.rerootCycle hc v hv) := by
  unfold Walk.rerootCycle
  apply isWalkIn_append
  · exact isWalkIn_dropUntil G w v hv hw
  · exact isWalkIn_takeUntil G w v hv hw

omit [DecidableEq α] in
lemma mem_dropTail_toList (s : VertexSeq α) (x : α) :
    x ∈ s.dropTail.toList → x ∈ s.toList := by
  cases s with
  | singleton => simp [VertexSeq.dropTail, VertexSeq.toList]
  | cons s _ =>
      intro hx
      simp only [VertexSeq.dropTail] at hx
      simp only [VertexSeq.toList, List.mem_cons]
      exact Or.inr hx

/-- Rerooting does not introduce vertices that were absent from the original cycle. -/
lemma rerootCycle_support_subset (w : Walk α) (hc : IsCycle w)
    (v : α) (hv : v ∈ w.support) :
    ∀ x ∈ (w.rerootCycle hc v hv).support, x ∈ w.support := by
  intro x hx
  unfold Walk.rerootCycle at hx
  simp only [Walk.support] at hx ⊢
  unfold Walk.append at hx
  split at hx
  · exact mem_takeUntil w.seq v x hv hx
  · simp only [toList_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact mem_takeUntil w.seq v x hv hx
    · exact mem_dropUntil w.seq v x hv (mem_dropTail_toList _ _ hx)

omit [DecidableEq α] in
lemma mem_dropHead_toList (s : VertexSeq α) (x : α) :
    x ∈ s.dropHead.toList → x ∈ s.toList := by
  induction s with
  | singleton => simp [VertexSeq.dropHead, VertexSeq.toList]
  | cons s v ih =>
      cases s with
      | singleton _ =>
          simp only [VertexSeq.dropHead, VertexSeq.toList, List.mem_cons,
            List.not_mem_nil, or_false]
          exact fun h => Or.inl h
      | cons s _ =>
          simp only [VertexSeq.dropHead, VertexSeq.toList, List.mem_cons]
          grind

/-- Every graph represented by `ParentTree` contains no cycle. -/
theorem parent_tree_is_acyclic (G : ParentTree α) (w : Walk α)
    (hw : IsWalkIn G w) : ¬ IsCycle w := by
  intro hc
  have hs : w.support.toFinset.Nonempty := by
    refine ⟨w.head, ?_⟩
    simp only [List.mem_toFinset]
    exact VertexSeq.head_mem_toList w.seq
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image w.support.toFinset G.level hs
  have hv' : v ∈ w.support := by simpa using hv

  let c := w.rerootCycle hc v hv'
  have hc' : IsCycle c := isCycle_rerootCycle w hc v hv'
  have hw' : IsWalkIn G c := isWalkIn_rerootCycle G w hc hw v hv'
  have hc_len : 0 < c.length := by
    rcases hc' with ⟨hlen, _, _⟩
    omega
  have hc_head : c.head = v := by
    simp only [c, Walk.rerootCycle, Walk.head_on_head]
    exact VertexSeq.head_dropUntil w.seq v hv'
  have hc_tail : c.tail = v := by
    rcases hc' with ⟨_, hclosed, _⟩
    grind

  let a := c.seq.dropHead.head
  let b := c.dropTail.tail
  have ha_mem : a ∈ c.support := by
    apply mem_dropHead_toList c.seq a
    exact VertexSeq.head_mem_toList c.seq.dropHead
  have hb_mem : b ∈ c.support :=
    VertexSeq.dropTail_tail_mem_toList c.seq
  have haV : a ∈ Vₚ(G) := is_walk_in_tree_support G c hw' a ha_mem
  have hvV : v ∈ Vₚ(G) := is_walk_in_tree_support G w hw v hv'

  have hva : a ∈ Nₚ(G, v) := by
    have hfirst := is_walk_in_tree_first_second G c hw' hc_len
    have hsymm := edge_antisymm G a c.head haV hfirst
    simpa [hc_head, a] using hsymm
  have hvb : b ∈ Nₚ(G, v) := by
    have hlast := is_walk_in_tree_last_semilast G c hw' hc_len
    simpa [hc_tail, b] using hlast.2

  have ha_original := rerootCycle_support_subset w hc v hv' a ha_mem
  have hb_original := rerootCycle_support_subset w hc v hv' b hb_mem
  have ha_le : G.level a ≤ G.level v := hmax a (by simpa using ha_original)
  have hb_le : G.level b ≤ G.level v := hmax b (by simpa using hb_original)
  have ha_parent := max_neighbour_eq_parent G v a hvV hva ha_le
  have hb_parent := max_neighbour_eq_parent G v b hvV hvb hb_le

  have hab := cycle_neighbours_ne c hc'
  exact hab (by simpa [a, b] using ha_parent.trans hb_parent.symm)

end ParentTreeAcyclic
