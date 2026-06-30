/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.SimplePath

/-!
# Simple cycles

A `SimpleCycle α` is a closed `SimpleWalk α` of length at least three whose
interior (the walk with its final repeated vertex dropped) is a simple path.
It is represented as a subtype of `SimpleWalk`.

The length-≥-3 bound is the *undirected* convention; the directed notion
(which admits length-two cycles) will get its own `SimpleDiCycle`. The `arcs`
API here only reflects a chosen traversal orientation and is not canonical.

## Main definitions

* `SimpleWalk.IsCycle` — a closed simple walk whose dropped-tail walk is a path.
* `SimpleCycle` — a simple walk bundled with a proof of `SimpleWalk.IsCycle`.
-/

variable {α : Type*}

namespace SimpleWalk

/-- A simple walk is a cycle when it is closed, has length at least three,
and its dropped-tail walk is a path. -/
@[grind] def IsCycle (w : SimpleWalk α) : Prop :=
  3 ≤ w.length ∧ w.closed ∧ w.dropTail.nodup

/-- Reversal preserves the simple-cycle property. -/
lemma isCycle_reverse (w : SimpleWalk α) (h : IsCycle w) :
    IsCycle w.reverse := by
  rcases h with ⟨hlen, hclosed, hnodup⟩
  refine ⟨?_, ?_, ?_⟩
  · change 3 ≤ w.val.reverse.length
    simpa using hlen
  · change w.val.reverse.closed
    simpa [VertexSeq.closed] using hclosed.symm
  · exact VertexSeq.nodup_reverse_dropTail_of_cycle w.val hclosed hnodup

end SimpleWalk

/-- A simple cycle is a simple walk that is a cycle. -/
def SimpleCycle (α : Type*) :=
  { w : SimpleWalk α // SimpleWalk.IsCycle w }

namespace SimpleCycle

/-! ## Basic accessors -/

/-- The underlying simple walk. -/
abbrev val (c : SimpleCycle α) : SimpleWalk α := c.1

/-- The underlying vertex sequence. -/
abbrev vertices (c : SimpleCycle α) : VertexSeq α := c.val.val

/-- The list of vertices visited by the cycle. -/
abbrev support (c : SimpleCycle α) : List α := (vertices c).toList

/-- The unordered edges traversed by the cycle. -/
abbrev edges (c : SimpleCycle α) : List (Sym2 α) := (vertices c).edges

/-- The directed arcs traversed by the cycle. -/
abbrev arcs (c : SimpleCycle α) : List (α × α) := (vertices c).arcs

/-- The first vertex of the cycle. -/
abbrev head (c : SimpleCycle α) : α := (vertices c).head

/-- The last vertex of the cycle (equal to its head, since a cycle is closed). -/
abbrev tail (c : SimpleCycle α) : α := (vertices c).tail

/-- The number of edges in the cycle. -/
abbrev length (c : SimpleCycle α) : ℕ := (vertices c).length

/-- The interior of the cycle: the vertex sequence with its final (repeated)
vertex dropped. -/
def interior (c : SimpleCycle α) : SimplePath α :=
  ⟨c.val.dropTail, c.2.2.2⟩

/-- A cycle is closed: its first and last vertex coincide. -/
lemma closed (c : SimpleCycle α) : c.val.closed := c.2.2.1

/-- A simple cycle is, in particular, a simple walk. -/
instance : Coe (SimpleCycle α) (SimpleWalk α) :=
  ⟨val⟩

/-! ## reverse -/

/-- Reverse the orientation of a simple cycle. -/
@[grind] def reverse (c : SimpleCycle α) : SimpleCycle α :=
  ⟨c.val.reverse, SimpleWalk.isCycle_reverse c.val c.2⟩

/-! ## reroot -/

/-- Re-root a simple cycle at any vertex on it. -/
def reroot [DecidableEq α] (c : SimpleCycle α) (u : α) (hu : u ∈ vertices c) :
    SimpleCycle α :=
  if hhead : u = head c then
    c
  else
    ⟨(c.val.suffixFrom u hu).glue (c.val.prefixUntil u hu) (by
        change (c.val.val.suffixFrom u hu).tail = (c.val.val.prefixUntil u hu).head
        rw [VertexSeq.tail_suffixFrom, VertexSeq.head_prefixUntil]
        exact (SimpleCycle.closed c).symm),
      by
        have hsplit := VertexSeq.dropTail_prefixUntil_append_suffixFrom
          (vertices c) u hu hhead
        let pre : VertexSeq α := (vertices c).prefixUntil u hu
        let suf : VertexSeq α := (vertices c).suffixFrom u hu
        have hpre_pos : pre.length ≠ 0 := by
          intro hz
          have h_eq := VertexSeq.head_eq_tail_of_length_zero pre hz
          have h_eq' : (vertices c).head = u := by
            simpa [pre] using h_eq
          exact hhead h_eq'.symm
        have hsuf_pos : suf.length ≠ 0 := by
          intro hz
          have h_eq := VertexSeq.head_eq_tail_of_length_zero suf hz
          have h_eq' : u = (vertices c).tail := by
            simpa [suf] using h_eq
          exact hhead (by
            rw [← SimpleCycle.closed c] at h_eq'
            exact h_eq')
        have hsplit' : pre.dropTail.append suf = vertices c := by
          simpa [pre, suf] using hsplit
        have hsplitLen := congrArg VertexSeq.length hsplit'
        have hsplitLen' : pre.dropTail.length + suf.length + 1 = (vertices c).length := by
          simpa [VertexSeq.length_append] using hsplitLen
        have hpreLen := VertexSeq.dropTail_length_succ pre hpre_pos
        have hsufLen := VertexSeq.dropTail_length_succ suf hsuf_pos
        have hdropSplit := congrArg VertexSeq.dropTail hsplit'
        have hleft : (pre.dropTail.append suf.dropTail).nodup := by
          have hdrop :
              (pre.dropTail.append suf).dropTail = pre.dropTail.append suf.dropTail :=
            VertexSeq.dropTail_append_of_length_ne_zero pre.dropTail suf hsuf_pos
          rw [← hdrop]
          rw [hdropSplit]
          exact c.2.2.2
        have hrotDrop : (suf.dropTail.append pre).dropTail = suf.dropTail.append pre.dropTail :=
          VertexSeq.dropTail_append_of_length_ne_zero suf.dropTail pre hpre_pos
        have hsuf_pos' : ((c.val.suffixFrom u hu).val.length ≠ 0) := by
          simpa [suf] using hsuf_pos
        simp [SimpleWalk.IsCycle, SimpleWalk.glue, hsuf_pos']
        refine ⟨?_, ?_, ?_⟩
        · change 3 ≤ (suf.dropTail.append pre).length
          have hrotLen : (suf.dropTail.append pre).length = (vertices c).length := by
            simp [VertexSeq.length_append]
            omega
          rw [hrotLen]
          exact c.2.1
        · change (suf.dropTail.append pre).closed
          simp [VertexSeq.closed, pre, suf]
        · change (suf.dropTail.append pre).dropTail.nodup
          rw [hrotDrop]
          exact VertexSeq.nodup_append_comm pre.dropTail suf.dropTail hleft⟩

/-! ## edges -/

/-- The number of traversed edges equals the cycle's length. -/
@[simp] lemma length_edges (c : SimpleCycle α) : (edges c).length = length c :=
  VertexSeq.length_edges (vertices c)

/-- A simple cycle has at least three traversed edges. -/
lemma three_le_length_edges (c : SimpleCycle α) : 3 ≤ (edges c).length := by
  rw [length_edges]
  exact c.2.1

/-- A simple cycle traverses at least one edge. -/
lemma edges_ne_nil (c : SimpleCycle α) : edges c ≠ [] := by
  intro h
  have hlen := three_le_length_edges c
  rw [h] at hlen
  simp at hlen

/-- The edge list is the interior path's edge list plus the closing edge. -/
lemma interior_edges (c : SimpleCycle α) :
    edges c = SimplePath.edges (interior c) ++ [s(SimplePath.tail (interior c), tail c)] := by
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hpos : (vertices c).length ≠ 0 := by omega
  change (vertices c).edges =
    (vertices c).dropTail.edges ++ [s((vertices c).dropTail.tail, (vertices c).tail)]
  rw [VertexSeq.edges_eq_dropTail_concat_of_length_ne_zero (vertices c) hpos]
  simp [List.concat_eq_append]

/-- A simple cycle traverses each edge at most once. -/
lemma edges_nodup (c : SimpleCycle α) : (edges c).Nodup := by
  rw [interior_edges]
  rw [List.nodup_append]
  refine ⟨SimplePath.edges_nodup (interior c), by simp, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst hb
  subst hab
  have hclosedTail : tail c = SimplePath.head (interior c) := by
    change (vertices c).tail = (vertices c).dropTail.head
    rw [VertexSeq.head_dropTail]
    exact (closed c).symm
  have hmem :
      s((SimplePath.vertices (interior c)).head,
        (SimplePath.vertices (interior c)).tail) ∈
        (SimplePath.vertices (interior c)).edges := by
    simpa [hclosedTail, Sym2.eq_swap] using ha
  have hle := VertexSeq.length_le_one_of_mem_edges_head_tail
    (SimplePath.vertices (interior c))
    (SimplePath.nodup (interior c)) hmem
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hpos : (vertices c).length ≠ 0 := by omega
  have hdrop := VertexSeq.dropTail_length_succ (vertices c) hpos
  change (vertices c).dropTail.length + 1 = (vertices c).length at hdrop
  change (vertices c).dropTail.length ≤ 1 at hle
  omega

/-- Reversal reverses the edge list. -/
@[simp] lemma edges_reverse (c : SimpleCycle α) :
    edges (reverse c) = (edges c).reverse :=
  VertexSeq.edges_reverse (vertices c)

/-! ## arcs -/

/-- The number of traversed arcs equals the cycle's length. -/
@[simp] lemma length_arcs (c : SimpleCycle α) : (arcs c).length = length c :=
  VertexSeq.length_arcs (vertices c)

/-- A simple cycle has at least three traversed arcs. -/
lemma three_le_length_arcs (c : SimpleCycle α) : 3 ≤ (arcs c).length := by
  rw [length_arcs]
  exact c.2.1

/-- A simple cycle traverses at least one arc. -/
lemma arcs_ne_nil (c : SimpleCycle α) : arcs c ≠ [] := by
  intro h
  have hlen := three_le_length_arcs c
  rw [h] at hlen
  simp at hlen

/-- The arc list is the interior path's arc list plus the closing arc. -/
lemma interior_arcs (c : SimpleCycle α) :
    arcs c =
      SimplePath.arcs (interior c) ++ [(SimplePath.tail (interior c), tail c)] := by
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hpos : (vertices c).length ≠ 0 := by omega
  change (vertices c).arcs =
    (vertices c).dropTail.arcs ++ [((vertices c).dropTail.tail, (vertices c).tail)]
  rw [VertexSeq.arcs_eq_dropTail_concat_of_length_ne_zero (vertices c) hpos]
  simp [List.concat_eq_append]

/-- A simple cycle traverses each directed arc at most once. -/
lemma arcs_nodup (c : SimpleCycle α) : (arcs c).Nodup := by
  rw [interior_arcs]
  rw [List.nodup_append]
  refine ⟨SimplePath.arcs_nodup (interior c), by simp, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_singleton] at hb
  subst hb
  subst hab
  have hclosedTail : tail c = SimplePath.head (interior c) := by
    change (vertices c).tail = (vertices c).dropTail.head
    rw [VertexSeq.head_dropTail]
    exact (closed c).symm
  have hmem :
      ((SimplePath.vertices (interior c)).tail,
        (SimplePath.vertices (interior c)).head) ∈
        (SimplePath.vertices (interior c)).arcs := by
    simpa [hclosedTail] using ha
  have hle := VertexSeq.length_le_one_of_mem_arcs_tail_head
    (SimplePath.vertices (interior c))
    (SimplePath.nodup (interior c)) hmem
  have hlen : 3 ≤ (vertices c).length := c.2.1
  have hpos : (vertices c).length ≠ 0 := by omega
  have hdrop := VertexSeq.dropTail_length_succ (vertices c) hpos
  change (vertices c).dropTail.length + 1 = (vertices c).length at hdrop
  change (vertices c).dropTail.length ≤ 1 at hle
  omega

/-- Reversal reverses the arc list and swaps every arc's endpoints. -/
@[simp] lemma arcs_reverse (c : SimpleCycle α) :
    arcs (reverse c) = (arcs c).reverse.map (fun a : α × α => (a.2, a.1)) :=
  VertexSeq.arcs_reverse (vertices c)

/-! ## constructors -/

/-- Close a simple path by adding an edge from its tail back to its head. -/
def ofPathClosing (p : SimplePath α)
    (hlen : 2 ≤ (SimplePath.vertices p).length) :
    SimpleCycle α :=
  let w : SimpleWalk α :=
    ⟨VertexSeq.cons (SimplePath.vertices p) (SimplePath.head p), by
      have hp : (SimplePath.vertices p).nodup := SimplePath.nodup p
      have htail_ne :
          (SimplePath.vertices p).tail ≠ (SimplePath.vertices p).head := by
        intro h
        have hzero := VertexSeq.length_zero_of_nodup_head_eq_tail
          (SimplePath.vertices p) hp h.symm
        omega
      exact ⟨p.val.nonstalling, htail_ne⟩⟩
  ⟨w, by
    refine ⟨?_, ?_, ?_⟩
    · change 3 ≤ (VertexSeq.cons (SimplePath.vertices p)
          (SimplePath.head p)).length
      simp [VertexSeq.length]
      omega
    · change (VertexSeq.cons (SimplePath.vertices p)
          (SimplePath.head p)).closed
      simp [VertexSeq.closed]
    · change (VertexSeq.cons (SimplePath.vertices p)
          (SimplePath.head p)).dropTail.nodup
      simpa using SimplePath.nodup p⟩

end SimpleCycle
