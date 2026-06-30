/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.SimpleWalk

/-!
# Simple paths

A `SimplePath α` is a `SimpleWalk α` whose vertices are pairwise distinct.
This file keeps paths as a subtype of simple walks, so every path can be used
where a simple walk is expected.

## Main definitions

* `SimpleWalk.IsPath` — a simple walk with no repeated vertices.
* `SimplePath` — a simple walk bundled with a proof that its vertices are
  pairwise distinct.
-/

variable {α : Type*}

namespace SimpleWalk

/-- A simple walk is a path when it has no repeated vertices. -/
abbrev IsPath (w : SimpleWalk α) : Prop := w.nodup

end SimpleWalk

/-- A simple path is a simple walk with no repeated vertex. -/
def SimplePath (α : Type*) :=
  { w : SimpleWalk α // SimpleWalk.IsPath w }

namespace SimplePath

/-! ## Basic accessors -/

/-- The underlying simple walk. -/
abbrev val (p : SimplePath α) : SimpleWalk α := p.1

/-- The underlying vertex sequence. -/
abbrev vertices (p : SimplePath α) : VertexSeq α := p.val.val

/-- The list of vertices visited by the path. -/
abbrev support (p : SimplePath α) : List α := (vertices p).toList

/-- The unordered edges traversed by the path. -/
abbrev edges (p : SimplePath α) : List (Sym2 α) := (vertices p).edges

/-- The directed arcs traversed by the path. -/
abbrev arcs (p : SimplePath α) : List (α × α) := (vertices p).arcs

/-- The first vertex of the path. -/
abbrev head (p : SimplePath α) : α := (vertices p).head

/-- The last vertex of the path. -/
abbrev tail (p : SimplePath α) : α := (vertices p).tail

/-- The number of edges in the path. -/
abbrev length (p : SimplePath α) : ℕ := (vertices p).length

/-- A path has no repeated vertices. -/
lemma nodup (p : SimplePath α) : (vertices p).nodup := p.2


/-- A simple path is, in particular, a simple walk. -/
instance : Coe (SimplePath α) (SimpleWalk α) :=
  ⟨val⟩

/-! ## dropHead, dropTail -/

/-- Drop the first vertex of a path. Removing an endpoint preserves `nodup`. -/
def dropHead (p : SimplePath α) : SimplePath α :=
  ⟨p.val.dropHead, by
    exact VertexSeq.nodup_dropHead (vertices p) (nodup p)⟩

/-- Drop the last vertex of a path. Removing an endpoint preserves `nodup`. -/
def dropTail (p : SimplePath α) : SimplePath α :=
  ⟨p.val.dropTail, by
    exact VertexSeq.nodup_dropTail (vertices p) (nodup p)⟩

/-! ## append -/

/-- Concatenate two vertex-disjoint paths, keeping both joining vertices.
The disjointness hypothesis is what preserves `nodup`; it also rules out a
stall at the junction. -/
def append (p q : SimplePath α)
    (hdisj : ∀ v : α, v ∈ vertices p → v ∈ vertices q → False) : SimplePath α :=
  ⟨p.val.append q.val (by
      intro h
      exact hdisj (tail p) (VertexSeq.tail_mem (vertices p)) (by
        simp [tail, vertices, h])), by
    exact VertexSeq.nodup_append (vertices p) (vertices q) (nodup p) (nodup q) hdisj⟩

/-- Concatenate two paths meeting at a shared vertex, dropping the duplicated
joining vertex. The remaining vertices of `p` must be disjoint from `q`. -/
def glue (p q : SimplePath α) (h : tail p = head q)
    (hdisj : ∀ v : α, v ∈ (vertices p).dropTail → v ∈ vertices q → False) :
    SimplePath α :=
  ⟨p.val.glue q.val h, by
    unfold SimpleWalk.glue
    by_cases hp : (vertices p).length = 0
    · simpa [vertices, hp] using nodup q
    · simpa [vertices, hp] using
        VertexSeq.nodup_append (vertices p).dropTail (vertices q)
          (VertexSeq.nodup_dropTail (vertices p) (nodup p)) (nodup q) hdisj⟩

/-! ## reverse -/

/-- Reverse a path. Reversal preserves `nodup`. -/
def reverse (p : SimplePath α) : SimplePath α :=
  ⟨p.val.reverse, by
    exact VertexSeq.nodup_reverse (vertices p) (nodup p)⟩

/-! ## prefixUntil, suffixFrom -/

/-- The prefix of a path ending at the first occurrence of `v`. A contiguous
prefix of a path is a path. -/
def prefixUntil [DecidableEq α] (p : SimplePath α) (v : α) (h : v ∈ vertices p) :
    SimplePath α :=
  ⟨p.val.prefixUntil v h, by
    exact VertexSeq.nodup_prefixUntil (vertices p) v h (nodup p)⟩

/-- The suffix of a path starting at the first occurrence of `v`. A contiguous
suffix of a path is a path. -/
def suffixFrom [DecidableEq α] (p : SimplePath α) (v : α) (h : v ∈ vertices p) :
    SimplePath α :=
  ⟨p.val.suffixFrom v h, by
    exact VertexSeq.nodup_suffixFrom (vertices p) v h (nodup p)⟩

/-! ## map -/

/-- Map a path through an injective function. Injectivity preserves distinct
vertices. -/
def map {β : Type*} (f : α → β) (hf : Function.Injective f) (p : SimplePath α) :
    SimplePath β :=
  ⟨p.val.map f hf, by
    exact VertexSeq.nodup_map f hf (vertices p) (nodup p)⟩

/-! ## takeWhile, dropWhile -/

/-- Take a contiguous prefix of a path, including the first failure if any. -/
def takeWhile (p : SimplePath α) (q : α → Prop) [DecidablePred q] :
    SimplePath α :=
  ⟨p.val.takeWhile q, by
    exact VertexSeq.nodup_takeWhile (vertices p) q (nodup p)⟩

/-- Drop the longest prefix of a path on which `q` holds. The result is a
contiguous suffix, hence a path. -/
def dropWhile (p : SimplePath α) (q : α → Prop) [DecidablePred q]
    (h : ∃ v ∈ (vertices p).toList, ¬ q v) : SimplePath α :=
  ⟨p.val.dropWhile q h, by
    exact VertexSeq.nodup_dropWhile (vertices p) q h (nodup p)⟩

/-! ## splitAt -/

/-- Split a path at every occurrence of `v`. Every produced piece is a
contiguous subpath. -/
def splitAt [DecidableEq α] (p : SimplePath α) (v : α) : List (SimplePath α) :=
  ((vertices p).splitAt v).pmap
    (fun w (hw : w.nonstalling ∧ w.nodup) => ⟨⟨w, hw.1⟩, hw.2⟩)
    (by
      intro w hw
      exact ⟨VertexSeq.nonstalling_splitAt (vertices p) p.val.nonstalling v w hw,
        VertexSeq.nodup_splitAt (vertices p) (nodup p) v w hw⟩)

/-! ## zip -/

/-- Zip two paths into a path of pairs. Pairwise distinct first components are
enough to make the pairs pairwise distinct. -/
def zip {β : Type*} (p : SimplePath α) (q : SimplePath β) :
    SimplePath (α × β) :=
  ⟨p.val.zip q.val, by
    exact VertexSeq.nodup_zip (vertices p) (vertices q) (nodup p)⟩

/-! ## loopErase, cycleErase -/

/-- Remove immediate stalls from a path. Since a path has no repeated vertices,
this preserves `nodup`. -/
def loopErase [DecidableEq α] (p : SimplePath α) : SimplePath α :=
  ⟨p.val.loopErase, by
    exact VertexSeq.nodup_loopErase (vertices p) (nodup p)⟩

/-- Cycle erasure of any simple walk produces a simple path. -/
def cycleErase [DecidableEq α] (w : SimpleWalk α) : SimplePath α :=
  ⟨w.cycleErase, by
    exact w.val.cycleErase_nodup⟩

/-! ## edges -/

/-- The number of traversed edges equals the path's length. -/
@[simp] lemma length_edges (p : SimplePath α) : (edges p).length = length p :=
  VertexSeq.length_edges (vertices p)

/-- A path traverses each edge at most once (a path is a trail). -/
lemma edges_nodup (p : SimplePath α) : (edges p).Nodup :=
  VertexSeq.nodup_edges_of_nodup (vertices p) (nodup p)

/-- Reversal reverses the edge list. -/
@[simp] lemma edges_reverse (p : SimplePath α) :
    edges (reverse p) = (edges p).reverse :=
  VertexSeq.edges_reverse (vertices p)

/-- Dropping the last vertex cannot introduce new edges. -/
lemma edges_dropTail_subset (p : SimplePath α) : edges (dropTail p) ⊆ edges p :=
  VertexSeq.edges_dropTail_subset (vertices p)

/-- Dropping the first vertex cannot introduce new edges. -/
lemma edges_dropHead_subset (p : SimplePath α) : edges (dropHead p) ⊆ edges p :=
  VertexSeq.edges_dropHead_subset (vertices p)

/-- Taking a prefix cannot introduce new edges. -/
lemma edges_prefixUntil_subset [DecidableEq α] (p : SimplePath α) (v : α)
    (h : v ∈ vertices p) : edges (prefixUntil p v h) ⊆ edges p :=
  VertexSeq.edges_prefixUntil_subset (vertices p) v h

/-- Taking a suffix cannot introduce new edges. -/
lemma edges_suffixFrom_subset [DecidableEq α] (p : SimplePath α) (v : α)
    (h : v ∈ vertices p) : edges (suffixFrom p v h) ⊆ edges p :=
  VertexSeq.edges_suffixFrom_subset (vertices p) v h

/-! ## arcs -/

/-- The number of traversed arcs equals the path's length. -/
@[simp] lemma length_arcs (p : SimplePath α) : (arcs p).length = length p :=
  VertexSeq.length_arcs (vertices p)

/-- A path traverses each directed arc at most once. -/
lemma arcs_nodup (p : SimplePath α) : (arcs p).Nodup :=
  VertexSeq.nodup_arcs_of_nodup (vertices p) (nodup p)

/-- Reversal reverses the arc list and swaps every arc's endpoints. -/
@[simp] lemma arcs_reverse (p : SimplePath α) :
    arcs (reverse p) = (arcs p).reverse.map (fun a : α × α => (a.2, a.1)) :=
  VertexSeq.arcs_reverse (vertices p)

/-- Dropping the last vertex cannot introduce new arcs. -/
lemma arcs_dropTail_subset (p : SimplePath α) : arcs (dropTail p) ⊆ arcs p :=
  VertexSeq.arcs_dropTail_subset (vertices p)

/-- Dropping the first vertex cannot introduce new arcs. -/
lemma arcs_dropHead_subset (p : SimplePath α) : arcs (dropHead p) ⊆ arcs p :=
  VertexSeq.arcs_dropHead_subset (vertices p)

/-- Taking a prefix cannot introduce new arcs. -/
lemma arcs_prefixUntil_subset [DecidableEq α] (p : SimplePath α) (v : α)
    (h : v ∈ vertices p) : arcs (prefixUntil p v h) ⊆ arcs p :=
  VertexSeq.arcs_prefixUntil_subset (vertices p) v h

/-- Taking a suffix cannot introduce new arcs. -/
lemma arcs_suffixFrom_subset [DecidableEq α] (p : SimplePath α) (v : α)
    (h : v ∈ vertices p) : arcs (suffixFrom p v h) ⊆ arcs p :=
  VertexSeq.arcs_suffixFrom_subset (vertices p) v h

end SimplePath
