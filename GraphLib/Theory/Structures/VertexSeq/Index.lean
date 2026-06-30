/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Basic

/-!
# Vertex sequences: indexing and insertion

Positional access into a vertex sequence via the underlying list, and insertion
of a vertex at a given index.

## Main definitions

* `GetElem (VertexSeq α) ℕ α` — index into the visited vertices.
* `VertexSeq.insert` — insert a vertex at a position.
-/

variable {α : Type*}

namespace VertexSeq

/-! ## Indexing and insertion -/

instance : GetElem (VertexSeq α) ℕ α (fun w i ↦ i < w.toList.length) where
  getElem w i h := w.toList[i]

/-- Insert the vertex `v` at index `i`, shifting later vertices one position
to the right. If `i` exceeds `w.toList.length`, `v` is appended at the end. -/
@[grind] def insert : VertexSeq α → ℕ → α → VertexSeq α
  | .singleton x, 0, v => .cons (.singleton v) x
  | .singleton x, _ + 1, v => .cons (.singleton x) v
  | .cons q x, i, v =>
    if i ≤ q.length then .cons (insert q i v) x
    else if i = q.length + 1 then .cons (q :+ v) x
    else .cons (q :+ x) v

end VertexSeq
