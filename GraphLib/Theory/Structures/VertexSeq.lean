/-
Copyright (c) 2026 Basil Rohner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Sorrachai Yingchareonthawornchai, Weixuan Yuan
-/
import GraphLib.Theory.Structures.VertexSeq.Basic
import GraphLib.Theory.Structures.VertexSeq.Predicates
import GraphLib.Theory.Structures.VertexSeq.Append
import GraphLib.Theory.Structures.VertexSeq.MapZip
import GraphLib.Theory.Structures.VertexSeq.Subseq
import GraphLib.Theory.Structures.VertexSeq.Erase
import GraphLib.Theory.Structures.VertexSeq.Edges
import GraphLib.Theory.Structures.VertexSeq.Index

/-!
# Vertex sequences

A `VertexSeq α` is a non-empty inductive sequence of vertices, with a
`singleton` base case and a right-extending `cons`. It is the underlying
carrier for walks, paths and cycles in the graph theory library.

This file defines nothing itself: it is an *umbrella* module that merely
re-exports (imports) the `VertexSeq` development, which is split across
`GraphLib/Theory/Structures/VertexSeq/`:

* `Basic` — the carrier, `length`/`head`/`tail`/`toList`, membership/subset,
  and `dropHead`/`dropTail`.
* `Predicates` — `nodup`, `nonstalling`, `closed`.
* `Append` — `append`, `reverse` and their laws.
* `MapZip` — `map`, `foldl`, `foldr`, `zip`, `any`, `all` and the `Functor`
  instance.
* `Subseq` — `prefixUntil`, `suffixFrom`, `takeWhile`, `dropWhile`, `splitAt`.
* `Erase` — `loopErase`, `cycleErase`.
* `Edges` — `edges`, `arcs` (the traversed edges/arcs, as lists).
* `Index` — `GetElem` and `insert`.

Downstream files should keep importing this umbrella; the split is internal.

## Module dependency graph

Direct imports between the submodules (an arrow `A → B` means "`A` imports
`B`"). The acyclic spine is `Basic ← Predicates ← Append ← Subseq ← Erase ←
Edges`, with `MapZip` branching off `Predicates` and `Index` off `Basic`:
```text
                       Basic
                      ╱     ╲
                Predicates   Index
                 ╱      ╲
            Append      MapZip
              │
            Subseq
              │
            Erase
              │
            Edges
```
This umbrella imports all eight submodules.
-/
