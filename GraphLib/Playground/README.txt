The Playground folder
=====================

This folder collects small, self-contained attempts at formalizing "easy"/"small" results.
Its purpose is NOT to build polished library components, but to stress-test the bespoke graph
definitions of GraphLib/Graph/Basic.lean on classical results and to record, in situ, where
those definitions are convenient and where they create friction.

Current files
-------------

  GraphInterval.lean — interval graphs are perfect (chromatic number = clique number on every
                       induced subgraph), for a finite family of arbitrary real intervals. Proved
                       via the interval order and Dilworth's theorem.
  Dilworth.lean      — statements of Dilworth's and Mirsky's theorems on a finite order (chain
                       covers vs antichains). Proofs are deferred (sorry); imported by
                       GraphInterval.lean as black boxes.
