Adds Dilworth's theorem and its dual, Mirsky's theorem, for finite subsets of a partial order.

Each is a weak-duality inequality plus a strong-duality existence of a matching pair (as for Hall's marriage theorem), so no `Finset.min'` / `Finset.max'` over families of sets is introduced:

- `dilworth` / `mirsky` — an antichain and a chain cover (resp. a chain and an antichain cover) of
  equal size;
- `antichain_le_chain_cover` / `chain_le_antichain_cover` — the weak-duality inequalities, for an
  arbitrary relation;
- `dilworth_partition` / `mirsky_partition` — the same with a pairwise-disjoint partition.

Dilworth uses Galvin's induction (gluing step: `chainCover_glue`); the König / bipartite-matching route is avoided as it isn't in Mathlib yet.

Choices I'd like input on:

1. **Mirsky is proved directly (peeling minimal elements), not as an `OrderDual` of Dilworth.** The
   two are dual in statement but not in difficulty: the direct induction is shorter, and both proofs
   already share the closure lemmas and the injective weak dualities.
2. **`[DecidableEq α]` on the main theorems** is forced by `s = 𝒞.biUnion id`; stating coverage membership-wise would remove it. The weak-duality lemmas themselves assume neither order nor
   `DecidableEq`.
3. **Covers are `Finset (Finset α)`, but the lemmas use injective/bijective `α → Finset α`,** so
   chain distinctness follows from the antichain property rather than bookkeeping. The injective core
   `exists_injOn_mem_of_inter_subsingleton` is index-polymorphic, so the Set-level and `Finset` forms
   are specializations of it.

Open questions: file placement (`Mathlib/Order/Dilworth.lean`?); whether the general lemmas belong in
existing files (`Mathlib/Order/Antichain.lean`, `Mathlib/Order/UpperLower/…`); naming of the `𝒞` / `𝒜`
covers.

Zulip: <link>
