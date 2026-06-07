/-
Copyright (c) 2026 CSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [your name here]
-/

import Batteries.Data.UnionFind
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import GraphLib.DataStructures.InverseAckermann.Basic

/-!
# `GraphLib.Algorithms.UnionFind`

Placeholder. Disjoint-set forests with union-by-rank and path compression.
-/

/-
The inverse Ackermann function arises naturally in the amortised complexity
analysis of Union-Find (disjoint-set forests with union-by-rank and path compression),
where a sequence of `m` operations on `n` elements runs in `O(m · α(n))` time.
-/
/-!
# Union-Find: Blueprint and Roadmap

This file is a **comprehensive blueprint** for the formal verification of the Union-Find
(disjoint-set) data structure in Lean 4. It covers:

1. **What Union-Find is** (mathematical description)
2. **How it works** (operations, heuristics)
3. **Correctness** (the equivalence relation is maintained)
4. **Amortised complexity** (the `O(m · α(n))` bound via Tarjan's potential function)

All theorem statements are provided with `sorry`; the goal is to fill them in incrementally.

## Table of contents

- §1  Overview: what is Union-Find?
- §2  The Batteries implementation (what we inherit)
- §3  Correctness properties (spec-level)
- §4  The rank invariant
- §5  Tarjan's potential function
- §6  Amortised cost of `find`
- §7  Amortised cost of `union`
- §8  The main theorem: `O(m · α(n))` amortised bound
- §9  Roadmap and dependency graph

---

## §1  Overview: What is Union-Find?

Union-Find (also called Disjoint-Set Union, DSU) maintains a partition of `{0, 1, …, n−1}`
into disjoint equivalence classes, supporting two operations:

- **`find(x)`**: return the canonical representative ("root") of the class containing `x`.
- **`union(x, y)`**: merge the classes containing `x` and `y`.

### Representation: rooted forests

Each equivalence class is stored as a rooted tree. Every element points to a *parent*;
roots point to themselves. `find(x)` follows parent pointers until it reaches a root.

### Heuristic 1: Union by rank

Each root carries a *rank* (an upper bound on the height of its tree).
When merging two trees, we attach the tree with the **smaller rank** under the root
of the tree with the **larger rank**. If ranks are equal, we pick one as the new root
and increment its rank. This keeps trees shallow.

**Key invariant:** The rank of a node never changes after it becomes a non-root.

### Heuristic 2: Path compression

During `find(x)`, after we locate the root `r`, we update every node on the path from
`x` to `r` so that it points directly to `r`. This flattens the tree for future queries.

**Key invariant:** Path compression does not change ranks. It only changes parent pointers.

### Combined complexity

With both heuristics, a sequence of `m` `find`/`union` operations on `n` elements takes
total time `O(m · α(n))`, where `α` is the inverse Ackermann function. This is *almost*
but not quite `O(m)` — the `α(n)` factor is ≤ 4 for all practical `n`.

This file formalises all three aspects: the data structure, correctness, and amortised
complexity.

---

## §2  The Batteries implementation

Lean's Batteries library (`Batteries.Data.UnionFind.Basic`) already provides:

- `Batteries.UnionFind`: the core data type (an `Array UFNode` with validity invariants)
- `UnionFind.find`: find with path compression
- `UnionFind.union`: union by rank
- `UnionFind.rootD`: the root function (without modifying the structure)
- `UnionFind.Equiv`: the equivalence relation `Equiv s a b ↔ rootD s a = rootD s b`

Key lemmas already proven in Batteries:
- `find_root_1`: `(s.find x).1.rootD i = s.rootD i`
  (find with path compression does not change the root mapping)
- `find_size`: `(s.find x).1.size = s.size`
  (find preserves the size)
- `rootD_rootD`: `s.rootD (s.rootD x) = s.rootD x`
  (rootD is idempotent)
- `rootD_parent`: `s.rootD (s.parent x) = s.rootD x`
  (following a parent doesn't change the root)

What Batteries does **not** provide (and what we aim to formalise here):
- `Equiv` is an equivalence relation
- `union` correctly merges equivalence classes
- `union` does not disturb other equivalence classes
- The amortised complexity bound

---
-/

open Batteries Batteries.UnionFind InverseAckermann

/-!
## §3  Correctness properties

We show that `UnionFind.Equiv` is an equivalence relation and that the operations
maintain it correctly.
-/

namespace UnionFind.Correctness

/-!
### 3.1  `Equiv` is an equivalence relation

Since `Equiv s a b ↔ s.rootD a = s.rootD b`, this is straightforward:
reflexivity, symmetry, and transitivity follow from `=` being an equivalence. -/

/-
`Equiv` is reflexive.
-/
theorem equiv_refl (s : UnionFind) (a : ℕ) : s.Equiv a a := by
  exact rfl

/-
`Equiv` is symmetric.
-/
theorem equiv_symm (s : UnionFind) {a b : ℕ} (h : s.Equiv a b) : s.Equiv b a := by
  exact h.symm

/-
`Equiv` is transitive.
-/
theorem equiv_trans (s : UnionFind) {a b c : ℕ}
    (hab : s.Equiv a b) (hbc : s.Equiv b c) : s.Equiv a c := by
  exact hab.trans hbc

/-- `Equiv` as a `Setoid` on `ℕ`. -/
noncomputable def equivSetoid (s : UnionFind) : Setoid ℕ where
  r := s.Equiv
  iseqv := ⟨equiv_refl s, fun h => equiv_symm s h, fun h1 h2 => equiv_trans s h1 h2⟩

/-!
### 3.2  `find` preserves `Equiv`

This is essentially `find_root_1` from Batteries: path compression does not change
which root any node maps to, so the equivalence relation is unchanged. -/

/-
`find` does not change the equivalence relation.
-/
theorem find_equiv (s : UnionFind) (x : Fin s.size) (a b : ℕ) :
    (s.find x).1.Equiv a b ↔ s.Equiv a b := by
  grind +suggestions

/-!
### 3.3  `union` merges exactly two classes

After `union x y`:
- Everything equivalent to `x` becomes equivalent to `y` (and vice versa).
- Everything not equivalent to either `x` or `y` is unchanged.
- `x` and `y` become equivalent.
-/

/-
After `union x y`, `x` and `y` are equivalent.
-/
theorem union_equiv (s : UnionFind) (x y : Fin s.size) :
    (s.union x y).Equiv x y := by
  grind +suggestions

/-
After `union x y`, if `a` was equivalent to `x` and `b` was equivalent to `y`,
    then `a` and `b` are now equivalent.
-/
theorem union_equiv_of_equiv (s : UnionFind) (x y : Fin s.size)
    {a b : ℕ} (ha : s.Equiv a x) (hb : s.Equiv b y) :
    (s.union x y).Equiv a b := by
  grind +suggestions

/-
`union` does not break existing equivalences: if `a` and `b` were already
    equivalent, they remain so after `union x y`.
-/
theorem union_equiv_of_equiv_pre (s : UnionFind) (x y : Fin s.size)
    {a b : ℕ} (h : s.Equiv a b) :
    (s.union x y).Equiv a b := by
  grind +suggestions

/-
`union` does not create spurious equivalences: if `a` and `b` are equivalent
    after `union x y`, then either they were already equivalent, or one is in the
    class of `x` and the other in the class of `y` (or vice versa).
-/
theorem union_equiv_iff (s : UnionFind) (x y : Fin s.size) (a b : ℕ)
    (_ha : a < s.size) (_hb : b < s.size) :
    (s.union x y).Equiv a b ↔
      s.Equiv a b ∨ (s.Equiv a x ∧ s.Equiv b y) ∨ (s.Equiv a y ∧ s.Equiv b x) := by
  convert union_equiv_of_equiv s x y using 1;
  rotate_left;
  · exact b;
  · exact a;
  · rw [ show ( s.union x y ).Equiv a b ↔ ( s.union x y ).Equiv b a from ?_ ];
    · grind +suggestions;
    · exact ⟨ fun h => equiv_symm _ h, fun h => equiv_symm _ h ⟩

/-!
### 3.4  `push` adds an isolated element

`push` adds a new node `n` (where `n = s.size`) that is its own root and not
equivalent to any existing node. -/

/-
The new node is its own root.
-/
theorem push_rootD_self (s : UnionFind) : s.push.rootD s.size = s.size := by
  unfold Batteries.UnionFind.rootD;
  split_ifs <;> simp_all +decide [ Batteries.UnionFind.root ]

/-
The new node is not equivalent to any old node (unless that old node was out of bounds).
-/
theorem push_not_equiv (s : UnionFind) (a : ℕ) (ha : a < s.size) :
    ¬ s.push.Equiv a s.size := by
  intro h; have := h; simp_all +decide [ Batteries.UnionFind.Equiv ] ;
  convert push_rootD_self s;
  constructor <;> intro <;> simp_all +decide [ Batteries.UnionFind.rootD ];
  grind

/-
`push` does not change equivalences among old nodes.
-/
theorem push_equiv_iff (s : UnionFind) (a b : ℕ) (_ha : a < s.size) (_hb : b < s.size) :
    s.push.Equiv a b ↔ s.Equiv a b := by
  grind +suggestions

end UnionFind.Correctness

/-!
## §4  The rank invariant

The rank system satisfies several important structural properties that are crucial
for both correctness and the complexity analysis.
-/

namespace UnionFind.RankInvariant

/-!
### 4.1  Structural properties of rank

These properties are partially covered by Batteries' invariants (`rankD_lt`), but we
state additional ones needed for the complexity analysis.
-/

/-
Rank of a root is strictly greater than rank of any of its non-root children.
  (This is Batteries' `rank_lt` rephrased.)
-/
theorem rank_lt_rank_parent (s : UnionFind) (x : ℕ) (hx : s.parent x ≠ x) :
    s.rank x < s.rank (s.parent x) := by
  -- Apply the rank_lt property to get the inequality.
  apply Batteries.UnionFind.rank_lt hx

/-
Rank of a node is bounded by the rank of its root.
-/
theorem rank_le_rank_root (s : UnionFind) (x : ℕ) :
    s.rank x ≤ s.rank (s.rootD x) := by
  -- By definition of `rootD`, we know that `rootD x` is the root of `x`.
  apply UnionFind.le_rank_root

/-- The number of nodes of rank `r` is at most `n / 2^r`, where `n = s.size`.
  This is the key combinatorial bound on the rank distribution.

  **Proof sketch:** Each rank-`r` node is the root of a subtree of size ≥ `2^r`
  (provable by induction on the union operations). Distinct rank-`r` roots have
  disjoint subtrees, so there are at most `n / 2^r` of them.

  **Important caveat:** This property does NOT hold for arbitrary `UnionFind` structures
  satisfying the Batteries invariants (`parentD_lt`, `rankD_lt`). It only holds for
  structures that were built from `empty` using `push` and `union` operations.
  A counterexample: a single-element structure with rank 1 (which satisfies the
  Batteries invariants since the node is a root, but violates `1 ≤ 1/2 = 0`).

  For a proper formalisation, one would need to either:
  (a) Track the construction history (e.g., as a predicate `WellFormed s`), or
  (b) Strengthen the `UnionFind` invariant to include this bound.

  For now, we state this as an axiom-like sorry for the complexity analysis.
  The complexity proof only applies to well-formed structures anyway. -/
theorem count_rank_le (s : UnionFind) (r : ℕ) :
    (Finset.univ.filter fun i : Fin s.size => s.rank i = r).card ≤ s.size / 2 ^ r := by
  sorry

/-
Maximum rank is at most `⌊log₂ n⌋`.
  Follows from `count_rank_le`: if `r > log₂ n` then `n / 2^r = 0`, so no node has
  that rank.
-/
theorem rank_lt_log (s : UnionFind) (x : ℕ) (hx : x < s.size) :
    s.rank x ≤ Nat.log 2 s.size := by
  refine Nat.le_log_of_pow_le (by decide) ?_
  have h_card : 1 ≤ (Finset.univ.filter fun i : Fin s.size => s.rank i = s.rank x).card :=
    Finset.card_pos.mpr ⟨⟨x, hx⟩, by aesop⟩
  have h_le := UnionFind.RankInvariant.count_rank_le s (s.rank x)
  have h_one : 1 ≤ s.size / 2 ^ s.rank x := h_card.trans h_le
  calc 2 ^ s.rank x
      = 1 * 2 ^ s.rank x := (one_mul _).symm
    _ ≤ (s.size / 2 ^ s.rank x) * 2 ^ s.rank x := Nat.mul_le_mul_right _ h_one
    _ ≤ s.size := Nat.div_mul_le_self _ _

/-!
### 4.2  Rank is unchanged by `find`

Path compression does not modify ranks. This is essential for the amortised analysis. -/

/-
`find` preserves the rank of every node.
-/
theorem find_rank (s : UnionFind) (x : Fin s.size) (i : ℕ) :
    (s.find x).1.rank i = s.rank i := by
  convert Batteries.UnionFind.rankD_findAux ( x := x ) using 1

end UnionFind.RankInvariant

/-!
## §5  Tarjan's potential function

This is the heart of the amortised analysis. We define a potential function `Φ(s)` on
Union-Find states such that:
- `Φ(s) ≥ 0` always
- The *amortised cost* of each operation = actual cost + ΔΦ = O(α(n))

### The potential function

For a Union-Find state `s` with `n` elements, define for each non-root node `x`:

```
  level(x) = max { k ≥ 0 : ack k (rank x) ≤ rank (root x) }
  index(x) = max { i ≥ 1 : ack^[i]_{level(x)} (rank x) ≤ rank (root x) }
```

where `ack^[i]_k` means `i` iterations of `fun n ↦ ack k n`.

Then the per-node potential is:
```
  φ(x) = if x is a root then α(n) · rank(x)
          else (α(n) - level(x)) · rank(x) - index(x)
```

And the total potential is:
```
  Φ(s) = Σ_{x ∈ [n]} φ(x)
```

### Why this works

The key insight is that path compression can only *increase* level and index values
(because after compression, a node's parent has higher rank), which *decreases* the
potential. The potential decrease compensates for the actual cost of walking up the
tree during `find`.

### References for the potential function

The potential function above follows Tarjan (1975) as refined by Tarjan & van Leeuwen (1984).
A simplified presentation appears in Cormen, Leiserson, Rivest, Stein (CLRS), Chapter 21.

An alternative (and arguably cleaner) analysis is given by Seidel & Sharir (2005), who use
a top-down approach with a simpler potential function. Both yield the same `O(m · α(n))` bound.

Full citations:

* R. E. Tarjan, *Efficiency of a good but not linear set union algorithm*,
  JACM 22(2), 1975, pp. 215–225.
* R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*,
  JACM 31(2), 1984, pp. 245–281.
* R. Seidel and M. Sharir, *Top-down analysis of path compression*,
  SIAM J. Comput. 34(3), 2005, pp. 515–525.
-/

namespace UnionFind.Potential

/-! ### Iterated / levelled inverse (Tarjan helpers)

For the full Tarjan–van Leeuwen amortised analysis of Union-Find, one needs a
finer decomposition using iterated applications of `ack`. The *level* of a node
`x` with rank `r` whose root has rank `R` is

  `level(x) = max { k : ack k r ≤ R }`

and the *index* is

  `index(x) = max { i : ack^[i]_{level(x)} r ≤ R }`.

The two abstract definitions below operate purely on natural-number ranks and
serve as low-level helpers for `nodeLevel` and `nodeIndex` further down. -/

/-- The *level function* `ufLevel r R` for Union-Find complexity analysis.
  Given a node rank `r` and the rank of its root `R` (with `r < R`), the level is
  `max { k ≥ 0 : ack k r ≤ R }`.

  This is well-defined because `ack k r` is strictly increasing in `k` and eventually
  exceeds any bound. -/
noncomputable def ufLevel (r R : ℕ) : ℕ :=
  Nat.find (⟨R, lt_ack_left R r⟩ : ∃ k, R < ack k r) - 1

/-- The *index function* `ufIndex r R k` for Union-Find complexity analysis.
  Given rank `r`, root rank `R`, and level `k`, the index is
  `max { i ≥ 1 : (ack k)^[i](r) ≤ R }`. -/
noncomputable def ufIndex (r R k : ℕ) : ℕ :=
  Nat.find (⟨R + 1, by
    have h_ind : ∀ i : ℕ, r + i ≤ (ack k)^[i] r := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (lt_ack_right _ _))
    have := h_ind (R + 1)
    omega
  ⟩ : ∃ i, R < (ack k)^[i] r) - 1

/-!
### 5.1  Level and index of a node

We define `nodeLevel` and `nodeIndex` for non-root nodes in a Union-Find structure.

**Important:** These are only meaningful for non-root nodes `x` with `rank x ≥ 1`.
For root nodes, the potential is defined differently (see §5.2).
-/

/-- The *level* of a non-root node `x` in a Union-Find structure:
  `nodeLevel s x = max { k : ack k (rank x) ≤ rank (rootD s x) }`.

  This measures "how many levels of the Ackermann hierarchy" fit between the
  rank of `x` and the rank of its root. -/
noncomputable def nodeLevel (s : UnionFind) (x : ℕ) : ℕ :=
  -- We want max { k : ack k (s.rank x) ≤ s.rank (s.rootD x) }
  -- Equivalently, (Nat.find { k : s.rank (s.rootD x) < ack k (s.rank x) }) - 1
  -- This is well-defined because ack k r → ∞ as k → ∞.
  if s.rank x = 0 then 0
  else
    have : ∃ k, s.rank (s.rootD x) < ack k (s.rank x) :=
      ⟨s.rank (s.rootD x), lt_ack_left _ _⟩
    Nat.find this - 1

/-- The *index* of a non-root node `x`:
  `nodeIndex s x = max { i ≥ 1 : (ack (level x))^[i] (rank x) ≤ rank (root x) }`.

  This measures "how many iterations of `ack` at the node's level" fit between
  the rank of `x` and the rank of its root. -/
noncomputable def nodeIndex (s : UnionFind) (x : ℕ) : ℕ :=
  let k := nodeLevel s x
  let r := s.rank x
  let R := s.rank (s.rootD x)
  if r = 0 then 0
  else
    have : ∃ i, R < (ack k)^[i] r :=
      ⟨R, lt_ack_right k R |>.trans_le (by
        sorry -- need ack k R ≤ (ack k)^[R] r for large enough R
      )⟩
    sorry -- Nat.find this - 1

/-!
### 5.2  The potential function -/

/-- Per-node potential.
  - For a root node: `φ(x) = α(n) · rank(x)`
  - For a non-root node: `φ(x) = (α(n) - level(x)) · rank(x) - index(x)` -/
noncomputable def nodePotential (s : UnionFind) (n : ℕ) (x : ℕ) : ℤ :=
  let α_n := invAck n
  if s.parent x = x then
    -- Root node
    ↑α_n * ↑(s.rank x)
  else
    -- Non-root node
    (↑α_n - ↑(nodeLevel s x)) * ↑(s.rank x) - ↑(nodeIndex s x)

/-- The total potential of a Union-Find state.
  `Φ(s) = Σ_{x < n} φ(x)` -/
noncomputable def potential (s : UnionFind) : ℤ :=
  (Finset.range s.size).sum (nodePotential s s.size)

/-- The potential is always nonneg (this requires showing level ≤ α(n) and index ≤ rank). -/
theorem potential_nonneg (s : UnionFind) : 0 ≤ potential s := by
  sorry

/-!
### 5.3  Bounds on level and index -/

/-- Level of a non-root node is at most `α(n)`. -/
theorem nodeLevel_le_alpha (s : UnionFind) (x : ℕ) (hx : s.parent x ≠ x)
    (hx_lt : x < s.size) :
    nodeLevel s x ≤ invAck s.size := by
  sorry

/-- Index of a non-root node is at most `rank(x)`. -/
theorem nodeIndex_le_rank (s : UnionFind) (x : ℕ) (hx : s.parent x ≠ x) :
    nodeIndex s x ≤ s.rank x := by
  sorry

/-- If rank is 0, then level is 0 and index is 0. -/
theorem level_index_of_rank_zero (s : UnionFind) (x : ℕ) (hr : s.rank x = 0) :
    nodeLevel s x = 0 ∧ nodeIndex s x = 0 := by
  sorry

end UnionFind.Potential

/-!
## §6  Amortised cost of `find`

The actual cost of `find(x)` is proportional to the length of the path from `x` to its root.
We show that the amortised cost (actual cost + ΔΦ) is `O(α(n))`.

### Proof sketch for `find`

Let `x₀ → x₁ → ⋯ → xₜ = root` be the find path. The actual cost is `t` (number of edges).

After path compression, every `xᵢ` points directly to `root`. For each `xᵢ`:
- If `level(xᵢ)` increases (or `index(xᵢ)` increases), the potential drops.
- At most `α(n)` nodes can have their level stay the same and their index not increase
  (one per level from 0 to α(n)-1, plus the child of the root).

Therefore: the potential drops by at least `t - α(n) - 2`, giving amortised cost
`t + (t - α(n) - 2) ≤ O(α(n))`. Wait, that's not right. Let me be more precise:

The amortised cost is `actual_cost + Φ(after) - Φ(before)`. We need `Φ(after) - Φ(before)`
to be negative enough to cancel most of the actual cost.

In detail:
- Nodes whose level or index strictly increase contribute a potential drop ≥ 1 each.
- There are at most `α(n) + 2` "expensive" nodes (those at the top of each level block,
  plus the root's child).
- So the potential drop is ≥ `t - α(n) - 2`.
- Amortised cost ≤ `t - (t - α(n) - 2) = α(n) + 2 = O(α(n))`.
-/

namespace UnionFind.AmortisedFind

/-- The actual cost (number of parent-pointer traversals) of `find x` in state `s`.
  This equals the depth of `x` in the forest. -/
noncomputable def findCost (s : UnionFind) (x : ℕ) : ℕ :=
  if h : x < s.size then
    -- Number of edges from x to root
    -- We define it as the number of iterations needed to reach the root
    if hpar : s.parent x = x then 0
    else 1 + findCost s (s.parent x)
  else 0
termination_by s.rankMax - s.rank x
decreasing_by
  exact Nat.sub_lt_sub_left (s.lt_rankMax x) (s.rank_lt hpar)

/-- **Main amortised bound for `find`:**
  The amortised cost of `find(x)` is at most `α(n) + 2`.

  Formally: `findCost(s, x) + Φ(s.find x) - Φ(s) ≤ α(n) + 2`.

  This is the key lemma in the Tarjan analysis. -/
theorem find_amortised_cost (s : UnionFind) (x : Fin s.size) :
    (findCost s x : ℤ) + Potential.potential (s.find x).1 - Potential.potential s
      ≤ ↑(invAck s.size) + 2 := by
  sorry

end UnionFind.AmortisedFind

/-!
## §7  Amortised cost of `union`

The `union(x, y)` operation:
1. Calls `find(x)` to get root `rx`.
2. Calls `find(y)` to get root `ry`.
3. Calls `link(rx, ry)` which attaches one root under the other (by rank).

Steps 1 and 2 have amortised cost `O(α(n))` each (from §6).
Step 3 has actual cost `O(1)` and we need to bound its effect on the potential.
-/

namespace UnionFind.AmortisedUnion

/-- **Amortised cost of `link`:**
  The potential change from `link` is at most `α(n)`.

  When we link root `rx` under root `ry` (with `rank ry ≥ rank rx`):
  - `rx` becomes a non-root. Its potential changes from `α(n) · rank(rx)` to at most
    `(α(n) - 0) · rank(rx) - 0 = α(n) · rank(rx)`, so no increase.
  - `ry` remains a root. If `rank(rx) = rank(ry)`, the rank of `ry` increases by 1,
    adding `α(n)` to the potential.
  - No other node's potential changes.

  Total potential change ≤ `α(n)`. -/
theorem link_potential_change (s : UnionFind) (rx ry : Fin s.size)
    (hry : s.parent ry = ry) :
    Potential.potential (s.link rx ry hry) - Potential.potential s
      ≤ ↑(invAck s.size) := by
  sorry

/-- **Main amortised bound for `union`:**
  The amortised cost of `union(x, y)` is at most `3 · α(n) + 4`.

  This combines:
  - `find(x)`: amortised cost ≤ `α(n) + 2`
  - `find(y)`: amortised cost ≤ `α(n) + 2`
  - `link`:    potential change ≤ `α(n)` -/
theorem union_amortised_cost (s : UnionFind) (x y : Fin s.size) :
    Potential.potential (s.union x y) - Potential.potential s
      ≤ 3 * ↑(invAck s.size) + 4 := by
  sorry

end UnionFind.AmortisedUnion

/-!
## §8  The main theorem

Putting it all together: a sequence of `m` operations (finds and unions) on a
Union-Find structure with `n` elements has total cost `O(m · α(n))`.
-/

namespace UnionFind.MainTheorem

/-!
### 8.1  Modelling a sequence of operations

We model a sequence of operations as a list of `Op` commands. -/

/-- An operation on a Union-Find structure. -/
inductive Op (n : ℕ) where
  | find (x : Fin n)
  | union (x y : Fin n)

/-
Execute a single operation, returning the new state.
  We track that the size stays at `n` for simplicity.
-/
noncomputable def execOp (s : UnionFind) (op : Op s.size) :
    { s' : UnionFind // s'.size = s.size } := by
  match op with
  | .find x =>
    exact ⟨(s.find x).1, s.find_size x⟩
  | .union x y =>
    exact ⟨s.union x y, by
      unfold UnionFind.union;
      unfold UnionFind.link;
      -- The size of the array after linking is the same as the original size because the link operation only modifies the parent and rank fields of the elements, but does not change the number of elements.
      simp [linkAux];
      grind⟩

/- `execOps` — Execute a sequence of operations.
   Each operation's indices must be valid for the *current* state.
   We keep the size fixed (no `push` in this model).

   Note: This is tricky to define because the type of the ops list depends on
   the evolving state. A cleaner approach would use a state monad or indexed family.
   For the blueprint we omit this definition and focus on the per-operation bounds. -/

/-- **The main amortised complexity theorem.**

  Starting from an initial Union-Find on `n` elements (each in its own class),
  any sequence of `m` find and union operations has total actual cost `O(m · α(n))`.

  More precisely, the total cost is at most `m · (3 · α(n) + 4)`.

  Note: this is the "accounting method" version. The total actual cost ≤ total amortised
  cost + Φ(initial) - Φ(final) ≤ total amortised cost + Φ(initial). Since the initial
  potential is 0 (all nodes are roots with rank 0), we get that the total actual cost
  is bounded by the sum of amortised costs.
-/
-- TODO: The main theorem needs a proper cost model. The statement below is a placeholder.
-- A full formalisation would track the total number of parent-pointer traversals
-- across all operations and show it is bounded by `m * (3 * α(n) + 4)`.
-- For now we state it as `True` to keep the file compiling.
theorem total_cost_le_placeholder : True := trivial

end UnionFind.MainTheorem

/-!
## §9  Roadmap and dependency graph

### File organisation (proposed for CSlib)

```
CSlib/
├── Computability/
│   └── InverseAckermann.lean          ← THIS FILE'S DEPENDENCY
│       • ackDiag, alpha (inverse Ackermann)
│       • alpha_le_iff, alpha_mono, alpha_le_four
│       • level, index (iterated inverse)
│
├── DataStructures/
│   └── UnionFind/
│       ├── Blueprint.lean              ← THIS FILE
│       │   • Full roadmap and sorry'd statements
│       │
│       ├── Correctness.lean            (TODO: extract from Blueprint)
│       │   • equiv_refl, equiv_symm, equiv_trans
│       │   • find_equiv, union_equiv, union_equiv_iff
│       │   • push_rootD_self, push_not_equiv, push_equiv_iff
│       │
│       ├── RankBounds.lean             (TODO: extract from Blueprint)
│       │   • rank_lt_log, count_rank_le
│       │   • find_rank (rank preservation under find)
│       │
│       ├── Potential.lean              (TODO: extract from Blueprint)
│       │   • nodeLevel, nodeIndex
│       │   • nodePotential, potential
│       │   • potential_nonneg
│       │   • nodeLevel_le_alpha, nodeIndex_le_rank
│       │
│       └── Complexity.lean             (TODO: extract from Blueprint)
│           • find_amortised_cost
│           • link_potential_change
│           • union_amortised_cost
│           • total_cost_le (THE MAIN THEOREM)
```

### Dependency graph

```
  Mathlib.Computability.Ackermann
         │
         ▼
  InverseAckermann.lean
    (alpha, ackDiag)
         │
         ├──────────────────────────────────────┐
         ▼                                      ▼
  Batteries.Data.UnionFind.Basic         RankBounds.lean
    (UnionFind, find, union,               (count_rank_le,
     rootD, Equiv, find_root_1)             rank_lt_log)
         │                                      │
         ▼                                      ▼
  Correctness.lean                       Potential.lean
    (equiv is equivalence,                 (nodeLevel, nodeIndex,
     find/union preserve it)                nodePotential, potential)
                                                │
                                                ▼
                                         Complexity.lean
                                           (find_amortised_cost,
                                            union_amortised_cost,
                                            total_cost_le)
```

### Suggested proving order

1. **InverseAckermann.lean** — Start here, it's self-contained and PR-able.
   - `alpha_le_iff`, `alpha_mono` are easy (✅ already done).
   - `alpha_ackDiag`, `alpha_ackDiag_succ` need `ack` injectivity (available in Mathlib).

2. **Correctness.lean** — Next easiest.
   - `equiv_refl/symm/trans` are trivial (just `Eq` properties).
   - `find_equiv` follows from `find_root_1`.
   - `union_equiv` and `union_equiv_iff` require understanding `link`'s effect on `rootD`.
     This is the hardest part and may need additional lemmas about `linkAux`.

3. **RankBounds.lean** — Moderately hard.
   - `find_rank` follows from `rankD_findAux` in Batteries.
   - `rank_lt_log` and `count_rank_le` require a size argument based on subtree sizes,
     which is not directly tracked in Batteries' representation. May need to define
     "subtree size" and prove it's ≥ 2^rank by induction on the sequence of operations.

4. **Potential.lean** — Hard.
   - Defining `nodeLevel` and `nodeIndex` cleanly requires care with well-foundedness.
   - Proving `nodeLevel_le_alpha` and `nodeIndex_le_rank` requires connecting the
     Ackermann hierarchy to the rank bounds.

5. **Complexity.lean** — The hardest part.
   - `find_amortised_cost` is the core argument. Needs careful path analysis.
   - `link_potential_change` is a local calculation.
   - `total_cost_le` combines everything via telescoping sums.

### Alternative approach: Seidel–Sharir (2005)

An alternative to Tarjan's bottom-up potential analysis is the top-down analysis of
Seidel and Sharir. Their approach:
- Defines a simpler potential based on "coins" placed on edges.
- Analyses path compression by charging coins from the compressed edges.
- Avoids the level/index machinery entirely.
- Still yields the `O(m · α(n))` bound.

This might be easier to formalise. The key reference is:
  R. Seidel, M. Sharir, "Top-down analysis of path compression",
  SIAM J. Comput. 34(3), 2005, pp. 515–525.

### What to PR to Mathlib/Batteries

1. **Mathlib PR: Inverse Ackermann function**
   - `InverseAckermann.alpha`, `alpha_le_iff`, `alpha_mono`
   - Goes into `Mathlib.Computability.Ackermann` (extending the existing file)
   - Prerequisites: None beyond what's already in Mathlib

2. **Batteries PR: UnionFind correctness**
   - `Equiv` is an equivalence relation
   - `find_equiv`, `union_equiv_iff`
   - Goes into `Batteries.Data.UnionFind.Basic` or a new `.Lemmas` file
   - Prerequisites: None beyond what's already in Batteries

3. **CSlib: Complexity analysis**
   - The amortised analysis is novel formalisation work
   - Keep in CSlib until mature, then consider upstreaming
-/

/-!
## Appendix: Relationship to the Klazar Ackermann hierarchy

The file `Ackermann_Function.lean` defines a *different* Ackermann hierarchy
(`KlazarAckermann.F`) used for Davenport–Schinzel sequence bounds:

```
  F 1 n = 2n
  F (k+1) n = (F k ·)^[n] 1
```

This is related to but distinct from the standard Ackermann function. The connection is:
- `F 2 n = 2^n ≈ ack 3 (n-3) + 3` (exponential level)
- `F 3` ≈ tower function ≈ `ack 4`
- In general, `F k` grows like `ack (k+1)` (off by a shift in the hierarchy index)

The inverse `KlazarAckermann.alpha k n` corresponds roughly to `α_k(n)` but with
different base cases. For Union-Find, we use the standard `ack`-based inverse
because it directly matches the Tarjan analysis.

The Klazar hierarchy could potentially be connected to the standard one via
a theorem like:
```
  ∀ k ≥ 1, ∀ n ≥ 1, F (k+1) n ≤ ack (k+1) (c * n) for some constant c
```
but this is not needed for Union-Find and is left as a future project.
-/
