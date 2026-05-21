/-
Copyright (c) 2026 CSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne
-/

import Mathlib.Computability.Ackermann
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic


--- Maybe it should technically go to the computability folder of CSlib.
/-!
# Inverse Ackermann Function

This file defines the **inverse Ackermann function** `α(n)` and establishes its key properties.
The inverse Ackermann function arises naturally in the amortised complexity analysis of
Union-Find (disjoint-set forests with union-by-rank and path compression), where a sequence
of `m` operations on `n` elements runs in `O(m · α(n))` time.

## Mathematical background

Recall Mathlib's standard (two-argument) Ackermann function `ack : ℕ → ℕ → ℕ`:

```
  ack 0 n       = n + 1
  ack (m+1) 0   = ack m 1
  ack (m+1)(n+1) = ack m (ack (m+1) n)
```

The *diagonal* `ack k k` grows extraordinarily fast:

| k | ack k k      |
|---|-------------|
| 0 | 1           |
| 1 | 3           |
| 2 | 7           |
| 3 | 61          |
| 4 | 2^2^2^… − 3 (a tower of 65536 twos minus 3) |

The **inverse Ackermann function** `α(n)` is defined as
```
  α(n) = min { k : ack k k ≥ n }
```
It grows *incredibly* slowly: `α(n) ≤ 4` for all `n ≤ 2^(2^(2^65536))`, which vastly exceeds
the number of atoms in the observable universe.

## Main definitions

* `InverseAckermann.ackDiag`: The diagonal Ackermann function `n ↦ ack n n`.
* `InverseAckermann.alpha`: The inverse Ackermann function `α(n) = Nat.find (∃ k, n ≤ ack k k)`.

## Main results (stated, proofs TODO)

* `alpha_le_iff`: `α(n) ≤ k ↔ n ≤ ack k k`.
* `alpha_mono`: `α` is monotone.
* `alpha_zero`: `α 0 = 0`.
* `alpha_one`: `α 1 = 0`.
* `alpha_le_four`: `α n ≤ 4` for `n ≤ ack 4 4` (i.e., all practical inputs).
* `alpha_lt_id`: For `n ≥ 5`, `α n < n`.
* `ackDiag_alpha`: `n ≤ ack (α n) (α n)` (the defining property).

## Design notes

- We build on Mathlib's `ack` rather than defining a separate hierarchy. This avoids
  duplication and gives us access to all existing Ackermann lemmas (monotonicity, growth
  bounds, strict monotonicity in both arguments, etc.).
- An alternative definition sometimes used in the literature is
  `α(m, n) = min { i ≥ 1 : ack(i, ⌊m/n⌋) ≥ log₂ n }`, which is a two-argument version.
  For the Union-Find bound, the single-argument diagonal inverse suffices.
- This file is designed to be independently useful and PR-able to Mathlib's
  `Mathlib.Computability.Ackermann`.

## References

* R. E. Tarjan, "Efficiency of a good but not linear set union algorithm", *JACM* 22(2), 1975.
* R. E. Tarjan, J. van Leeuwen, "Worst-case analysis of set union algorithms", *JACM* 31(2), 1984.
* R. Seidel, M. Sharir, "Top-down analysis of path compression", *SIAM J. Comput.* 34(3), 2005.

## TODO

- Prove remaining sorry'd lemmas below (currently all proven!).
- Add `Decidable` instance for `α` (it is computable).
- Prove `α` grows slower than any primitive recursive function of the form `n ↦ f(n)`.
- Connect to the two-argument inverse `α(m, n)` used in some references.
-/

namespace InverseAckermann

open Nat

/-! ### Diagonal Ackermann function -/

/-- The diagonal Ackermann function `ackDiag n = ack n n`. -/
def ackDiag (n : ℕ) : ℕ := ack n n

@[simp] theorem ackDiag_zero : ackDiag 0 = 1 := by simp [ackDiag]
@[simp] theorem ackDiag_one : ackDiag 1 = 3 := by simp [ackDiag]
@[simp] theorem ackDiag_two : ackDiag 2 = 7 := by simp [ackDiag]
@[simp] theorem ackDiag_three : ackDiag 3 = 61 := by simp [ackDiag]

/-- `ackDiag` is strictly monotone. -/
theorem ackDiag_strictMono : StrictMono ackDiag := by
  intro a b hab
  exact calc ack a a < ack a b := ack_strictMono_right a hab
    _ ≤ ack b b := ack_mono_left b (le_of_lt hab)

/-- `ackDiag` is monotone. -/
theorem ackDiag_mono : Monotone ackDiag := ackDiag_strictMono.monotone

/-- `ackDiag n > 0` for all `n`. -/
theorem ackDiag_pos (n : ℕ) : 0 < ackDiag n := ack_pos n n

/-- `ackDiag n ≥ n` for all `n`. -/
theorem le_ackDiag (n : ℕ) : n ≤ ackDiag n := le_of_lt (lt_ack_right n n)

/-- `ackDiag` is unbounded: for every `N`, there exists `k` with `ackDiag k ≥ N`. -/
theorem ackDiag_unbounded (N : ℕ) : ∃ k, N ≤ ackDiag k :=
  ⟨N, le_ackDiag N⟩

/-! ### Inverse Ackermann function -/

/-- Auxiliary: the predicate `n ≤ ack k k` is decidable. -/
instance (n k : ℕ) : Decidable (n ≤ ack k k) := inferInstance

/-- The **inverse Ackermann function**.
  `alpha n = min { k : ℕ | n ≤ ack k k }`.

  This is the standard single-argument inverse used in the Union-Find amortised bound.
  It grows incredibly slowly: `alpha n ≤ 4` for all practically occurring `n`. -/
noncomputable def alpha (n : ℕ) : ℕ :=
  Nat.find (ackDiag_unbounded n)

-- Some computational checks (via native_decide or norm_num in proofs)
-- α(0) = 0,  α(1) = 0,  α(2) = 1,  α(3) = 1,
-- α(4) = 2,  α(5) = 2, ..., α(7) = 2,
-- α(8) = 3, ..., α(61) = 3,
-- α(62) = 4, ...

/-! ### Core characterisation -/

/-- The defining property: `n ≤ ack (alpha n) (alpha n)`. -/
theorem ackDiag_alpha (n : ℕ) : n ≤ ackDiag (alpha n) :=
  Nat.find_spec (ackDiag_unbounded n)

/-- `alpha n ≤ k` if and only if `n ≤ ack k k`. -/
theorem alpha_le_iff {n k : ℕ} : alpha n ≤ k ↔ n ≤ ackDiag k := by
  constructor
  · intro h
    exact le_trans (ackDiag_alpha n) (ackDiag_mono h)
  · intro h
    exact Nat.find_le h

/-- `k < alpha n` if and only if `ack k k < n`. -/
theorem lt_alpha_iff {n k : ℕ} : k < alpha n ↔ ackDiag k < n := by
  rw [← not_le, ← not_le]
  exact not_congr alpha_le_iff

/-! ### Basic values -/

/-- `α(0) = 0`. -/
@[simp] theorem alpha_zero : alpha 0 = 0 := by
  apply le_antisymm
  · exact alpha_le_iff.mpr (by simp [ackDiag])
  · exact Nat.zero_le _

/-- `α(1) = 0`. -/
@[simp] theorem alpha_one : alpha 1 = 0 := by
  apply le_antisymm
  · exact alpha_le_iff.mpr (by simp [ackDiag])
  · exact Nat.zero_le _

/-- `α(2) = 1`. -/
theorem alpha_two : alpha 2 = 1 := by
  apply le_antisymm
  · exact alpha_le_iff.mpr (by simp [ackDiag])
  · exact lt_alpha_iff.mpr (by simp [ackDiag])

/-- `α(3) = 1`. -/
theorem alpha_three : alpha 3 = 1 := by
  apply le_antisymm
  · exact alpha_le_iff.mpr (by simp [ackDiag])
  · exact lt_alpha_iff.mpr (by simp [ackDiag])

/-! ### Monotonicity -/

/-- `α` is monotone: if `a ≤ b` then `α(a) ≤ α(b)`. -/
theorem alpha_mono : Monotone alpha := by
  intro a b hab
  exact alpha_le_iff.mpr (le_trans hab (ackDiag_alpha b))

/-! ### Growth bounds -/

/-- For all `n`, `α(n) ≤ n`. In fact `α` grows much slower, but this is a simple upper bound. -/
theorem alpha_le_self (n : ℕ) : alpha n ≤ n :=
  alpha_le_iff.mpr (le_ackDiag n)

/-- The key "practically constant" bound: `α(n) ≤ 4` whenever `n ≤ ack 4 4`.
Since `ack 4 4` is a number with about `10^(10^(10^19728))` digits, this covers
every input that could ever arise in practice. -/
theorem alpha_le_four_of_le_ack44 (n : ℕ) (h : n ≤ ack 4 4) : alpha n ≤ 4 :=
  alpha_le_iff.mpr (by rwa [ackDiag])

/-! ### Interaction with `ack` -/

/-- `alpha (ack k k) ≤ k` for all `k`. -/
theorem alpha_ackDiag_le (k : ℕ) : alpha (ackDiag k) ≤ k :=
  alpha_le_iff.mpr (le_refl _)

/-- `alpha (ack k k + 1) = k + 1`.
  (Going one above the diagonal value bumps the inverse.) -/
theorem alpha_ackDiag_succ (k : ℕ) : alpha (ackDiag k + 1) = k + 1 := by
  -- By definition of `alpha`, we know that `alpha (ackDiag k + 1) = k + 1`.
  apply le_antisymm;
  · apply alpha_le_iff.mpr;
    exact Nat.succ_le_of_lt (ackDiag_strictMono (Nat.lt_succ_self k));
  · exact Nat.succ_le_of_lt (lt_of_not_ge fun h => by linarith [alpha_le_iff.mp h,
    ackDiag_strictMono.monotone, h])

/-
`alpha` composed with `ackDiag` is the identity.
-/
theorem alpha_ackDiag (k : ℕ) : alpha (ackDiag k) = k := by
  exact le_antisymm (alpha_ackDiag_le _)
    (Nat.le_of_not_lt fun h => by have := lt_alpha_iff.2
  (show ackDiag (alpha (ackDiag k)) < ackDiag k from StrictMono.lt_iff_lt (ackDiag_strictMono) |>.2 h)
   aesop)


/-! ### Iterated / levelled inverse (for the full Tarjan analysis)

For the full Tarjan–van Leeuwen amortised analysis of Union-Find, one needs a
finer decomposition using iterated applications of `ack`. The *level* of a node `x`
with parent `p` and `rank r` is
  `level(x) = max { k : ack k (rank x) ≤ rank (root x) }`
and the *index* is
  `index(x) = max { i : ack^[i]_{level(x)} (rank x) ≤ rank (root x) }`.

We define the iterated version here for use in the potential function.

**Blueprint:** See `CSlib.DataStructures.UnionFind.Blueprint` for how these
are used in the potential function.
-/

/-- The *level function* `ufLevel r R` for Union-Find complexity analysis.
  Given a node rank `r` and the rank of its root `R` (with `r < R`), the level is
  `max { k ≥ 0 : ack k r ≤ R }`.

  This is well-defined because `ack k r` is strictly increasing in `k` and eventually
  exceeds any bound. -/
noncomputable def ufLevel (r R : ℕ) : ℕ :=
  Nat.find (⟨R, lt_ack_left R r⟩ : ∃ k, R < ack k r) - 1

/-
The *index function* `ufIndex r R k` for Union-Find complexity analysis.
  Given rank `r`, root rank `R`, and level `k`, the index is
  `max { i ≥ 1 : (ack k)^[i](r) ≤ R }`.
-/
noncomputable def ufIndex (r R k : ℕ) : ℕ :=
  Nat.find (⟨R + 1, by
    -- By induction on $i$, we show that $(ack k)^[i] r \geq r + i$.
    have h_ind : ∀ i : ℕ, (ack k)^[i] r ≥ r + i := by
      intro i;
      induction' i with i ih;
      · rfl;
      · rw [ Function.iterate_succ_apply' ];
        exact Nat.succ_le_of_lt ( lt_of_le_of_lt ih ( lt_ack_right _ _ ) );
    linarith [ h_ind ( R + 1 ) ] -- need: (ack k)^[R+1] r > R, which follows from ack k being inflationary
  ⟩ : ∃ i, R < (ack k)^[i] r) - 1

/-!
## Roadmap for this file

### Immediate TODO (needed for Union-Find correctness + complexity)
1. ✅ Define `alpha`, `ackDiag`
2. ✅ Prove `alpha_le_iff`, `ackDiag_alpha` (core characterisation)
3. ✅ Prove `alpha_mono`, `alpha_zero`, `alpha_one`
4. ✅ Prove `alpha_ackDiag` and `alpha_ackDiag_succ`
5. 🔲 Prove `alpha_lt_id` for `n ≥ 5`
6. 🔲 Make `alpha` computable (provide a `DecidableEq`-based algorithm)

### Medium-term TODO (for Mathlib PR)
7. 🔲 Prove `alpha` grows slower than `log* n`
8. 🔲 Connect `ufLevel` and `ufIndex` to the iterated Ackermann hierarchy
9. 🔲 Prove `ufLevel` and `ufIndex` are well-defined and bounded
10. 🔲 Add simp lemmas for small values of `alpha`

### Long-term TODO
11. 🔲 Two-argument inverse `α(m, n)` for the most refined bounds
12. 🔲 Connection to the Davenport–Schinzel sequence bounds
    (relate to `KlazarAckermann.alpha` in `Ackermann_Function.lean`)
-/

end InverseAckermann
