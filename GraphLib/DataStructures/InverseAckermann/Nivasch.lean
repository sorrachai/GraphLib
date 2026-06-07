/-
Copyright (c) 2026 GraphLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne
-/

import GraphLib.DataStructures.InverseAckermann.Basic

/-!
# Nivasch's hierarchy: the inverse Ackermann function without `ack`

An alternative definition of the inverse Ackermann function due to Nivasch
that avoids any reference to `ack`. Set
`invAckHier 0 n = ⌈n / 2⌉`, and
`invAckHier (k+1) n = min { i | (invAckHier k)^[i] n ≤ 3 }`;
then `invAckNivasch n = min { k | invAckHier k n ≤ 3 }`.

## Main definitions

* `Nivasch.invAckHier`: the slow-growing hierarchy `αₖ`.
* `Nivasch.invAckNivasch`: Nivasch's `α`, defined via the hierarchy.

## Main results (all `sorry`)

* `invAckNivasch_le_invAck`: `invAckNivasch n ≤ invAck n` (unconditional).
* `invAck_le_invAckNivasch_add_two`: `invAck n ≤ invAckNivasch n + 2`
  (depends on `findBdd` fuel being sufficient at every level).
* `invAck_agree_Nivasch`: the two-sided bound.

The constant `2` is tight: at `n = 4`, `invAck 4 = 2` and
`invAckNivasch 4 = 0`. The `+2` arises from two structural offsets:
  - level `0` here is halving, not `log` (Nivasch's `α₁`): one off-by-one;
  - `bound_k(3)` (the threshold of the `α_k`-hierarchy) lies between
    `ack k k` and `ack (k+2) (k+2)`: one more off-by-one.

## Status

Work in progress.

## AI usage

The definitions in this file were drafted by AI from Nivasch's writeup and
reviewed by the author. The agreement theorem with `invAck` is stated but
not yet proved.

## References

* G. Nivasch, *Inverse Ackermann without Ackermann*,
  <https://www.gabrielnivasch.org/fun/inverse-ackermann>.
-/

namespace InverseAckermann
namespace Nivasch

/-- Bounded least-search: the smallest `k' ∈ [k, k + fuel)` with `p k'`, or `0`
if none. Used to express the inner searches in `invAckHier` and
`invAckNivasch`.

Implemented via `List.find?` on `List.range'`; the `0` fallback matches the
expected case-analysis behaviour at call sites (see the TODO on `invAckHier`
about justifying the chosen `fuel = n + 2`). -/
private def findBdd (p : ℕ → Bool) (k fuel : ℕ) : ℕ :=
  ((List.range' k fuel).find? p).getD 0

/-- Nivasch's slow-growing hierarchy `αₖ`:
`invAckHier 0 n = ⌈n / 2⌉`, and
`invAckHier (k+1) n = min { i | (invAckHier k)^[i] n ≤ 3 }`.

TODO: prove that `n + 2` always suffices for the inner search. Without this
lemma, `invAckHier` and `invAckNivasch` silently return `0` when the search
fails. The bound should follow from `αₖ`'s growth rate; see Nivasch's writeup. -/
def invAckHier : ℕ → ℕ → ℕ
  | 0,     n => (n + 1) / 2
  | k + 1, n => findBdd (fun i => decide ((invAckHier k)^[i] n ≤ 3)) 0 (n + 2)

/-- Nivasch's inverse Ackermann:
`invAckNivasch n = min { k | invAckHier k n ≤ 3 }`. See the TODO on
`invAckHier` about the `n + 2` search bound. -/
def invAckNivasch (n : ℕ) : ℕ :=
  findBdd (fun k => decide (invAckHier k n ≤ 3)) 0 (n + 2)

end Nivasch

/-- Lower bound: `invAckNivasch n ≤ invAck n` for every `n`. Holds even when
the bounded search inside `invAckHier`/`invAckNivasch` returns the `0`
fallback, since `0 ≤ invAck n` is trivial. -/
theorem invAckNivasch_le_invAck (n : ℕ) :
    Nivasch.invAckNivasch n ≤ invAck n := by
  sorry

/-- Upper bound: `invAck n ≤ invAckNivasch n + 2`. The constant `2` is tight,
witnessed at `n = 4` where `invAck 4 = 2` and `invAckNivasch 4 = 0`.

This direction depends on the bounded search inside `invAckHier` and
`invAckNivasch` actually finding the minimum (rather than hitting the `0`
fallback); see the TODO on `invAckHier`. -/
theorem invAck_le_invAckNivasch_add_two (n : ℕ) :
    invAck n ≤ Nivasch.invAckNivasch n + 2 := by
  sorry

/-- `invAck` and `Nivasch.invAckNivasch` agree pointwise up to the explicit
constant `2`. The constant is tight (witnessed at `n = 4`). -/
theorem invAck_agree_Nivasch (n : ℕ) :
    Nivasch.invAckNivasch n ≤ invAck n ∧
      invAck n ≤ Nivasch.invAckNivasch n + 2 :=
  ⟨invAckNivasch_le_invAck n, invAck_le_invAckNivasch_add_two n⟩

end InverseAckermann
