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

## Main results

* `invAck_agree_Nivasch` (currently `sorry`): `invAck` and
  `Nivasch.invAckNivasch` agree up to an additive constant.

## Status

Work in progress. Nivasch's writeup only claims agreement up to "a small
additive constant" without pinning the value; making the constant explicit
(and proving it) is the goal of this file.

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

/-- `invAck` and `Nivasch.invAckNivasch` agree up to an additive constant. -/
theorem invAck_agree_Nivasch :
    ∃ C : ℕ, ∀ n : ℕ,
      ((invAck n : ℤ) - (Nivasch.invAckNivasch n : ℤ)).natAbs ≤ C := by
  sorry

end InverseAckermann
