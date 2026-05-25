/-
Copyright (c) 2026 GraphLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne
-/

import Mathlib.Computability.Ackermann
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD

/-!
# Inverse Ackermann function

Given Mathlib's Ackermann function `ack : ℕ → ℕ → ℕ`, the diagonal `ack k k` is
strictly increasing in `k`, so we may define the inverse Ackermann function

  `invAck n = min { k | n ≤ ack k k }`.

Values: `invAck 0 = invAck 1 = 0`, `invAck 2 = invAck 3 = 1`, and `invAck n ≤ 4`
whenever `n ≤ ack 4 4`.

## Main definitions

* `ackDiag n = ack n n`.
* `invAck n` is the inverse Ackermann function.
* `ackBdd B k m = min (ack k m) B` is a truncated `ack`, computed via a table
  of fixed-width rows, which makes it primitive recursive.

## Main results

* `invAck_le_iff : invAck n ≤ k ↔ n ≤ ack k k`.
* `invAck_mono`, `invAck_ackDiag : invAck (ack k k) = k`.
* `invAck_primrec`: `invAck` is primitive recursive (whereas `fun k ↦ ack k k`
  is not, by `not_nat_primrec_ack_self`).

## AI usage

AI assistance was used to draft boilerplate API, docstrings, and several of
the proofs in the primitive-recursiveness section, following Mathlib and
CSlib naming and style conventions. All statements and proofs were reviewed
and verified.

-/

namespace InverseAckermann

open Nat


/-! ### Diagonal Ackermann function -/

section AckDiag

/-- The diagonal Ackermann function `ackDiag n = ack n n`. -/
def ackDiag (n : ℕ) : ℕ := ack n n

@[simp] theorem ackDiag_zero : ackDiag 0 = 1 := by simp [ackDiag]
@[simp] theorem ackDiag_one : ackDiag 1 = 3 := by simp [ackDiag]
@[simp] theorem ackDiag_two : ackDiag 2 = 7 := by simp [ackDiag]
@[simp] theorem ackDiag_three : ackDiag 3 = 61 := by simp [ackDiag]

/-- `ackDiag` is strictly monotone. -/
theorem ackDiag_strictMono : StrictMono ackDiag := fun _ _ hab =>
  (ack_strictMono_right _ hab).trans_le (ack_mono_left _ hab.le)

/-- `ackDiag` is monotone. -/
theorem ackDiag_mono : Monotone ackDiag := ackDiag_strictMono.monotone

/-- `ackDiag n` is positive. -/
theorem ackDiag_pos (n : ℕ) : 0 < ackDiag n := ack_pos n n

/-- `n ≤ ackDiag n`. -/
theorem le_ackDiag (n : ℕ) : n ≤ ackDiag n := (lt_ack_right n n).le

/-- For every `N`, some `k` satisfies `N ≤ ackDiag k`. -/
theorem ackDiag_unbounded (N : ℕ) : ∃ k, N ≤ ackDiag k := ⟨N, le_ackDiag N⟩

end AckDiag


/-! ### Inverse Ackermann function -/

section InvAck

/-! #### Definition -/

/-- The inverse Ackermann function `invAck n = min { k | n ≤ ack k k }`. -/
def invAck (n : ℕ) : ℕ := Nat.find (ackDiag_unbounded n)

/-- Defining property: `n ≤ ackDiag (invAck n)`. -/
theorem ackDiag_invAck (n : ℕ) : n ≤ ackDiag (invAck n) :=
  Nat.find_spec (ackDiag_unbounded n)


/-! #### Characterisation -/

/-- `invAck n ≤ k ↔ n ≤ ackDiag k`. -/
theorem invAck_le_iff {n k : ℕ} : invAck n ≤ k ↔ n ≤ ackDiag k :=
  ⟨fun h => (ackDiag_invAck n).trans (ackDiag_mono h), fun h => Nat.find_le h⟩

/-- `k < invAck n ↔ ackDiag k < n`. -/
theorem lt_invAck_iff {n k : ℕ} : k < invAck n ↔ ackDiag k < n := by
  rw [← not_le, invAck_le_iff, not_le]

/-- `invAck n < k + 1 ↔ n ≤ ackDiag k`. -/
theorem invAck_lt_add_one_iff {n k : ℕ} : invAck n < k + 1 ↔ n ≤ ackDiag k := by
  rw [Nat.lt_succ_iff, invAck_le_iff]

/-- `k + 1 ≤ invAck n ↔ ackDiag k < n`. -/
theorem add_one_le_invAck_iff {n k : ℕ} : k + 1 ≤ invAck n ↔ ackDiag k < n := by
  rw [Nat.succ_le_iff, lt_invAck_iff]

/-- `invAck (ackDiag k) ≤ k`. -/
theorem invAck_ackDiag_le (k : ℕ) : invAck (ackDiag k) ≤ k := invAck_le_iff.mpr le_rfl

/-- `invAck` is a left inverse of `ackDiag`. -/
@[simp]
theorem invAck_ackDiag (k : ℕ) : invAck (ackDiag k) = k :=
  le_antisymm (invAck_ackDiag_le k) (ackDiag_strictMono.le_iff_le.mp (ackDiag_invAck _))

/-- One past the diagonal: `invAck (ackDiag k + 1) = k + 1`. -/
theorem invAck_ackDiag_add_one (k : ℕ) : invAck (ackDiag k + 1) = k + 1 :=
  le_antisymm
    (invAck_le_iff.mpr (ackDiag_strictMono k.lt_succ_self))
    (lt_invAck_iff.mpr (Nat.lt_succ_self _))


/-! #### Basic values -/

@[simp] theorem invAck_zero : invAck 0 = 0 :=
  Nat.le_zero.mp (invAck_le_iff.mpr (Nat.zero_le _))

@[simp] theorem invAck_one : invAck 1 = 0 :=
  Nat.le_zero.mp (invAck_le_iff.mpr (by simp))

@[simp] theorem invAck_two : invAck 2 = 1 :=
  le_antisymm (invAck_le_iff.mpr (by simp)) (lt_invAck_iff.mpr (by simp))

@[simp] theorem invAck_three : invAck 3 = 1 :=
  le_antisymm (invAck_le_iff.mpr (by simp)) (lt_invAck_iff.mpr (by simp))


/-! #### Monotonicity and bounds -/

/-- `invAck` is monotone. -/
theorem invAck_mono : Monotone invAck := fun _ _ hab =>
  invAck_le_iff.mpr (hab.trans (ackDiag_invAck _))

/-- `invAck n ≤ n`. -/
theorem invAck_le_self (n : ℕ) : invAck n ≤ n := invAck_le_iff.mpr (le_ackDiag n)

end InvAck


/-! ### `invAck` is primitive recursive

Define a truncated `ackBdd B k m = min (ack k m) B`, computed as a table whose
rows have fixed length `B + 1`; this is primitive recursive. Then the graph

  `invAck n = b ↔ n ≤ ack b b ∧ (b = 0 ∨ ack (b - 1) (b - 1) < n)`

becomes primitive recursive (using `ackBdd` for the comparisons), and the bound
`invAck n ≤ n` lets us apply `Primrec.of_graph`. -/

section InvAckPrimrec

/-! #### Bounded Ackermann -/

/-- Entry `m` of row `k + 1`, computed from the previous row `prev`. Uses
`ackBdd B (k+1) m = ackBdd B k (ackBdd B (k+1) (m-1))` and
`ackBdd B (k+1) 0 = ackBdd B k 1`. -/
def ackBddEntry (B : ℕ) (prev : List ℕ) : ℕ → ℕ
  | 0     => prev.getD 1 B
  | m + 1 => prev.getD (ackBddEntry B prev m) B

/-- Row `k` of the `ackBdd` table: a list of length `B + 1` with
`(ackBddRow B k)[i] = ackBdd B k i`. -/
def ackBddRow (B : ℕ) : ℕ → List ℕ
  | 0     => (List.range (B + 1)).map fun m => min (m + 1) B
  | k + 1 => (List.range (B + 1)).map (ackBddEntry B (ackBddRow B k))

/-- The bounded Ackermann function `ackBdd B k m = min (ack k m) B`, set up to
be primitive recursive (`ack` itself is not). -/
def ackBdd (B k m : ℕ) : ℕ := (ackBddRow B k).getD m B

/-- Every row of the `ackBdd` table has length `B + 1`. -/
@[simp]
lemma ackBddRow_length (B k : ℕ) : (ackBddRow B k).length = B + 1 := by
  cases k <;> simp [ackBddRow]

/-- Truncating the argument before applying `ack k` does not change the
truncated value. -/
private lemma ack_min_arg (k B x : ℕ) :
    min (ack k (min x B)) B = min (ack k x) B := by
  rcases le_or_gt x B with h | h
  · rw [min_eq_left h]
  · have hB : B < ack k B := lt_ack_right k B
    rw [min_eq_right h.le, min_eq_right hB.le,
      min_eq_right (hB.trans_le (ack_mono_right k h.le)).le]

/-- Out-of-range entries of `ackBdd` saturate at `B`. -/
private lemma ackBdd_of_ge {B k m : ℕ} (h : B + 1 ≤ m) :
    ackBdd B k m = min (ack k m) B := by
  have hB : B < ack k m := (Nat.lt_of_succ_le h).trans (lt_ack_right k m)
  rw [ackBdd, List.getD_eq_default _ _ (by simp [h]), min_eq_right hB.le]

/-- Closed form: `ackBdd B k m = min (ack k m) B`. -/
theorem ackBdd_eq (B k m : ℕ) : ackBdd B k m = min (ack k m) B := by
  induction k generalizing m with
  | zero =>
    rcases lt_or_ge m (B + 1) with hm | hm
    · unfold ackBdd ackBddRow
      rw [ack_zero, List.getD_eq_getElem _ _ (by simp [hm])]
      simp [List.getElem_map, List.getElem_range]
    · exact ackBdd_of_ge hm
  | succ k ih =>
    rcases lt_or_ge m (B + 1) with hm | hm
    · unfold ackBdd ackBddRow
      rw [List.getD_eq_getElem _ _ (by simp [hm])]
      simp only [List.getElem_map, List.getElem_range]
      clear hm
      induction m with
      | zero =>
        change ackBdd B k 1 = min (ack (k + 1) 0) B
        rw [ack_succ_zero]; exact ih 1
      | succ m ih_m =>
        change ackBdd B k (ackBddEntry B (ackBddRow B k) m) = min (ack (k + 1) (m + 1)) B
        rw [ih, ih_m, ack_succ_succ, ack_min_arg]
    · exact ackBdd_of_ge hm

/-- `ackBdd B k m ≤ B`. -/
lemma ackBdd_le (B k m : ℕ) : ackBdd B k m ≤ B := by
  rw [ackBdd_eq]; exact min_le_right _ _

/-- `n ≤ ack k k` rephrased via `ackBdd`. -/
private lemma le_ack_iff_ackBdd_eq (n k : ℕ) : n ≤ ack k k ↔ ackBdd n k k = n := by
  rw [ackBdd_eq, min_eq_right_iff]

/-- `ack k k < n` rephrased via `ackBdd`. -/
private lemma ack_lt_iff_ackBdd_lt (n k : ℕ) : ack k k < n ↔ ackBdd n k k < n := by
  rw [ackBdd_eq, min_lt_iff, or_iff_left (lt_irrefl n)]


/-! #### Primitive recursiveness of `ackBdd` -/

/-- `ackBddEntry` is primitive recursive. -/
lemma ackBddEntry_primrec :
    Primrec fun p : (ℕ × List ℕ) × ℕ => ackBddEntry p.1.1 p.1.2 p.2 := by
  -- Rephrase `ackBddEntry` as an `ℕ.rec`-shaped term on the third argument so we
  -- can hand it to `Primrec.nat_rec'`: base case `prev.getD 1 B`, step case
  -- `prev.getD ih B`. The pattern-match definition itself is not directly in
  -- the shape `Primrec.nat_rec'` expects.
  have h_rec : ∀ p : (ℕ × List ℕ) × ℕ, ackBddEntry p.1.1 p.1.2 p.2 =
      p.2.rec (p.1.2.getD 1 p.1.1) fun _ ih => p.1.2.getD ih p.1.1 := by
    rintro ⟨⟨B, prev⟩, m⟩
    induction m with
    | zero      => rfl
    | succ m ih => simp [ackBddEntry, ih]
  refine (Primrec.nat_rec' (f := fun p : (ℕ × List ℕ) × ℕ => p.2)
      (g := fun p => p.1.2.getD 1 p.1.1)
      (h := fun p q => p.1.2.getD q.2 p.1.1)
      Primrec.snd ?_ ?_).of_eq fun p => (h_rec p).symm
  · exact Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
      (Primrec.fst.comp Primrec.fst)
  · exact Primrec.option_getD.comp
      (Primrec.list_getElem?.comp
        (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp <| Primrec.fst.comp Primrec.fst)

/-- `ackBddRow` is primitive recursive. -/
lemma ackBddRow_primrec : Primrec₂ ackBddRow := by
  have h_base : Primrec fun B : ℕ => (List.range (B + 1)).map fun m => min (m + 1) B := by
    refine Primrec.list_map (Primrec.list_range.comp Primrec.succ) ?_
    exact Primrec.nat_min.comp (Primrec.succ.comp Primrec.snd) Primrec.fst
  have h_step_curried : Primrec₂ fun (B : ℕ) (prev : List ℕ) =>
      (List.range (B + 1)).map (ackBddEntry B prev) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
      ackBddEntry_primrec
  have h_step : Primrec₂ fun (B : ℕ) (p : ℕ × List ℕ) =>
      (List.range (B + 1)).map (ackBddEntry B p.2) :=
    h_step_curried.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  refine (Primrec.nat_rec h_base h_step).of_eq fun B k => ?_
  induction k with
  | zero      => rfl
  | succ k ih => simp [ackBddRow, ih]

/-- `ackBdd` is primitive recursive. -/
lemma ackBdd_primrec :
    Primrec fun p : (ℕ × ℕ) × ℕ => ackBdd p.1.1 p.1.2 p.2 :=
  let h_row : Primrec fun p : (ℕ × ℕ) × ℕ => ackBddRow p.1.1 p.1.2 :=
    ackBddRow_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp h_row Primrec.snd)
    (Primrec.fst.comp Primrec.fst)


/-! #### Primitive recursiveness of `invAck` -/

/-- Characterisation of the graph of `invAck` used to show it is primitive
recursive. -/
lemma invAck_eq_iff (n b : ℕ) :
    invAck n = b ↔ n ≤ ack b b ∧ (b = 0 ∨ ack (b - 1) (b - 1) < n) := by
  refine ⟨fun h => h ▸ ⟨ackDiag_invAck n, ?_⟩,
    fun ⟨h1, h2⟩ => le_antisymm (invAck_le_iff.mpr h1) ?_⟩
  · rcases Nat.eq_zero_or_pos (invAck n) with hα | hα
    · exact .inl hα
    · exact .inr (lt_invAck_iff.mp (Nat.sub_lt hα Nat.one_pos))
  · rcases h2 with rfl | hlt
    · exact Nat.zero_le _
    · have := lt_invAck_iff.mpr hlt; omega

/-- The graph of `invAck` is a primitive recursive relation. -/
private lemma invAck_graph_primrec : PrimrecRel fun (n b : ℕ) => invAck n = b := by
  have h_bb : Primrec fun p : ℕ × ℕ => ackBdd p.1 p.2 p.2 :=
    ackBdd_primrec.comp (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd) Primrec.snd)
  have h_pred : Primrec fun p : ℕ × ℕ => ackBdd p.1 (p.2 - 1) (p.2 - 1) :=
    let h_b1 : Primrec fun p : ℕ × ℕ => p.2 - 1 :=
      Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
    ackBdd_primrec.comp (Primrec.pair (Primrec.pair Primrec.fst h_b1) h_b1)
  have h_eq : PrimrecRel fun n b : ℕ => ackBdd n b b = n :=
    Primrec.eq.comp h_bb Primrec.fst
  have h_lt : PrimrecRel fun n b : ℕ => ackBdd n (b - 1) (b - 1) < n :=
    Primrec.nat_lt.comp h_pred Primrec.fst
  have h_zero : PrimrecRel fun (_ b : ℕ) => b = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  refine (h_eq.and (h_zero.or h_lt)).of_eq fun ⟨n, b⟩ => ?_
  simp only [invAck_eq_iff, le_ack_iff_ackBdd_eq, ack_lt_iff_ackBdd_lt]

/-- `invAck` is primitive recursive, even though `fun k => ack k k` is not (see
`not_nat_primrec_ack_self`). The bounded search uses `invAck_le_self` together
with `invAck_graph_primrec`. -/
theorem invAck_primrec : Nat.Primrec invAck := by
  rw [← Primrec.nat_iff]
  exact Primrec.of_graph ⟨id, Primrec.id, invAck_le_self⟩ invAck_graph_primrec

end InvAckPrimrec

end InverseAckermann
