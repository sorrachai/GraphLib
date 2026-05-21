/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Antoine du Fresne von Hohenesche,
  Sorrachai Yingchareonthawornchai
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Tree.Basic

@[expose] public section

/-!
# Binary Tree

In this file we introduce the `Tree` data structure and its basic operations.
-/

variable {α : Type}

/-- A tree node -/
notation:65 l:66 " △[" v "] " r:66 => Tree.node v l r

namespace Tree

/-! ### Core Definitions -/
section CoreDefs

theorem non_empty_exist (s : Tree α) (h : s ≠ .nil) :
    ∃ A k B, s = A △[k] B := by
  induction s <;> grind

def num_nodes : Tree α → ℕ
  | .nil => 0
  | .node _ l r => 1 + num_nodes l + num_nodes r

@[simp] lemma num_nodes_empty : num_nodes (nil : Tree α) = 0 := rfl

@[simp] lemma num_nodes_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl

/-- In-order traversal as a list of keys. -/
def toKeyList : Tree α → List α
  | .nil => []
  | l △[k] r => l.toKeyList ++ [k] ++ r.toKeyList

@[simp] lemma toKeyList_empty : toKeyList (nil : Tree α) = [] := rfl

@[simp] lemma toKeyList_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).toKeyList = l.toKeyList ++ [k] ++ r.toKeyList := rfl

/-- Number of nodes on the search path for `q` in `t`. Zero on the empty
tree; on a node this counts the root plus (if `q ≠ k`) the search path
length in the appropriate subtree. -/
def search_path_len [LinearOrder α] (t : Tree α) (q : α) : ℕ :=
  match t with
  | nil => 0
  | l △[key] r =>
    if q < key then
      1 + l.search_path_len q
    else if key < q then
      1 + r.search_path_len q
    else
      1

/--
Remark:
This implementation is not really a "contain function",
because a binary tree could have q >/< key while being in
the left/right subtree of key respectively.
If `contains t q` is true, then `q` is in `t`; but
the converse need not necessarily hold true. The
converse is true for a binary search tree.
-/
def contains [LinearOrder α] (t : Tree α) (q : α) : Prop :=
  match t with
  | nil => False
  | l △[key] r =>
    if q < key then
      l.contains q
    else if key < q then
      r.contains q
    else
      True

end CoreDefs


/-! ### Rotations and Mirroring -/
section Transformations

def rotateRight : Tree α → Tree α
  | (a △[x] b) △[y] c => a △[x] (b △[y] c)
  | t => t

def rotateLeft : Tree α → Tree α
  | a △[x] (b △[y] c) => (a △[x] b) △[y] c
  | t => t

/-- Mirror a binary tree: swap every left and right subtree. -/
def mirror : Tree α → Tree α
  | .nil => .nil
  | l △[k] r => r.mirror △[k] l.mirror

@[simp] lemma mirror_empty : (nil : Tree α).mirror = nil := rfl

@[simp] lemma mirror_node (l : Tree α) (k : α) (r : Tree α) :
    (l △[k] r).mirror = r.mirror △[k] l.mirror := rfl

@[simp] lemma mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t <;> simp_all

@[simp] lemma num_nodes_mirror (t : Tree α) : t.mirror.num_nodes = t.num_nodes := by
  induction t <;> simp_all [num_nodes]; omega

@[simp] lemma mirror_rotateRight (t : Tree α) :
    (rotateRight t).mirror = rotateLeft t.mirror := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight, rotateLeft, mirror]

@[simp] lemma mirror_rotateLeft (t : Tree α) :
    (rotateLeft t).mirror = rotateRight t.mirror := by
  rcases t with _ | ⟨k, l, (_ | ⟨rk, rl, rr⟩)⟩ <;>
    simp [rotateRight, rotateLeft, mirror]

@[simp] theorem num_nodes_rotateRight (t : Tree α) :
    (rotateRight t).num_nodes = t.num_nodes := by
  rcases t with _ | ⟨k, (_ | ⟨lk, ll, lr⟩), r⟩ <;>
    simp [rotateRight]; omega

@[simp] theorem num_nodes_rotateLeft (t : Tree α) :
    (rotateLeft t).num_nodes = t.num_nodes := by
  have h := num_nodes_rotateRight t.mirror
  simp only [← mirror_rotateLeft, num_nodes_mirror] at h; exact h

end Transformations


/-! ### Contains Characterizations -/
section ContainsLemmas

@[simp] lemma not_contains_empty [LinearOrder α] (q : α) :
    ¬ (nil : Tree α).contains q := nofun

@[simp] lemma contains_node_lt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : q < k) :
    (l △[k] r).contains q ↔ l.contains q := by
  simp [contains, h]

@[simp] lemma contains_node_gt [LinearOrder α] {l : Tree α} {k q : α}
    {r : Tree α} (h : k < q) :
    (l △[k] r).contains q ↔ r.contains q := by
  simp [contains, h, not_lt_of_gt h]

@[simp] lemma contains_node_not_eq_not_lt [LinearOrder α]
    {l : Tree α} {k q : α} {r : Tree α}
    (h1 : ¬ q = k) (h2 : ¬ q < k) :
    (l △[k] r).contains q ↔ r.contains q := by
  have hgt : k < q := lt_of_le_of_ne (Std.not_lt.mp h2) (Ne.symm (Ne.intro h1))
  simp [contains, hgt, not_lt_of_gt hgt]

end ContainsLemmas


/-! ### Tree Invariants and BST Properties -/
section Invariants

/-- BST invariant parameterised by optional lower/upper key bounds.
`IsBSTAux t lb ub` holds iff every key in `t` lies strictly in `(lb, ub)`
(absent bound = ±∞) and children satisfy the BST property recursively. -/
def IsBSTAux [LinearOrder α] : Tree α → Option α → Option α → Prop
  | .nil, _, _ => True
  | l △[k] r, lb, ub =>
      lb.elim True (· < k) ∧
      ub.elim True (k < ·) ∧
      IsBSTAux l lb (some k) ∧
      IsBSTAux r (some k) ub

def IsBST [LinearOrder α] (t : Tree α) : Prop := t.IsBSTAux none none

end Invariants

/-! ### Accessor Lemmas for IsBST -/
section IsBSTAccessors

@[simp] lemma IsBSTAux_node [LinearOrder α] (l : Tree α) (k : α) (r : Tree α)
    (lb ub : Option α) :
    IsBSTAux (l △[k] r) lb ub ↔
      lb.elim True (· < k) ∧ ub.elim True (k < ·) ∧
      IsBSTAux l lb (some k) ∧ IsBSTAux r (some k) ub := Iff.rfl

@[simp] lemma IsBST_node [LinearOrder α] (l : Tree α) (k : α) (r : Tree α) :
    IsBST (l △[k] r) ↔ IsBSTAux l none (some k) ∧ IsBSTAux r (some k) none := by
  simp [IsBST, IsBSTAux]

end IsBSTAccessors

end Tree


/-! ### BST Structure -/
section BSTStructure

structure BST (α : Type) [LinearOrder α] where
  tree : Tree α
  hBST : Tree.IsBST tree

namespace BST

/-- Checks if the BST contains a given key by delegating to the underlying tree. -/
def contains [LinearOrder α] (t : BST α) (q : α) : Prop :=
  t.tree.contains q

end BST

end BSTStructure
