import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

import GraphLib.Graph.Basic
import GraphLib.Graph.Finite
import GraphLib.Graph.Degree
import GraphLib.Theory.Spectral.Cuts
import GraphLib.Theory.Spectral.Helper

-- Cuts and contractions (undirected simple)
-- Authors: Yuchen Zhong, Weixuan Yuan
-- LLM: Gemini, GPT-5.5 on codex

set_option tactic.hygienic false

open Finset
open Cuts

namespace GraphLib

variable {α : Type*} [DecidableEq α]

noncomputable def edgeExpansion (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (S : Finset α) : ℝ :=
  ( (Cut G S).card : ℝ ) / ( (d * S.card) : ℝ )

noncomputable def graphExpansion (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) : ℝ :=
  let validSubsets := (G.vertexFinset.powerset).filter (fun S => S.Nonempty ∧ 2 * S.card ≤ (G.vertexFinset).card)
  if h : validSubsets.Nonempty then
    (validSubsets.image (fun S => edgeExpansion G d S)).min' (by
      -- The image of a non-empty set is non-empty.
      exact Finset.Nonempty.image h (fun S => edgeExpansion G d S)
    )
  else 0

noncomputable def SimpleGraph.rayleighQuotient (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) : ℝ :=
  let numerator := G.edgeFinset.sum (fun e =>
    e.lift ⟨fun u v => (x u - x v)^2, by
      intro u v
      dsimp
      ring
    ⟩
  )
  let denominator := G.vertexFinset.sum (fun v => (G.degree v : ℝ) * (x v)^2)
  numerator / denominator

lemma rayleighQuotient_nonneg (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
  0 ≤ G.rayleighQuotient x := by
  unfold SimpleGraph.rayleighQuotient
  apply div_nonneg
  · -- Numerator: ∑ (x u - x v)² ≥ 0
    apply sum_nonneg
    intro e _
    -- Use Sym2.inductionOn to handle the unordered pair
    induction e using Sym2.inductionOn with
    | hf u v =>
      dsimp
      exact sq_nonneg (x u - x v)
  · -- Denominator: ∑ d_v * x_v² ≥ 0
    apply sum_nonneg
    intro v _
    apply mul_nonneg
    · -- Degrees are natural numbers, so their real coercion is ≥ 0
      norm_cast
      exact Nat.zero_le _
    · -- Squares are ≥ 0
      exact sq_nonneg (x v)

def orthogonalVectors (G : SimpleGraph α) [Finite G.vertexSet] : Set (α → ℝ) :=
  { x | (G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0) ∧ (∃ v ∈ G.vertexFinset, x v ≠ 0) }

def R_values (G : SimpleGraph α) [Finite G.vertexSet] : Set ℝ :=
  { r | ∃ x ∈ orthogonalVectors G, r = G.rayleighQuotient x }

noncomputable def lambda2 (G : SimpleGraph α) [Finite G.vertexSet] : ℝ :=
  sInf (R_values G)

-- lambda2 ≥ 0
lemma lambda2_bounded_below (G : SimpleGraph α) [Finite G.vertexSet] :
  BddBelow { r : ℝ | ∃ x : α → ℝ, (G.vertexFinset.sum (fun v => (G.degree v : ℝ) * x v) = 0) ∧
    (∃ v ∈ G.vertexFinset, x v ≠ 0) ∧ r = G.rayleighQuotient x } := by
  use 0
  intro r hr
  simp only [Set.mem_setOf_eq] at hr
  rcases hr with ⟨x, _, _, rfl⟩
  apply rayleighQuotient_nonneg

noncomputable def SimpleGraph.energy (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v ↦ (x u - x v) ^ 2, by
    expose_names
    intro a1 a2
    dsimp
    rw [← neg_sub]
    linarith
  ⟩ e

lemma energy_nonneg (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
    0 ≤ G.energy x := by
  unfold SimpleGraph.energy
  apply Finset.sum_nonneg
  intro e he
  induction e using Sym2.ind
  case h =>
    dsimp
    apply sq_nonneg

lemma energy_mul (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) (c : ℝ) :
    G.energy (fun v => c * x v) = c ^ 2 * G.energy x := by
  classical
  unfold SimpleGraph.energy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h u =>
    simp
    ring_nf

noncomputable def SimpleGraph.deg_norm (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) : ℝ :=
  ∑ v ∈ G.vertexFinset, ↑(G.degree v) * x v ^ 2

lemma deg_norm_nonneg (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
    0 ≤ G.deg_norm x := by
  unfold SimpleGraph.deg_norm
  apply Finset.sum_nonneg
  intro v hv
  apply mul_nonneg
  · norm_cast
    exact Nat.zero_le _
  · exact sq_nonneg (x v)

lemma deg_norm_eq_sum_reg (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) (d : ℕ)
    (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) :
    G.deg_norm x = ∑ v ∈ G.vertexFinset, (d : ℝ) * x v ^ 2 := by
  unfold SimpleGraph.deg_norm
  apply Finset.sum_congr rfl
  intro v hv
  rw [h_reg v hv]

lemma deg_norm_mul (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) (c : ℝ) :
    G.deg_norm (fun v => c * x v) = c ^ 2 * G.deg_norm x := by
  classical
  unfold SimpleGraph.deg_norm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

lemma deg_norm_shifted_parts_add (G : SimpleGraph α) [Finite G.vertexSet] (z : α → ℝ) :
    G.deg_norm (fun v => max (z v) 0) +
      G.deg_norm (fun v => max (-(z v)) 0) =
        G.deg_norm z := by
  unfold SimpleGraph.deg_norm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← mul_add, pos_neg_sq_add]

lemma energy_shifted_parts_add_le (G : SimpleGraph α) [Finite G.vertexSet] (z : α → ℝ) :
    G.energy (fun v => max (z v) 0) +
      G.energy (fun v => max (-(z v)) 0) ≤
        G.energy z := by
  unfold SimpleGraph.energy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  induction e using Sym2.ind
  case h =>
    dsimp
    exact pos_neg_sub_sq_add_le (z x) (z y)

lemma rQ_eq_energy_div_norm (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
    G.rayleighQuotient x = G.energy x / G.deg_norm x := by
  unfold SimpleGraph.rayleighQuotient
  rfl

lemma rayleighQuotient_mul (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) {c : ℝ} (hc : c ≠ 0) :
    G.rayleighQuotient (fun v => c * x v) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
  rw [energy_mul, deg_norm_mul]
  field_simp [pow_ne_zero 2 hc]


noncomputable def restrictToVertexSet (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) : α → ℝ :=
  fun v => if v ∈ G.vertexFinset then x v else 0

lemma energy_restrictToVertexSet (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
    G.energy (restrictToVertexSet G x) = G.energy x := by
  classical
  unfold SimpleGraph.energy restrictToVertexSet
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind
  case h =>
    have huV : x_1 ∈ G.vertexFinset := by
      have he' : s(x_1, y) ∈ E(G) := G.mem_edgeFinset.mp he
      have h_inc := G.incidence he' (Sym2.mem_mk_left x_1 y)
      exact G.mem_vertexFinset.mpr h_inc
    have hvV : y ∈ G.vertexFinset := by
      have he' : s(x_1, y) ∈ E(G) := G.mem_edgeFinset.mp he
      have h_inc := G.incidence he' (Sym2.mem_mk_right x_1 y)
      exact G.mem_vertexFinset.mpr h_inc
    simp_all only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_vertexFinset, Sym2.lift_mk, ↓reduceIte]

lemma deg_norm_restrictToVertexSet (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
    G.deg_norm (restrictToVertexSet G x) = G.deg_norm x := by
  classical
  unfold SimpleGraph.deg_norm restrictToVertexSet
  apply Finset.sum_congr rfl
  intro v hv
  simp [hv]

lemma rayleighQuotient_restrictToVertexSet (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ) :
    G.rayleighQuotient (restrictToVertexSet G x) = G.rayleighQuotient x := by
  rw [rQ_eq_energy_div_norm, rQ_eq_energy_div_norm]
  rw [energy_restrictToVertexSet, deg_norm_restrictToVertexSet]

lemma orthogonalVectors_restrictToVertexSet (G : SimpleGraph α) [Finite G.vertexSet] (x : α → ℝ)
    (horth : x ∈ orthogonalVectors G) :
    restrictToVertexSet G x ∈ orthogonalVectors G := by
  classical
  rcases horth with ⟨horth, hne⟩
  constructor
  · unfold restrictToVertexSet
    rw [show (∑ v ∈ G.vertexFinset, ↑(G.degree v) * (if v ∈ G.vertexFinset then x v else 0)) =
        ∑ v ∈ G.vertexFinset, ↑(G.degree v) * x v by
      apply Finset.sum_congr rfl
      intro v hv
      simp [hv]]
    exact horth
  · rcases hne with ⟨v, hv, hxv⟩
    exact ⟨v, hv, by simpa [restrictToVertexSet, hv] using hxv⟩

-- Only consider |S| <= |V|/2 in graph expansion
-- Could be merged with above definition
noncomputable def graphExpansionValidSubsets (G : SimpleGraph α) [Finite G.vertexSet] : Finset (Finset α) :=
  (G.vertexFinset.powerset).filter (fun S => S.Nonempty ∧ 2 * S.card ≤ (G.vertexFinset).card)

lemma mem_graphExpansionValidSubsets_of_valid (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ G.vertexFinset)
    (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    S ∈ graphExpansionValidSubsets G := by
  classical
  simp [graphExpansionValidSubsets, hS_sub, hS_ne, hS_size]

lemma graphExpansionValidSubsets_nonempty_of_valid (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α)
    (hS_ne : S.Nonempty) (hS_sub : S ⊆ G.vertexFinset)
    (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    (graphExpansionValidSubsets G).Nonempty := by
  exact ⟨S, mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size⟩

lemma edgeExpansion_mem_graphExpansion_image_of_valid (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ)
    (S : Finset α) (hS_ne : S.Nonempty) (hS_sub : S ⊆ G.vertexFinset)
    (hS_size : 2 * S.card ≤ (G.vertexFinset).card) :
    edgeExpansion G d S ∈ (graphExpansionValidSubsets G).image (fun T => edgeExpansion G d T) := by
  exact Finset.mem_image.mpr
    ⟨S, mem_graphExpansionValidSubsets_of_valid G S hS_ne hS_sub hS_size, rfl⟩

lemma edgeExpansion_zero_degree (G : SimpleGraph α) [Finite G.vertexSet] (S : Finset α) :
    edgeExpansion G 0 S = 0 := by
  unfold edgeExpansion
  simp

lemma graphExpansion_zero_degree (G : SimpleGraph α) [Finite G.vertexSet] :
    graphExpansion G 0 = 0 := by
  classical
  unfold graphExpansion
  dsimp only
  split_ifs with h
  · apply le_antisymm
    · obtain ⟨S, hS⟩ := h
      have hm : edgeExpansion G 0 S ∈ (Finset.image (fun S => edgeExpansion G 0 S)
          {S ∈ G.vertexFinset.powerset | S.Nonempty ∧ 2 * #S ≤ #G.vertexFinset}) := by
        exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
      have hz : edgeExpansion G 0 S = 0 := edgeExpansion_zero_degree G S
      simpa [hz] using Finset.min'_le _ _ hm
    · apply Finset.le_min'
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
      rw [edgeExpansion_zero_degree]
  · rfl


end GraphLib
