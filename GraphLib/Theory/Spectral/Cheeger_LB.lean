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
import GraphLib.Theory.Spectral.Expansion

open Finset
open Cuts

namespace GraphLib

variable {α : Type*} [DecidableEq α]

/-- The "Easy Direction" of Cheeger's Inequality (Section 3).
For a d-regular graph: λ₂ / 2 ≤ ϕ(G). -/
theorem cheeger_easy_direction (G : SimpleGraph α) [Finite G.vertexSet] (d : ℕ) (S : Finset α)
  (hS_nonempty : S.Nonempty) (hS_size : 2 * #S ≤ #G.vertexFinset) (hS_subset : S ⊆ G.vertexFinset)
  (h_reg : ∀ v ∈ G.vertexFinset, G.degree v = d) (hd : d > 0) :
  (lambda2 G) / 2 ≤ edgeExpansion G d S := by
  /-
    Proof Sketch from Lecture:
    1. Define a specific test vector x based on S.
    2. To satisfy x ⊥ D1, let:
         x_v = |V \ S| if v ∈ S
         x_v = -|S|     if v ∉ S
    3. Compute R_L(x).
    4. Show R_L(x) = |E(S, V \ S)| * |V| / (d * |S| * |V \ S|).
    5. Show this is ≤ 2 * ϕ(S) from |S| ≤ |V| / 2.
  -/
  let n : ℝ := (#G.vertexFinset : ℝ)
  let s : ℝ := (#S : ℝ)
  let x : α → ℝ := fun v => if v ∈ S then (n - s) else -s
  have h_sum_zero : ∑ v ∈ G.vertexFinset, x v = 0 := by
    simp only [x]; let Sc := G.vertexFinset \ S
    have h_union : G.vertexFinset = S ∪ Sc := by
      grind [Finset.union_sdiff_self_eq_union]
    rw [h_union, Finset.sum_union (Finset.disjoint_sdiff)]
    have h1 : ∑ v ∈ S, (if v ∈ S then n - s else -s) = s * (n - s) := by
      rw [Finset.sum_congr rfl (fun v hv => if_pos hv)]
      rw [Finset.sum_const]
      grind [nsmul_eq_mul]
    have h2 : ∑ v ∈ Sc, (if v ∈ S then n - s else -s) = (n - s) * (-s) := by
      rw [Finset.sum_congr rfl (fun v hv => if_neg (Finset.mem_sdiff.1 hv).2)]
      rw [Finset.sum_const]
      have h_card_Sc : ↑(#Sc) = n - s := by
        have h_union_card : #(S ∪ Sc) = #S + #Sc := by
          apply Finset.card_union_of_disjoint; exact Finset.disjoint_sdiff
        have h_V_eq : G.vertexFinset = S ∪ Sc := by
          unfold Sc; rw [Finset.union_sdiff_self_eq_union]; grind
        have h_sum : #G.vertexFinset = #S + #Sc := by
          rw [← h_union_card, ← h_V_eq]
        unfold n s
        have h_sum_R : (↑(#G.vertexFinset) : ℝ) = ↑(#S) + ↑(#Sc) := by
          norm_cast
        linarith
      simp only [smul_neg, nsmul_eq_mul, mul_neg, neg_inj, mul_eq_mul_right_iff]
      left
      exact h_card_Sc
    rw [h1, h2]; ring
  have h_orth : ∑ v ∈ G.vertexFinset, (G.degree v : ℝ) * x v = 0 := by
    rw [← mul_zero (d : ℝ), ← h_sum_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv; simp [h_reg v hv]
  have h_x_ne_zero : ∃ v ∈ G.vertexFinset, x v ≠ 0 := by
    rcases hS_nonempty with ⟨v, hv⟩
    use v, hS_subset hv
    simp only [hv, ↓reduceIte, ne_eq, x]
    intro h_zero
    have : n = s := by linarith
    have h_size_real : 2 * s ≤ n := by
      unfold n s; norm_cast
    rw [this] at h_size_real
    have h_s_pos : 0 < s := by
      unfold s; norm_cast; grind
    linarith
  have h_lambda_le_rq : lambda2 G ≤ G.rayleighQuotient x := by
    unfold lambda2; apply csInf_le
    · use 0; intro r hr; rcases hr with ⟨w, _, rfl⟩
      exact rayleighQuotient_nonneg (G := G) w
    · refine ⟨x, ?_, rfl⟩; exact ⟨h_orth, h_x_ne_zero⟩
  have h_rq_le_two_phi : G.rayleighQuotient x ≤ 2 * edgeExpansion G d S := by
    -- We follow the lecture derivation in three layers:
    -- (1) exact numerator formula,
    -- (2) exact denominator formula,
    -- (3) scalar comparison n/(n-s) ≤ 2.
    unfold SimpleGraph.rayleighQuotient edgeExpansion
    let dS := G.edgeFinset.filter (fun e =>
      ∃ u ∈ G.vertexFinset, u ∈ e ∧ u ∈ S ∧ ∃ v ∈ G.vertexFinset, v ∈ e ∧ v ∉ S)
    let edge_diff := Sym2.lift ⟨fun u v => (x u - x v)^2, by
      intro u v; dsimp; ring⟩
    -- Layer 1: numerator = n^2 * |dS|.
    have h_num_total : ∑ e ∈ G.edgeFinset, edge_diff e = n^2 * ↑(#dS) := by
      -- 1) dS is a subset of G.edgeFinset.
      have h_sub : dS ⊆ G.edgeFinset := by
        intro e he; simp only [dS, Finset.mem_filter] at he; exact he.1
      -- 2) Edges outside dS contribute 0, hence the full sum equals the dS-sum.
      have h_sum_is_dS : ∑ e ∈ G.edgeFinset, edge_diff e = ∑ e ∈ dS, edge_diff e := by
        rw [Finset.sum_subset h_sub]; intro e he_G he_ndS; by_contra h_nz
        have h_cross : ∃ u ∈ e, u ∈ S ∧ ∃ v ∈ e, v ∉ S := by
          obtain ⟨u, v⟩ := e
          unfold edge_diff at h_nz
          simp only [Sym2.lift_mk] at h_nz
          unfold x at h_nz
          split_ifs at h_nz with huS hvS
          · simp at h_nz
          · refine ⟨u, by simp, huS, v, by simp, hvS⟩
          · refine ⟨v, by simp, ?_, u, by simp, huS⟩
            simp_all only [mul_ite, mul_neg, ne_eq, filter_subset,
              mem_filter, Sym2.mem_iff, true_and, not_exists, not_and,
              Decidable.not_not, x, n, s, dS]
          · simp at h_nz
        have he_in_dS : e ∈ dS := by
          simp only [dS, Finset.mem_filter]
          use he_G
          rcases h_cross with ⟨u, hu_e, hu_S, v, hv_e, hv_nS⟩
          use u, G.mem_vertexFinset.mpr (G.incidence (G.mem_edgeFinset.mp he_G) hu_e), hu_e, hu_S
          use v, G.mem_vertexFinset.mpr (G.incidence (G.mem_edgeFinset.mp he_G) hv_e), hv_e, hv_nS
        exact he_ndS he_in_dS
      rw [h_sum_is_dS]
      -- 3) Every edge in dS contributes exactly n^2.
      have h_const : ∀ e ∈ dS, edge_diff e = n^2 := by
        intro e he
        simp only [dS, Finset.mem_filter] at he
        rcases he with ⟨he_G, u, hu_V, hu_e, hu_S, v, hv_V, hv_e, hv_nS⟩
        obtain ⟨u', v'⟩ := e
        unfold edge_diff
        simp only [Sym2.lift_mk]
        unfold x
        split_ifs with h1 h2
        · have h_v_mem : v = u' ∨ v = v' := by simpa using hv_e
          rcases h_v_mem with rfl | rfl
          · exact (hv_nS h1).elim
          · exact (hv_nS h2).elim
        · ring
        · ring
        · have h_u_mem : u = u' ∨ u = v' := by simpa using hu_e
          rcases h_u_mem with rfl | rfl
          · exfalso
            exact h1 hu_S
          · exfalso
            have hu_not : u ∉ S := by aesop
            exact hu_not hu_S
      rw [Finset.sum_congr rfl h_const]
      simp only [sum_const, nsmul_eq_mul]
      rw [mul_comm]
    -- Layer 2a: pull out regular degree in denominator.
    have h_den_match : ∑ v ∈ G.vertexFinset, ↑(G.degree v) * x v ^ 2 = ↑d * ∑ v ∈ G.vertexFinset, x v ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro v hv
      rw [h_reg v hv]
    -- Layer 2b: evaluate ∑ x(v)^2 explicitly.
    have h_denom : (d : ℝ) * ∑ v ∈ G.vertexFinset, (x v)^2 = (d : ℝ) * n * s * (n - s) := by
      rw [← Finset.sum_sdiff hS_subset]
      have h_sum_S : ∑ v ∈ S, (x v)^2 = s * (n - s)^2 := by
        unfold x
        rw [Finset.sum_congr rfl (fun v hv => by rw [if_pos hv])]
        rw [Finset.sum_const]
        simp [s]
      have h_sum_Sc : ∑ v ∈ G.vertexFinset \ S, (x v)^2 = (n - s) * s^2 := by
        unfold x
        rw [Finset.sum_congr rfl (fun v hv => by
          have h_not_in_S : v ∉ S := (Finset.mem_sdiff.1 hv).2
          rw [if_neg h_not_in_S])]
        rw [Finset.sum_const]
        rw [Finset.card_sdiff]
        simp only [even_two, Even.neg_pow, nsmul_eq_mul, mul_eq_mul_right_iff, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
        left
        rw [Finset.inter_comm]
        rw [Finset.inter_eq_right.mpr hS_subset]
        rw [Nat.cast_sub]
        grind
      rw [h_sum_S, h_sum_Sc]
      ring
    -- Rewrite Rayleigh quotient using the two formulas above.
    rw [h_num_total, h_den_match, h_denom]
    -- Convert |Cut G S| into |dS|.
    have h_cut_val : ↑(#(Cut G S)) = ↑(#dS) := by
      congr
      ext e
      constructor
      · intro he
        simp only [Cut, dS, Finset.mem_filter] at he ⊢
        rcases he with ⟨heE, u, huS, hu_e, v, hvSc, hv_e⟩
        rcases Finset.mem_sdiff.mp hvSc with ⟨hvV, hvnS⟩
        exact ⟨heE, u, by grind, hu_e, huS, v, hvV, hv_e, hvnS⟩
      · intro he
        simp only [Cut, dS, Finset.mem_filter] at he ⊢
        rcases he with ⟨heE, u, huV, hu_e, huS, v, hvV, hv_e, hvnS⟩
        exact ⟨heE, u, huS, hu_e, v, Finset.mem_sdiff.mpr ⟨hvV, hvnS⟩, hv_e⟩
    rw [h_cut_val]
    -- Prepare non-vanishing side conditions for `field_simp`.
    unfold n s at *
    have h_s_ne_zero : (↑(#S) : ℝ) ≠ 0 := by
      have hS_pos : 0 < #S := by
        rcases hS_nonempty with ⟨v, hv⟩
        exact Finset.card_pos.mpr ⟨v, hv⟩
      exact ne_of_gt (by exact_mod_cast hS_pos)
    have h_d_ne_zero : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hd)
    have h_ns_ne_zero : (↑(#G.vertexFinset) : ℝ) - ↑(#S) ≠ 0 := by
      intro h_eq
      have h_n_eq_s : (↑(#G.vertexFinset) : ℝ) = ↑(#S) := by linarith
      have h_size_real : (2 : ℝ) * ↑(#S) ≤ ↑(#G.vertexFinset) := by
        exact_mod_cast hS_size
      rw [h_n_eq_s] at h_size_real
      have hS_pos : (0 : ℝ) < ↑(#S) := by
        have hS_pos_nat : 0 < #S := by
          rcases hS_nonempty with ⟨v, hv⟩
          exact Finset.card_pos.mpr ⟨v, hv⟩
        exact_mod_cast hS_pos_nat
      linarith
    -- Layer 3: pure scalar inequality after cancellation.
    field_simp [h_s_ne_zero, h_d_ne_zero, h_ns_ne_zero]
    have h_size_real : (2 : ℝ) * ↑(#S) ≤ ↑(#G.vertexFinset) := by
      exact_mod_cast hS_size
    -- Equivalent to n ≤ 2*(n-s), i.e. 2s ≤ n.
    have h_dS_nonneg : (0 : ℝ) ≤ ↑(#dS) := by positivity
    have hS_pos : (0 : ℝ) < ↑(#S) := by
      have hS_pos_nat : 0 < #S := by
        rcases hS_nonempty with ⟨v, hv⟩
        exact Finset.card_pos.mpr ⟨v, hv⟩
      exact_mod_cast hS_pos_nat
    have h_ns_pos : (0 : ℝ) < (↑(#G.vertexFinset) : ℝ) - ↑(#S) := by
      nlinarith [h_size_real, hS_pos]
    have h_ratio_le_two :
        (↑(#G.vertexFinset) : ℝ) / ((↑(#G.vertexFinset) : ℝ) - ↑(#S)) ≤ 2 := by
      rw [div_le_iff₀ h_ns_pos]
      nlinarith [h_size_real]
    have h_main :
        (↑(#G.vertexFinset) : ℝ) * ↑(#dS) / ((↑(#G.vertexFinset) : ℝ) - ↑(#S)) ≤ ↑(#dS) * 2 := by
      have hmul :
          ((↑(#G.vertexFinset) : ℝ) / ((↑(#G.vertexFinset) : ℝ) - ↑(#S))) * ↑(#dS) ≤ 2 * ↑(#dS) :=
        mul_le_mul_of_nonneg_right h_ratio_le_two h_dS_nonneg
      convert hmul using 1 <;> ring
    exact h_main
  have h_lambda_le_two_phi : lambda2 G ≤ 2 * edgeExpansion G d S :=
    h_lambda_le_rq.trans h_rq_le_two_phi
  nlinarith [h_lambda_le_two_phi]

end GraphLib
