import GraphAlgorithms.SimpleGraphs.WeightedGraphs.WeightedSimpleGraphs
import GraphAlgorithms.SimpleGraphs.WeightedGraphs.Walk
import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic

set_option tactic.hygienic false

variable {α : Type*} [DecidableEq α]

open Finset

def is_connected (G : WeightedSimpleGraph α) : Prop := 
  ∀ u v: α , u ≠ v →  ∃ p: Walk α, Path.IsPathIn G p

noncomputable def kruskal
    (G : WeightedSimpleGraph α)
    (h : is_connected G)
    (partitions : Finset (Finset α))
    (h_part : ∀ v ∈ G.vertexSet, ∃! P ∈ partitions, v ∈ P)
    (redEdges blueEdges : Finset (Edge α)) : Finset (Edge α) :=

  let E : Finset (Edge α) := G.edgeSet \ (redEdges ∪ blueEdges)

  if hE : E.Nonempty then

    let findPartition :=
      fun (v : α) =>
      fun (hv : v ∈ G.vertexSet) =>
        Classical.choose (ExistsUnique.exists (h_part v hv))

    let minWeight :=
      (E.image G.edgeWeight).min'
        (hE.image G.edgeWeight)

    let minEdgeWeight := E.filter (fun p => G.edgeWeight p ≤ minWeight)

    let validBlueEdges := minEdgeWeight.attach.filter (fun ⟨e, he⟩ =>
          let u := e.out.1
          let v := e.out.2
          have he_G : e ∈ G.edgeSet := by simp [minEdgeWeight,E] at he; simp [he]
          have hu_mem : u ∈ e := Sym2.out_fst_mem e
          have hv_mem : v ∈ e := Sym2.out_snd_mem e
          let hu_mem_g : u ∈ G.vertexSet := G.incidence e he_G u hu_mem
          let hv_mem_g : v ∈ G.vertexSet := G.incidence e he_G v hv_mem
          findPartition u hu_mem_g ≠ findPartition v hv_mem_g
      )
    let validBlueEdge_set : Finset (Edge α) := validBlueEdges.map (Function.Embedding.subtype (· ∈ minEdgeWeight))
    let validRedEdges := minEdgeWeight \ validBlueEdge_set
    if hx: validBlueEdge_set.Nonempty then
      let e := Classical.choose hx
      let newBlue := blueEdges ∪ {e}
      sorry
    else
      have hxr : validRedEdges.Nonempty := by
        have h1 : minEdgeWeight.Nonempty := by
          simp [minEdgeWeight, minWeight, hE, Finset.Nonempty]
          have hl2 := (Finset.min'_eq_iff (E.image G.edgeWeight) ((hE.image G.edgeWeight)) minWeight).mp
          simp [minWeight] at hl2
          obtain ⟨ha, hb⟩ := hl2
          obtain ⟨a, hb2⟩ := ha
          use a
          simp [← hb2.right] at hb
          constructor
          . exact hb2.left
          intro a2 ha2
          exact hb a2 ha2
        simp at hx
        have hsub : validBlueEdge_set ⊆ minEdgeWeight = by
          sorry

        have hadd := Finset.card_sub_card_eq validBlueEdge_set minEdgeWeight
        

      sorry



    -- continue Kruskal:
    -- choose an edge in validEdges with weight minWeight,
    -- colour it blue, merge partitions, recurse, etc.
    sorry
  else
    blueEdges

