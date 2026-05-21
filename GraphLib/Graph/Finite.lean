def SimpleGraph.vertexFinset (G : SimpleGraph α) [Finite G.vertexSet] : Finset α :=
  sorry

theorem SimpleGraph.fin_vertexSet_fin_edgeSet (G : SimpleGraph α)
    (hfin : Finite G.vertexSet) : Finite G.edgeSet := by
  sorry

def SimpleGraph.edgeFinset (G : SimpleGraph α) [Finite G.vertexSet] : Finset (Sym2 α) :=
  sorry

def SimpleDiGraph.vertexFinset (G : SimpleGraph α) [Finite G.vertexSet] : Finset α :=
  sorry

theorem SimpleDiGraph.fin_vertexSet_fin_edgeSet (G : SimpleDiGraph α)
    (hfin : Finite G.vertexSet) : Finite G.edgeSet := by
  sorry

def SimpleDiGraph.edgeFinset (G : SimpleGraph α) [Finite G.vertexSet] : Finset (Sym2 α) :=
  sorry

theorem SimpleGraph.card_edgeFinset_le_card_choose_two
    (G : SimpleGraph α) [Finite G.vertexSet] :
    G.edgeFinset.card ≤ G.vertexFinset.card.choose 2 := by
  sorry

theorem SimpleDiGraph.card_edgeFinset_le_two_card_choose_two
    (G : SimpleDiGraph α) [Finite G.vertexSet] :
    G.edgeFinset.card ≤ 2 * G.vertexFinset.card.choose 2 := by
  sorry

