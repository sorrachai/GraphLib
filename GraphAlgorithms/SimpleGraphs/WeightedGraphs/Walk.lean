import GraphAlgorithms.SimpleGraphs.Walk
import GraphAlgorithms.SimpleGraphs.WeightedGraphs.WeightedSimpleGraphs

-- Authors: Christos Demetriou

namespace Walk

set_option tactic.hygienic false

/-- A walk `w` is a walk in graph `G` if every consecutive pair of vertices
    forms an edge in `G`, and the starting vertex lies in the vertex set. -/
inductive IsWalkInWG {V : Type*} (G : WeightedSimpleGraph V) : Walk V → Prop
  | singleton (v : V) (hv : v ∈ G.vertexSet)
    : IsWalkInWG G ⟨.singleton v, .singleton v⟩
  | cons (w : Walk V) (u : V)
      (hw   : IsWalkInWG G w)
      (hedg : s(w.tail, u) ∈ G.edgeSet)
    : IsWalkInWG G (w.append_single u (by have : ∀ e ∈ G.edgeSet, ¬ e.IsDiag :=  G.loopless; grind))
end Walk

-- Analytical definition of `path` for bfs correctness analysis.
namespace Path

open Walk
variable {α : Type*} [DecidableEq α]

/-- A path is a walk whose support (the list of vertices from VertexSeq.toList)
    has no duplicate vertices — List.Nodup. -/
def IsPathIn (G : WeightedSimpleGraph α) (w : Walk α) : Prop := IsWalkInWG G w ∧ w.IsPath

end Path
