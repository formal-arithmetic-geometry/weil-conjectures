module

public import Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal

/-! # The tensor differential before paired cubical faces cancel

This is the expansion and reindexing part of the agent-written cubical calculation,
original diagonal proof steps 2–3. No shuffle-sign identity or cancellation is asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace IntegralLatticeCubical

/-- Expand the total tensor differential and index its two families of faces by a removed
coordinate and a partition of the remaining coordinates. Source: steps 1–2 of the retained
agent-written finite calculation in `lem-sfb-cubical-partition-boundary-expansion`, originally
steps 2–3 of the integral cubical diagonal proof. The blueprint direct-images paragraph (3)
is only the route location; an exact external reference remains WANTED.
(blueprint: lem-sfb-cubical-partition-differential-faces).

Proof: Evaluate the linear extension `diagonalComponent` on its free generator to obtain
its powerset sum. Each partition has total degree `I.card`, by disjointness and the
cardinality of a set difference. Distribute the total differential over this finite sum
and its integer coefficients. On the summand of bidegree `(|A|,|C|)`, the total differential
is the tensor of the first boundary with the identity plus `(-1)^|A|` times the tensor
of the identity with the second boundary. Apply the defining cubical boundary to each
cell and use tensor bilinearity to expand each boundary sum into differences of tensors.
A first face is indexed by `(A,C,i)` with `A` and `C` disjoint, union `I`, and `i` in `A`.
Send it to `(i,A.erase i,C)`. Its inverse inserts `i` into the first part. A second face
is indexed by `(A,C,i)` with `i` in `C`; send it to `(i,A,C.erase i)`, with inverse inserting
`i` into the second part. Removing `i` from the union proves that both new indices are
partitions of `I.erase i`. Conversely neither part of such a partition contains `i`, so
inserting and removing are inverse operations. Enumerate each remaining partition by
`B` in `(I.erase i).powerset`, its complement being `I.erase i \ B`. Reindex the two finite
sums by these inverses. The resulting summands are exactly the two displayed expressions,
with the original shuffle and boundary signs unchanged. A factor of degree zero has no
faces. If `I` is empty both factors have degree zero, the total differential is zero and
the reindexed outer sum is empty. This also handles `r=0`. -/
theorem partitionDifferentialFaces (r : ℕ) (v : Fin r → ℤ) (I : Finset (Fin r)) :
    ((HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).d
        I.card (I.card - 1))
      (diagonalComponent r I.card (cell r (I.card : ℤ) v I)) =
      ∑ i ∈ I, ∑ B ∈ (I.erase i).powerset,
        ((partitionSign r (insert i B) (I.erase i \ B) *
            (-1 : ℤ) ^ ((insert i B).filter (fun j ↦ j < i)).card) •
          (tensorCell r (I.card - 1) (v + unitVector r i)
              (v + directionSum r (insert i B)) ((insert i B).erase i) (I.erase i \ B) -
            tensorCell r (I.card - 1) v (v + directionSum r (insert i B))
              ((insert i B).erase i) (I.erase i \ B)) +
        (partitionSign r B (insert i (I.erase i \ B)) * (-1 : ℤ) ^ B.card *
            (-1 : ℤ) ^ ((insert i (I.erase i \ B)).filter (fun j ↦ j < i)).card) •
          (tensorCell r (I.card - 1) v (v + directionSum r B + unitVector r i) B
              ((insert i (I.erase i \ B)).erase i) -
            tensorCell r (I.card - 1) v (v + directionSum r B) B
              ((insert i (I.erase i \ B)).erase i))) := by sorry

end IntegralLatticeCubical
