module

public import WeilConjectures.ConstructibleSheaf.Refinement

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite stratification of a Noetherian scheme admits an irreducible refinement.
Source: Stacks Project, Tags 0052 (1)-(3) and 0BA8; blueprint
`lem-weil-pbc-irreducible-refinement`.

Proof: each stratum, with its induced topology, is Noetherian. List its distinct
irreducible components C_1, ..., C_r, which are closed and cover the stratum, and set
P_j = C_j minus the union of the earlier components. This is open in C_j and locally
closed in the stratum. It is nonempty: otherwise irreducibility of C_j and finiteness
would force C_j to lie in an earlier component, contradicting maximality and distinctness.
Thus P_j is irreducible. The P_j are disjoint and cover the stratum, since each point
belongs to a first component. Omit empty original strata, which have no components.
Their images in X are locally closed, and hence constructible since X is Noetherian.
Realize each image by its reduced locally closed subscheme, whose underlying space is
homeomorphic to P_j. The finitely many pieces over all original strata give T; inclusion
of each piece in its original stratum proves T.Refines S. If X is empty, use n = 0.
(blueprint: lem-weil-pbc-irreducible-refinement-topological)
-/
theorem exists_irreducible_refinement_topological
    (X : Scheme.{u}) [IsNoetherian X] (S : Stratification X) :
    ∃ T : Stratification X,
      T.Refines S ∧ ∀ i : Fin T.n, IrreducibleSpace (T.domain i) := by
  sorry

end AlgebraicGeometry.Scheme
