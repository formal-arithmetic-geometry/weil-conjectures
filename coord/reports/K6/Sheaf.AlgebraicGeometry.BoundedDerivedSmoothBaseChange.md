## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth`
in `Sheaf.AlgebraicGeometry.BoundedDerivedSmoothBaseChange` by reusing the source library's
module-coefficient bounded-below smooth base-change theorem and its canonical unbounded
comparison. Extracted the lower cohomological bound from the given bounded constructibility
hypothesis; supplied the torsion condition on every cohomology sheaf directly from the
positive annihilator N and its invertibility on S. The theorem signature, coefficient
conventions, constructibility predicate and specified unbounded exchange are unchanged.

The upstream constructibility predicate differs from this project's predicate, so the
proof uses the general bounded-below theorem, which only needs the lower bound and
invertible-order torsion. No conversion between those predicates is asserted. The existing
upstream proof reduces to the recorded sheaf smooth-base-change declaration and uses
triangulated truncation devissage. The unit `sk-rem-rest` has no prescribed proof steps or
realized nodes to bypass.

Added proof imports of `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived`,
`WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus`, and
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison`. Updated the declaration's proof
docstring and the existing DAG node's proof, proof dependencies, proof origin and obsolete
tool approvals to match this route. Preserved the existing public import interface,
removing only its duplicate identical import command. No definitions or statements changed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_boundedConstructible_of_smooth`
(node `sbc-thm-bounded-derived-smooth-base-change`). There are zero local holes left and
zero holes added; no statement was split off. This reuses existing library declarations,
whose own transitive proof obligations remain with their nodes.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`
- `Sheaf.AlgebraicGeometry.HypercohomologyConvergence`
- `Sheaf.AlgebraicGeometry.FiniteRangeComparison`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`
- `Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility`
- `Sheaf.AlgebraicGeometry.HypercohomologyConvergenceStatement`

The smooth sheaf theorem is still used through the upstream derived theorem's public
imports. The generic derived map and Cartesian square definitions remain available from
the statement imports and the new upstream proof imports. These three removed imports
are redundant direct imports, not pruned mathematical dependencies.

The proof no longer needs the declarations of
`lem-kun-unbounded-abelian-exchange-comparison`,
`lem-weil-pbc-truncation-couple-morphism`,
`lemma-weil-pbc-hypercohomology-convergence`, `sbc-lem-finite-range-comparison`, or
`lem-sbc-abelian-derived-exchange-plus-compatibility`. Their obsolete tool approvals were
removed in the existing node. The seven Sheaf proof modules above are unnecessary for
this proof; other library consumers may still need them. Coefficient forgetting and the
abelian exact-couple/convergence construction are replaced by an already proved direct
module-coefficient result. The upper bound and the constructibility of the cohomology
sheaves need not be used by this stronger upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan was mathematically valid but unnecessarily long given the existing
source-library module-coefficient derived smooth-base-change theorem and its canonical
D+/unbounded comparison. Library searches by theorem name and by smooth base-change and
bounded-constructibility terminology found these declarations. The preserved search log
also records LeanFinder and Loogle searches; they returned algebraic smoothness and
functorial isomorphism facts, not an additional Mathlib smooth sheaf base-change theorem.
No mathematical statement dispute, definition repair, new node, or forced consumer
adaptation is needed.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
