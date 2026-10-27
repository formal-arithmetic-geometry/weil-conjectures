## What changed

Proved `AlgebraicGeometry.ProEtale.closedIdentityOpenHomNormalization` by expanding the
specified constructions. Private categorical helpers descend the identity-open square,
compare the two canonical compact-support presentations, and compute transport through
the counit-compatible adjunction uniqueness isomorphism. The bounded-below antecedent is
exactly the assumed `IH`; its witness is the mapped actual comparison unit.

All existing declaration signatures, public imports and definitions are unchanged.
The node now records the direct calculation. No new nodes or public declarations.
The change record
`coord/changes/closed-identity-open-hom-proof-scope.md` documents the file-local
backward elaboration options and exact-composite instances; there is no mathematical
interface change. The complete module compiled on the server in 46.4 seconds;
the final unused-simp warning was then removed for the delivery checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.closedIdentityOpenHomNormalization`
(node `lem-coef-closed-identity-open-hom-normalization`).

Closed 1 original hole; added 0 holes. No holes are left in the delivered module. The proof uses the existing comparison
and adjunction APIs; this does not assert that their transitive dependencies are sorry-free.

## No longer needed

The direct calculation does not need the planned applications of
`Sheaf.AlgebraicGeometry.ProperIdentityOpenSiteComparison`
(`lem-coef-proper-identity-open-site-comparison`) or
`Sheaf.SixFunctors.RelativeHomChangeOfPresentation`
(`lem-coef-relative-hom-change-of-presentation`). Neither was imported by the original
module, and neither is added. The coefficient-universe transport needed by their
specialized signatures is avoided by calculating with the existing general finite-ring
constructions instead.

Removed proof imports: `Sheaf.Paper.BoundaryExceptionalComparisonData`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`WeilConjectures.AlgebraicGeometry.ProperBasic`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
The last two are already publicly available through the retained statement imports.
The first three provide no constants used by this proof.

Removed direct node dependencies `def-weil-boundary-exceptional-comparison-data`,
`def-weil-pbc-direct-image`, `lem-kun-dimension-finite-type`, and `pqf-lem-proper-basic`.
The direct-image and properness constructions remain available in the retained APIs.
No global withdrawal or claim about the entire targets' import closure is made.
The obsolete dimension and proper-basic tool-use entries are removed in order.

## Where the brief, the DAG or earlier work was wrong

The planned relative-Hom theorem is specialized to a coefficient quotient in Type (u+1),
whereas this item uses ULift of the quotient of a field in Type u. Its asserted formula
is true, but direct expansion of `specifiedExceptionalHomEquiv` and adjunction uniqueness
avoids this presentation transport. The explicit Hom construction also does not need
a geometric dimension bound in this proof.

The two compact-support comparisons use different but compatible D+ inclusion placements.
Their equality is checked by naturality of the right-derived inclusion comparison and
the exact derived composition/isomorphism compatibility equations, not by assuming the
comparison definitions are identical.

The unit `sk-prop-sf-biduality-general` has no realized statement or steps for this node;
its route is unchanged. The current blueprint displayed Hom chain was read from
`literature/blueprint/latest/`. Identity immersions, empty schemes, zero complexes,
and the lowest coefficient level introduce no exceptions: the calculation uses only
naturality, inverse identities and the given bounded-below property of IH.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
