# AlgebraicGeometry.ProEtale.constantModelBoundedConstructible_field_triangulated

## Reason

Restore the missing module assigned by `coord/rework.tsv`. Its archive at
`quarantine/Sheaf/Paper/CoefficientHeartTriangulated.lean` records the full proof
removed after a cluster restore. This is restoration of the complete mathematical
interface and implementation, not withdrawal of its still-needed node.

## Old

The library path `lean/Sheaf/Paper/CoefficientHeartTriangulated.lean` is absent.
The full archived source remains at
`quarantine/Sheaf/Paper/CoefficientHeartTriangulated.lean`; it has zero sorries.
Its theorem is still attached to `det-cor-coefficient-heart-ii-triangulated`.

## New

Restore that archived module verbatim, including the public theorem, both private
proved helpers, both public imports and all three proof imports. No definition,
statement, visibility, attribute or target changes. The existing DAG proof and
Lean attachment already describe this implementation and remain unchanged.

For each coefficient, coefficientHeart_closure supplies kernel, cokernel and
extension closure and an abelian full subcategory. Its zero object gives
constructible zero. The well-definedness theorem gives isomorphism closure.
The weak-Serre cohomology theorem gives triangulation, intersected with canonical
boundedness. A retract is a kernel of the complementary idempotent; applying
homology and descending the original cohomological bounds gives thickness.
The proof covers rank zero and the empty scheme without additional hypotheses.

The restored source compiled cleanly through lcompile.py in 5.2 seconds.

## Users

`tools/downstream.py --allow-missing --uses` reports zero live downstream modules.
Searching both `lean/` and `quarantine/` finds the three archived direct importers
below; two apply the theorem. All retain exactly the archived interface, including
coefficient ring objects and the order of the returned conjunctions. No consumer
adaptation is necessary. The archives and their DAG dependencies are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientHeartTriangulated | B2, assigned restoration | Restore complete source with zero holes. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed in shared snapshot; quarantined | Existing finite-field and algebraic-closure applications unchanged. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed in shared snapshot; quarantined | Existing applications to X and Z unchanged. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed in shared snapshot; quarantined | Existing proof import restored; no direct application found. |

## Status

landed 20261021T023255-L-2943400 2026-10-21 (merge of deliver/B2/Sheaf.Paper.CoefficientHeartTriangulated)
