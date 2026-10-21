## What changed

Proved `AlgebraicGeometry.Scheme.cbcCompletedOpenFiniteEtaleOrigins` with its original
signature. Added only proved private helpers in its module and private proof imports.
The proof identifies finite reduction as a left adjoint to finite scalar restriction,
then obtains reduction/open-extension compatibility from the existing
`cbcFiniteOpenRestriction` by uniqueness of left adjoints. It transports the published
origin realization to `StrictTower.HD`, applies `hJ` to the retained bounded-below etale
antecedent, and composes the resulting isomorphisms. Updated the item's DAG proof to
this route. No other module, public definition, or target statement changes. The conservative
preflight scope-change flag is documented in
`coord/changes/c9-completed-open-origin-proof-scopes.md`; the private exactness
theorems are registered only as local instances.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.cbcCompletedOpenFiniteEtaleOrigins`
(node `lem-cbc-completed-open-finite-etale-origins`).
The delivered module has zero `sorry`; zero holes are added or split off.
Existing dependency declarations are used as stated. This is a proof from those
interfaces, not a claim that all their transitive proof obligations are closed.

## No longer needed

The original file had no proof-only imports to remove. The revised proof does not
use the original node's direct proof dependencies
`lem-cbc-ringed-open-strict-reduction` (`Sheaf.Paper.RingedOpenStrictReduction`),
`lem-pc-kflat-resolution` (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`),
`lem-cbc-ringed-open-flat-resolution` (`Sheaf.Algebra.Homology.RingedOpenFlatResolution`),
`lem-pur-derived-change-of-rings` (`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`), or
`lem-cbc-proetale-extension-zero-comparison`
(`Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`).
The first four are replaced here by the finite-coordinate right-adjoint comparison;
the last is replaced here by the existing finite constant transport's `hJ`.
These are local dependency removals only: other modules and the retained public
imports may still need those nodes. No module is withdrawn and no global pruning
is claimed. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original K-flat argument is a valid plan but unnecessary for this obligation:
only an isomorphism is requested, so the existing comparison of right adjoints
supplies the required isomorphism of left adjoints. The finite constant transport
already contains the bounded-below etale/pro-etale open comparison. The proof uses
these declarations without adding a common lower bound, completeness,
constructibility, or quasi-compactness hypothesis. The final standalone compile passed
without errors or warnings in 7.1 seconds. Empty opens and zero quotient
rings are covered by the same functorial constructions.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
