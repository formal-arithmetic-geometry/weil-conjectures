## What changed

Prove `AlgebraicGeometry.ProEtale.CondensedRing.coefficient_ringed_square_normalization`
in `Sheaf.Paper.CoefficientRingedSquareNormalization`, preserving its entire signature
and all four public constructions. Proved private helpers compare the two canonical
exact-postcomposition right-derived isomorphisms by their universal units, normalize
resolution coordinates, and evaluate composition units. The direct-image equality
then follows by reversing the factors of the specified comparison; the pullback equality
follows from the inverse-component formula for conjugate isomorphisms. The representative
formula for `e` follows from the universal derived bridge equation and both composition
unit equations. Taking its inverse gives the representative formula for `C`.

The node's proof, proof dependencies, and proof origin now follow this direct
internal-coordinate argument. Change record: `coord/changes/C9-coefficient-ringed-normalization-private-proof.md`
documents the scoped private-helper commands flagged by preflight.
All public imports are preserved. No definitions,
statements, consumers, or source-library files are changed. Edge cases (identity
coefficient map, identity scheme morphism, zero complexes, zero coefficient ring)
are covered by the same categorical identities; no nonzero or geometric hypothesis
is used in the proof.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.coefficient_ringed_square_normalization`
(node `lem-sfb-coefficient-ringed-square-normalization`).
Added 0 holes, split off 0 statements, and left 0 holes in the delivered module.
All private helpers are proved. No new axioms or choices of unproved data.
The complete delivered file compiled cleanly through `lcompile.py` in 33.5 seconds.
The earlier packet timed out at 60 seconds. The proof now respects transparency in
the concrete theorem, uses a single associativity simplification in the abstract
bridge calculation, and unfolds the existing pullback comparison instead of
re-elaborating the two full derived composite adjunctions. The public constructions
are unchanged, and no compile limit was raised.

## No longer needed

Removed five private proof imports:

- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
- `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`
- `Sheaf.Paper.RingedComparisonTensorAdjunction`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`

The proof does not need the following planned proof dependencies:
`lem-pd-module-ringed-topos-derived-comparison`,
`lem-sfb-internal-section-scalar-adjunction`,
`lem-sfb-coefficient-scalar-tensor-realization`,
`def-weil-pbc-ringed-topos-morphism`,
`prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-sfb-ringed-comparison-tensor-adjunction`.
These generic section/ringed transport results are unnecessary here because the
four existing constructions already express the specified paths in internal coordinates.
The source-library composition/derived-unit APIs provide the required comparison directly.
No resolution-existence argument or extension from representatives is needed to prove
an equality already characterized by universal units. The five removed imports have
the corresponding module names above; `Sheaf.Paper.CoefficientScalarTensorRealization`
was a planned dependency but was never imported by the original item. No claim is
made that these modules are unused elsewhere in the library. No modules are withdrawn.

Obsolete approvals removed from the node's `tool_uses`:
`lem-pd-module-ringed-topos-derived-comparison`,
`lem-sfb-internal-section-scalar-adjunction`,
`prop-pur-kinjective-resolutions-exist`,
`lem-sfb-ringed-comparison-tensor-adjunction`.
The exact-factorization and K-injective-preservation dependencies remain.
The proper-base-change unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's section-module transport and arbitrary-resolution computations are longer
than needed for the current internal-coordinate definitions. The two exact
postcomposition constructions are not definitionally identical: their agreement
requires uniqueness of right derived functors and the compatibility equation for
the exact functor's derived unit. The proof supplies this compatibility explicitly.
The representative calculation does not assume that geometric pushforward preserves
K-injective complexes. No false statement or definition repair was necessary. The file has no previous
repair/quarantine row or current return entry; the dispatched item was the one-hole
live source module.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
