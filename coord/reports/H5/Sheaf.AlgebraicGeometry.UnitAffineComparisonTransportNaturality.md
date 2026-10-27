## What changed

Filled `AlgebraicGeometry.Scheme.Modules.unitAffineComparison_canonical_naturality`
in `Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportNaturality` without changing
its statement. Added a private proof import of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`,
`Sheaf.AlgebraicGeometry.TensorCompositeCohomologyRestriction`, and an explicit
private import of the changed `AffineCohomologyComparisonData` interface.

The private helpers identify the two normalized tensor adjunction interfaces,
compare their composition isomorphisms, prove the structural-unit coefficient
triangle, and apply source and target naturality of module cohomology. The two
pullback projections identify the scheme maps in the symmetry square. Finally,
the supplied naturality of the affine linear equivalences and evaluation on global
sections give the required restriction equation. A private explicit additive
isomorphism identifies scalar-restricted cohomology with its underlying group;
a private cohomology-map constructor fixes the endpoints before
specializing to fibre products. A chart evaluation wrapper fixes both section-group
endpoints on the chart scheme as presented by its identity functor. These are real
constructions with complete proofs and avoid expensive implicit conversions. Private
pointwise function views of the symmetry, coefficient map and linear-equivalence
family keep the underlying cohomology types fixed. Unpacking the
étale charts and arrow records and eliminating their morphism equality allows the
component equations to compose without unfolding the coefficient sheaves. This
follows the existing node's proof plan.

Factored the formula for `affineRealizationRestriction` in the unclaimed
`Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData` through the new constructed
`Sheaf.AlgebraicGeometry.TensorCompositeCohomologyRestriction`, publicly imported
by the definition module. The new construction uses arbitrary schemes and coefficient
modules and exposes its proved defining equation. A named, proved coefficient-object
equality and the explicit fibre-product schemes avoid expensive kernel conversion
after specialization to the structural unit. The signature and canonical map are
preserved. No existing public import is removed. The change record
`coord/changes/H5-affine-restriction-schemes.md` includes the verbatim old/new definitions
and all six consumers with current holders. No consumer adaptation was required.

Validation: the final assigned module compiles without diagnostics in 41.3 seconds
using `lcompile.py`. The generic construction and refactored definition module also
passed their server single-file checks. The theorem signature was compared verbatim
with the current repository source. All three delivered Lean modules have zero holes,
and no temporary probe module or diagnostic setting is included.

Searches used LeanFinder for naturality of structural-sheaf cohomology under
pullback symmetry, Loogle for left-adjoint uniqueness and the unit, the project
search service for tensor-section composition/unit equations, and ripgrep in the
source library and Mathlib. Existing private normalization calculations in
`TwoTermDeterminantPullbackCoherence` and `TensorSingleBaseChangePasting` supplied
the adjunction comparison proof method.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.unitAffineComparison_canonical_naturality`
(node `new-unit-affine-comparison-canonical-naturality`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
The changed definition module and the new generic construction contain no holes.
Holes added there: 0. The existing imported dependencies retain their own proof status.

## No longer needed

None. No existing imports are removed and all three planned proof dependencies
remain used: `def-pc-module-pullback`,
`lem-weil-pbc-module-pullback-structure-sheaf`, and
`lem-weil-pbc-module-cohomology-fmap-functorial`. No nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The restriction's inferred
comma-category schemes and inline coefficient equality caused kernel conversion
timeouts. Naming the schemes alone was insufficient. Its existing formula is now
constructed for arbitrary coefficient modules, using a named equality proof, then
specialized to the affine chart. The defining equation is proved without a hole.
The target statement and the unit route are unchanged.

## New nodes

`def-tensor-composite-cohomology-restriction` attaches the new generic construction,
its coefficient-object equality theorem and its defining-equation theorem. All three
are complete. The map is the existing module-cohomology map of the adjunct of the
normalized tensor-composition coefficient morphism; no new choice is made.
Change record: `coord/changes/H5-affine-restriction-schemes.md`.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
