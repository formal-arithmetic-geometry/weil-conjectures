## What changed

Proved `AlgebraicGeometry.ProEtale.proEtaleDirectImageScalarCocycle` with its exact existing
signature. Added three proved private helpers in the item module: `scalarPullbackMate`
identifies the inverse specified pullback comparison with its restriction mate;
`scalarPullbackCocycle` obtains coefficient coherence by taking scalar mates; and
`scalarMateCocycle` proves the general passage from pullback coherence to direct-image
coherence by the counit formula and naturality. The existing public imports are retained.

The proof privately imports `ProEtaleOpenScalarCocycle` with `import all` to reuse its
proved `coefficientRightSquare` and `derivedCoefficientComp`. These helpers are stated
for arbitrary scheme morphisms, without an open-immersion hypothesis. The open cocycle
theorem itself is not applied. `OrdinaryRestrictionPullbackSquare` supplies the proved
private categorical `mateSquare` helper. `ScalarAssociatorConjugate` identifies the
prescribed balanced associator, and Mathlib's mates API supplies pasting and transposition.
The DAG proof and proof dependencies now record this shorter argument. No definition,
public declaration signature, or importer-visible import was changed.

The unit route is preserved: this proves exactly the coefficient-composition assertion
needed by Step 4 of the direct-image comparison proof. The proof works for the zero
object, zero coefficient rings, identity maps, empty schemes, and nonflat coefficient
towers, because all intermediate identities concern the full unbounded categories and
only use the actual adjunctions and normalized scalar associators.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.proEtaleDirectImageScalarCocycle`
(node `lem-sp-proetale-direct-image-scalar-cocycle`).

The complete proof compiled through `lcompile.py` in 42.4 seconds. The sole unused-simp
warning was removed before delivery; the delivery tool performs the final compile and
axiom checks.

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivery. All three new
private helpers are proved. This is a proof, not a decomposition into new holes.

## No longer needed

Removed the following private imports from this module:

- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.Paper.RingedCoefficientProjectionCocycle`
- `Mathlib.CategoryTheory.Adjunction.Basic` (replaced by the actually used mates API).

This proof no longer needs the planned nodes
`lem-sp-proetale-coefficient-tower-normalization`,
`lem-sp-proetale-projection-mate-identification`, or
`lem-pur-ringed-coefficient-projection-cocycle`, and does not import the first two modules.
The specified constant-coefficient operations already define their pullback comparisons
as scalar mates, so the literal inverse-image coefficient presentation and its transport
are unnecessary here. A direct categorical counit calculation proves the mate cocycle.

Removed the old top-level `tool_uses` entries for
`lem-pur-proetale-constant-coefficient-comparison`, `lem-pc-kflat-resolution`,
`lem-sfb-successive-derived-quotient-normalization`, and
`lem-pur-ringed-coefficient-projection-cocycle`. The scalar normalization theory can
remain a transitive dependency of the already proved scalar-associator theorem; it is
not separately invoked by this proof. No existing module or declaration is withdrawn,
and no claim is made that these nodes have become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The item docstring predated the current two-normalization-node DAG split. Both planned
routes required substantially more transport data than the actual definitions need.
The already proved coefficient square calculation in the open-cocycle module is more
general than that module's headline theorem: its absence of an open-immersion hypothesis
allows its reuse here. The revised docstring and DAG follow the implemented proof.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
