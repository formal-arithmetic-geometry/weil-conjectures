## What changed

Proved `WeilConjectures.PurStrictScalar.scalarRoosNormalization` in
`Sheaf.Paper.CompactSupportScalarLimitReduction`, preserving its statement.
The proof uses the existing cofinality theorem for the quasi-isomorphism and
selection/block coordinates. Coordinate uniqueness identifies its chosen map
with the cofinality construction. The canonical comparison between the limit
of tower complexes and the degreewise limit commutes with arithmetic
restriction; a private helper proves this by the limit projections.

The derived comparison equation is proved on K-injective complexes by
cancelling the Roos inclusion, whose image is invertible by the existing
unit-normalized Roos comparison. The cochain formula for
`Functor.rightDerivedPullback` supplies the required equation for the actual
derived restriction. Naturality along a K-injective resolution extends it to
every complex. The final coordinate calculation proves the augmentation
identity, including its zero shifted-product coordinate.

Added the fully proved module `Sheaf.CategoryTheory.RoosArithmeticNormalization`
and a proof-only import of it in the item. Its single public theorem gives the
derived restriction equation and strict augmentation formula over an abstract
abelian category. Three private helpers prove the underlying calculations. The
new module uses proof-only `import all` to access the already proved cofinality
construction. Scoped `implicit_reducible` attributes expose the complex/functor
wrappers needed for implicit arguments.

The first implementation over the concrete sheaf category took 87 seconds.
Abstracting and extracting the calculation reduced the cost, but the parent
still reached the 60-second gate during final delivery. Moved the existing
`WeilConjectures.PurStrictScalar.scalarRoosComparison_existsUnique` theorem to
`Sheaf.Paper.ScalarRoosComparisonUnique`; its statement and proof are byte for
byte unchanged. The parent publicly imports that provider, preserving the exact
public declaration and its visibility. Three proof imports used only by that
theorem move to the provider. The original elaboration settings are retained
for the moved proof. No existing definition body, public signature, or other
existing module is edited. All profiling options are removed.

Updated Steps 3–4, proof dependencies, proof origin, and the declaration list of
`lem-pur-compact-support-scalar-limit-reduction`, and attached the moved theorem
to its own node. The unit route is preserved. The public import introduces only
the same theorem and the already imported foundation interface.

Validation: `lcompile.py --all` accepted all three packet modules and all ten
unchanged direct importers, without errors or warnings. The importer copies were
verified unchanged and removed after the check. The checked importers were:

- `Sheaf.Paper.ConstantCompletedOrdinaryAssociativity`.
- `Sheaf.Paper.CompletedScalarExactLocalization`.
- `Sheaf.Paper.ScalarLimitTensorComposition`.
- `Sheaf.Paper.ConstantCompletedScalarAssociativity`.
- `Sheaf.Paper.CompactSupportStrictScalarRefinement`.
- `Sheaf.Paper.CompactSupportScalarShiftStructures`.
- `Sheaf.Paper.CompactSupportScalarProjectionIdentification`.
- `Sheaf.Paper.CompactSupportStrictScalarComposition`.
- `Sheaf.Paper.ScalarRefinementOriginsF`.
- `Sheaf.Paper.ScalarLimitTensorRestriction`.

## Proved and sorry left

Closed 1 of the item's 3 original holes:
`WeilConjectures.PurStrictScalar.scalarRoosNormalization`.
Added 0 holes; split off 0 unproved statements.

The two unchanged holes in this item, both attached to
`lem-pur-compact-support-scalar-limit-reduction`, are:

- `WeilConjectures.PurStrictScalar.scalarRoosTensorNormalization`.
- `WeilConjectures.PurStrictScalar.compactSupportScalarLimitReduction`.

The unchanged foundation module also retains
`WeilConjectures.PurStrictScalar.scalarLimitTensor_exact` and
`WeilConjectures.PurStrictScalar.scalarLimitRestriction_exact`, attached to
`def-pur-compact-support-scalar-limit-maps`; this delivery does not edit that
module. All three private helpers and the public theorem in the arithmetic
normalization module are fully proved. Both new modules have zero holes.

## No longer needed

Removed these proof-only imports from the parent because the moved comparison
proof uses them in `Sheaf.Paper.ScalarRoosComparisonUnique`:

- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison` (`import all`).
- `Sheaf.CategoryTheory.StrictRoosDerivation`.
- `Sheaf.CategoryTheory.DerivedExactSquareCoherence` (`import all`).

No node or module is pruned: all three dependencies remain used by the extracted
proof. The two remaining theorem holes retain their stated route and dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The already proved internals of
`compactSupportRoosCofinality` provide the coordinate uniqueness, naturality,
and ordinary kernel-inclusion square needed for normalization. The remaining
step is the canonical derived-unit calculation; no additional mathematical
lemma with an unproved body is needed. Identity restriction, arbitrary
positive ramification indices, the zero complex, and every strict augmentation
are included without extra hypotheses.

## New nodes

`lem-pur-roos-arithmetic-normalization`, in
`dag/nodes/sec-smooth-purity/lem-pur-roos-arithmetic-normalization.json`, records
`CategoryTheory.roosArithmeticNormalization` in
`Sheaf.CategoryTheory.RoosArithmeticNormalization`. It is a fully proved,
category-independent part of the original cofinal normalization argument,
with the explicit K-injective unit calculation and strict augmentation formula.
It adds no unproved statement. No change record is needed: existing statements
and definitions are unchanged.

`lem-pur-scalar-roos-comparison-unique`, in
`dag/nodes/sec-smooth-purity/lem-pur-scalar-roos-comparison-unique.json`, reattaches
the already proved `WeilConjectures.PurStrictScalar.scalarRoosComparison_existsUnique`
to `Sheaf.Paper.ScalarRoosComparisonUnique`. It records the existing universal
right-derived-functor uniqueness argument, moved verbatim to reduce the parent
runtime. This module also has zero holes. No existing declaration is deleted or
renamed, and the parent continues to expose it by a public import.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
