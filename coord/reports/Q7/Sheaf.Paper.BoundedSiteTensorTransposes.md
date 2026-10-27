## What changed

Filled the two remaining theorem bodies in
`Sheaf.Paper.BoundedSiteTensorTransposes`, retaining every existing declaration
signature and all five arrow constructions. The proof uses the already proved
compactification projection square, the bounded transpose calculation, and
naturality of the tensor, comparison and adjunction counits. The reversed equation
uses the proved symmetry of the specified derived braiding, including its signs.
The dualizing equation follows by transporting the actual exceptional counit and
moving the dualizing-factor map through projection naturality. A small private
categorical triangle lemma keeps rewriting away from the large concrete
compact-support comparison definition. Proof elaboration respects transparency;
the original broad transparency-disabling options are no longer used. Local
irreducibility attributes for the large derived functor, braiding and compact-support
comparison keep the proof calculations at their API level; these are scoped to
this file and change no exported attribute or definition. Generic private isomorphism-cancellation and transpose-transport lemmas handle
the reverse source identification without rewriting through concrete braiding
or compact-support definitions. All proof helpers
are ordinary proved lemmas; no custom elaborator is delivered.

Added `Sheaf.Paper.SiteTensorUnitEvaluation` for the remaining ordinary tensor/unit
comparison step. It involves only the comparison pullback, arbitrary Q and K,
and an evaluation Q to the coefficient unit; it contains no exceptional functor,
compact support, projection map, or adjunction transpose. Updated the item's DAG
proof and added its node. No source-library module is changed. The initial proof compiled in 49.5 seconds;
the first delivery compile passed the proofs but exceeded the runtime gate at
63 seconds, so nothing was pushed. The final packet uses a generic cancellation
lemma to avoid expensive conversions in the reverse comparison. The new
unit-evaluation statement compiled in 35.1 seconds during the delivery check.

## Proved and sorry left

Original holes: 2. Closed bodies:
`AlgebraicGeometry.ProEtale.boundedSiteTensorTransposes` and
`AlgebraicGeometry.ProEtale.boundedSiteTensorTransposes_dualizing`.
The existing proof of `boundedSiteTensorTransposes_natural` is retained.

Added one hole:
`AlgebraicGeometry.ProEtale.siteTensorUnitEvaluation`, node
`lem-pur-site-tensor-unit-evaluation`. No holes remain in the assigned module.
This is a reduction of two tensor-transpose holes to one strictly smaller ordinary
monoidal compatibility statement; it does not claim an axiom-free proof of those
two theorems. Net hole reduction in this packet: one. All private helpers are proved;
no definition has a hole.

The new step was checked on zero inputs, zero evaluation, the zero ring, identity
comparison and odd shifts. The pure-tensor unitor calculation respects the existing
Koszul convention, and no projection is inverted in the new step.

## No longer needed

Removed these unused direct public imports:

- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`;
- `Sheaf.Paper.CompactSupportSiteCoherence`;
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`;
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`;
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`;
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`;
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.

Canonical compact support and etale compact support are still available through
the retained statement imports. Removing their redundant direct imports does not
claim their nodes are mathematically unnecessary. The unused general co-smoothness,
ringed comparison, supplied exchange-data and exceptional coefficient systems are
not used in this proof; other consumers may still need them.

The proof does not invoke `lem-sfb-ringed-derived-monoidal-comparisons`: its
`SheafOfModules` presentation does not identify the concrete tensor and unit maps
of the ordinary sheaf-category encoding used here. The smaller concrete unit step
is recorded separately. Nor does it invoke `thm-weil-pbc-site-comparison`: the
proved defining Hom-chain calculation suffices, without using invertibility of
the comparison unit. No unit realization is bypassed; the item's unit
`sk-thm-smooth-purity` has an empty `realized` list, and its existing ancestry is
preserved. Removed obsolete tool approvals for `lem-sfb-ringed-derived-monoidal-comparisons`
and `thm-weil-pbc-site-comparison` from the item node; retained the existing
projection-comparison approval. No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The planned generic symmetric-monoidal comparison is expressed for a different
module-sheaf encoding. It cannot directly supply the equality for the specified
`leftDerivedTensorComparison` and `mapDerivedCategoryComparisonUpperStarUnitIso`
without identifying their normalizations. The source module
`MapDerivedCategoryMonoidal` does package an oplax monoidal structure whose tensor
map is the transported derived tensor comparison, but its unit map is not identified
there with this item's separately defined coefficient-unit isomorphism. This offers
a shorter generic approach to the remaining unit step; it does not close it by a
plain application. The new step states precisely that
missing compatibility, with its K-flat-model argument. The existing projection
module already proves a more general forward square than its public finite-level
theorem advertises; using that proved helper avoids coefficient transport and
extra dimension hypotheses.

## New nodes

`lem-pur-site-tensor-unit-evaluation`, module
`Sheaf.Paper.SiteTensorUnitEvaluation`: Step 2 of the existing node, restricted to
ordinary tensor evaluation into the unit. Its docstring supplies the K-flat
pure-tensor proof, sourced to Stacks Tag 07A4 and tensor-pullback compatibility.
This is a genuine proper step of the argument, independent of all exceptional
and projection data in the item.

Change record: `coord/changes/Q7-bounded-site-tensor-imports.md`.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
