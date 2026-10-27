## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.SpTowerShriek.tower_ordinary_localization`
with a proof from the source library's proved finite-coefficient open-closed sequence,
transport through the intrinsic module-sheaf equivalences, and reflection by the exact
jointly faithful evaluation functors. Private proved helpers establish transport of short
exact sequences, compatibility of adjoint-uniqueness comparisons with the unit/counit,
conjugation of the finite sequence, and joint faithfulness of evaluation.

The new proof-only imports are `Sheaf.Paper.SmoothPurityTowerOrdinaryUnitEvaluation`,
`WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence`, and
`WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact`. Existing public
imports and the assigned theorem's signature are unchanged. No source-library file,
definition, target, or consumer is changed. Updated the assigned node's proof route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpTowerShriek.tower_ordinary_localization` (one of one).
There is no remaining sorry in the assigned module.

Added one hole, in
`AlgebraicGeometry.ProEtale.SpTowerShriek.geometry_unit_evaluation`, node
`lem-sp-tower-ordinary-unit-evaluation`, new module
`Sheaf.Paper.SmoothPurityTowerOrdinaryUnitEvaluation`.
This is a decomposition, not a net reduction in the hole count: one closed, one added.
The new obligation is only the ordinary unit evaluation equation for an arbitrary
scheme morphism and a single level. It asserts none of localization, monicity,
epicity, exactness, or preservation of colimits. All finite localization, counit
transport and exactness reflection arguments combining this equation are proved in
Lean in the assigned module. This does not rename or repackage the localization
statement.

Validation: both delivered modules compile through `lcompile.py`. The final assigned
module compile is clean in 15.2 seconds; the new statement module compiled in
46.8 seconds. All added imports pass `tools/import_direction.py may`. The original
theorem signature and statement metadata are unchanged, and Lean line widths are
at most 100 characters.

The docstring records its source, coordinate-identification argument, and checks at
index zero, the zero system and empty schemes. The parent argument also covers an
empty open or closed complementary part by the same source sequence.

## No longer needed

The assigned file originally had no proof-only dependency imports, so none of its
existing imports was removed.

The proof no longer needs node `lem-sp-semilinear-open-closed-complex-sequence` or
module `Sheaf.Paper.SemilinearOpenClosedComplexSequence`: it obtains ordinary
short exactness directly at each finite coefficient level and reflects it on
systems. In particular this proof does not request the sequence-site coefficient
construction, slice-site presentation, arbitrary-ring scalar-compatibility,
closed-system presentation, or passage to complexes from that branch. Specifically,
it does not use these modules or their nodes:

- `Sheaf.Paper.SequenceOpenCoefficientConstruction`
  (`lem-pur-sequence-open-coefficients`);
- `Sheaf.Paper.SequenceOpenOrdinary` (`lem-pur-sequence-open-ordinary`);
- `Sheaf.Paper.SemilinearClosedSystemPresentation`
  (`lem-sp-semilinear-closed-system-presentation`);
- `Sheaf.Paper.SemilinearOrdinaryLocalizationSequence`
  (`lem-sp-semilinear-ordinary-localization`);
- `Sheaf.Paper.SemilinearLocalizationScalarCompatibility`
  (`lem-sp-semilinear-localization-scalar-compatibility`).

Node `lem-coef-semilinear-derived-sections` is no longer a direct proof dependency
of the assigned theorem. It remains a dependency of the new unit-normalization
node, through its generic ordinary_unit_evaluation field; it is not globally pruned.
No declaration or module is withdrawn. Other consumers may still need the unused
complex-sequence branch.

## Where the brief, the DAG or earlier work was wrong

The original route constructs an arbitrary-ring sequence of complexes and then
evaluates a degree-zero complex. That is unnecessary here: the proved source
finite-coefficient sequence already has the required ordinary maps after
conjugation by the canonical realization equivalences. Its closed-pushforward
finite-colimit theorem applies to the hypotheses of the assigned statement,
without adding qcqs assumptions on the ambient scheme.

The remaining implementation difficulty is the dependent coordinate transport of
`Geometry.generic.ordinary_unit_evaluation` through the heterogeneous normalization
fields of `Geometry`. A naive elimination of the large records is too costly and
does not directly normalize all level functors. It is isolated as the specific
map equality that the completed localization argument needs. No mathematical
counterexample or disputed statement was found.

## New nodes

`lem-sp-tower-ordinary-unit-evaluation` isolates the generic-to-fixed-coordinate
ordinary unit equation from the original node's second proof step. Its statement
is independent of complementary immersions and of exactness. It is sourced to the
blueprint operations proof (2), with proof dependencies on the actual Geometry
interface and generic ordinary-unit equation. The parent DAG now cites this
normalization step, the source open-closed finite sequence, and exactness of the
source closed direct image. The ordinary normalized pullback comparison from `lem-trf-open-square-exchange`
is used only to identify adjoints; its derived square-exchange assertions are not
used. The unit route is preserved. No change record is
needed because no existing statement or definition is changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
