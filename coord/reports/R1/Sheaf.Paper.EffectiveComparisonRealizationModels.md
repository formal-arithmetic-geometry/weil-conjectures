## What changed

Proved `WeilConjectures.effectiveComparisonRealizationModels` by choosing one
completion calculus and Roos model per field and scheme, then assembling the
existing effective quotient descent and constructibility conclusions. All existing
statements and definitions are unchanged.

Added `Sheaf.Paper.EffectiveCompletionPresentationModels`, stating the separate completion
normalization on every simultaneous quotient presentation. It uses the existing
canonical ordinary/derived completion models, the existing normalized comparison
for the identity scheme map, and the strict quotient completion-unit theorem.
The chain map is the actual strict quotient augmentation followed by the Roos map
of the inverse presentation isomorphism. Its two coordinates and its entire derived
localization equality are the retained theorem obligation. The docstring records
the explicit strict augmentation transport and cancellation argument.

The main proof converts intrinsic derived completeness to the legacy unrestricted
predicate through `sfDerivedComplete_iff_legacy`, using an auxiliary finite-field
datum of characteristic different from l. This choice is inside a proof, and no
public definition chooses arbitrary data from an unproved existence statement.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.effectiveComparisonRealizationModels`.

Added one hole, the strictly smaller completion-normalization subresult
`WeilConjectures.effectiveCompletionPresentationModels`
(node `lem-trf-effective-completion-presentation-models`). Its proof is exactly
`by sorry`. The original theorem is proved completely from this result and existing
library declarations. This is a decomposition, not a net hole closure: one hole
closed and one hole added. No hole is inside a definition or private declaration.

The main assembly and complete interface were verified by the project compiler;
the split helper and main module compiled together. The completion lemma remains unproved: its explicit augmentation-transport argument
was developed, but the section-transport and full derived-morphism proof did not
compile within the project limits. Profiling identified repeated canonical
quotient-component conversions. It is retained as a separate mathematical
normalization result, not as a completed proof or a net hole closure. No experimental
dependency changes are retained.

## No longer needed

Removed the following direct proof imports from the item; its proof now uses
`Sheaf.Paper.EffectiveQuotientModelDescent`, the new completion-presentation theorem,
and `Sheaf.Paper.SfDerivedCompleteLegacyComparison`:

- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientExtensionReductionModel`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`
- `Sheaf.Paper.SystemNormalizedTensorClosure`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`

These modules are largely retained transitively through the existing descent
module. No entire module is withdrawn or claimed pruned. In particular the existing
Roos-adjunction and primitive-comparison nodes remain needed by the imported
descent statements; the new completion proof uses the existing canonical
model and proved strict quotient unit interfaces instead of duplicating their proofs.
The unit-level route is preserved. The planned helper proof reuses the existing
private Roos model and tower-map identification. Its new result is transport of both coordinates and the entire
unit equation to every simultaneous presentation; it does not duplicate an
existing theorem.

## Where the brief, the DAG or earlier work was wrong

The existing three-step assembly plan does not directly supply the exact
`completion_normalization` field. The Roos-adjunction node provides the unit formula
on its own ordinary quotient presentation, whereas the field quantifies over every
simultaneous presentation and specifies two section transports. The new separate
helper states exactly this transport. An existing identity-scheme comparison and
the strict quotient unit theorem give a shorter route than reconstructing it from
primitive pullback and scalar comparisons.

The descent unit clause accepts unrestricted legacy completeness; the constructible
subcategory stores intrinsic completeness. The explicit conversion closes this
interface gap.

## New nodes

`lem-trf-effective-completion-presentation-models` records the separate completion
normalization transport, with its sources, strict coordinate argument, and whole
morphism cancellation. The parent node now records the actual assembly and the
intrinsic/legacy completeness conversion. There is no statement or definition
change and therefore no change record.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
