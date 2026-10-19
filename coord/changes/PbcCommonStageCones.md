# Sheaf.Paper.PbcCommonStageCones

## Reason

The proof replaces two proof-only imports and adds private helper declarations
needed to identify the concrete tensor-Hom localization with the existing
Verdier rationalization. The delivery therefore changes the module's visible
command environment and must carry the stage-3 change record required by the
preflight checker. Public declarations and their signatures are unchanged.

## Old

The module imported `Sheaf.CategoryTheory.ScalarLocalizationTriangulated` and
`Mathlib.CategoryTheory.Triangulated.Triangulated`, and its public existence
theorem had proof `by sorry`.

## New

The module imports `WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`
and `Mathlib.CategoryTheory.Localization.Triangulated` privately. It adds the
private proved helpers `stageRationalComparison`, `stageLocalization`, and
`stagePretriangulated_ext`, and proves
`AlgebraicGeometry.Scheme.qbarStagePretriangulated_exists` using Mathlib's
localization pretriangulation with the published PBC shift. The public instance
and abbreviation remain unchanged.

## Users

The current `tools/downstream.py Sheaf.Paper.PbcCommonStageCones --direct`
lists ten direct consumers: `Sheaf.Paper.CurveMiddleExtension`,
`Sheaf.Paper.DlConstantFieldCharts`, `Sheaf.Paper.FieldShriekLowerBound`,
`Sheaf.Paper.PbcConeIndependence`, `Sheaf.Paper.PbcDescentFunctors`,
`Sheaf.Paper.PbcDistinguishedDiagramLifting`, `Sheaf.Paper.PbcQbarCategory`,
`Sheaf.Paper.PbcVerdierAxioms`, `Sheaf.Paper.QbarOrdinaryAdjunction`, and
`Sheaf.Paper.RationalCoefficientCategoryComparison`.
None needs adaptation: all existing public signatures, the chosen-instance
definition, the distinguished predicate, and public imports are unchanged.
The transitive `--uses qbarStagePretriangulated_exists` check finds only the
item's own chosen-instance definition. The added helpers and proof imports
are private; no consumer statement changes its meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcCommonStageCones | M9 | Adds private proof helpers and closes the theorem proof. |
| Sheaf.Paper.CurveMiddleExtension | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcConeIndependence | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcDescentFunctors | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcQbarCategory | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PbcVerdierAxioms | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarOrdinaryAdjunction | Not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | Not adapted | Unchanged public interface; no adaptation. |

## Status

landed 20261019T005348-L-2757727 2026-10-19 (merge of deliver/M9/Sheaf.Paper.PbcCommonStageCones)
