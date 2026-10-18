# AlgebraicGeometry.finite_spec_residueFieldMap

## Reason

The return of A2's delivery at 68674e8b6 identified a word-for-word duplicate private helper.
Reuse the existing theorem in IntegralClosureDedekindSurjectiveFibres. It must be exported
from its original module so the assigned item can import and apply it. This module is
unclaimed. Only `private` is removed; the theorem's binders, type and proof stay identical.
No data, definition, target signature or target meaning changes.

## Old

In namespace `AlgebraicGeometry`, in the exposed public section:

```lean
private theorem finite_spec_residueFieldMap {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (x : PrimeSpectrum S)
    (h : (Ideal.ResidueField.map (x.comap φ.hom).asIdeal x.asIdeal φ.hom rfl).Finite) :
    ((Spec.map φ).residueFieldMap x).hom.Finite
```

## New

In the same namespace and exposed public section:

```lean
theorem finite_spec_residueFieldMap {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (x : PrimeSpectrum S)
    (h : (Ideal.ResidueField.map (x.comap φ.hom).asIdeal x.asIdeal φ.hom rfl).Finite) :
    ((Spec.map φ).residueFieldMap x).hom.Finite
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
--uses finite_spec_residueFieldMap` found the following 18 downstream modules, and the
original module's own use. No downstream module names the previously private helper.
The sole direct importer is SemilocalNormalizationDimOne. Exporting a non-instance theorem
with no attributes changes no definitions or existing statements. No downstream edits are
needed. Claim holders below are recorded at repair time; these consumers are not adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres | unclaimed | Export existing helper; its internal call uses the same proof. |
| Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected | A2 | Remove duplicate; import original module and apply exported theorem. |
| Sheaf.AlgebraicGeometry.AffineComplementReciprocalCover | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | H5 | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion | U9 | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | U2 | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep | S8 | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.FindGloballyGenerated | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram | Q5 | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.IntegralDimOneAmple | unclaimed | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | D9 | No signature, definition or proof change needed. |
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductor | unclaimed | No signature, definition or proof change needed. |
| Sheaf.RingTheory.JacobsonDenominatorFunctionField | unclaimed | No signature, definition or proof change needed. |
| Sheaf.RingTheory.SemilocalNormalizationDimOne | unclaimed | No signature, definition or proof change needed. |

The original helper had no public callers. In particular, no target's statement depends
on this visibility addition. Both changed modules compile together (5.1 and 3.8 seconds). The unchanged direct importer
SemilocalNormalizationDimOne compiled separately against the exported helper (2.6 seconds).
All three compiles had no diagnostics. The temporary consumer copy was removed afterward.

## Status

landed 20261018T071131-L-1662401 2026-10-18 (merge of deliver/A2/Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected)
