# CartanEilenbergGoodCutIdentification imports

## Reason

`PlusSingle` supplies `homologyFunctorObjQIso` and its naturality theorem only
inside proofs. Make that import private and import the bounded-below derived
category interface used by the signatures directly and publicly. Also replace
the retired Sheaf truncation-step re-export with the upstream module owning
the private cycles-naturality helper, and remove the redundant direct
`HomologicalComplexLimits` proof import.

No declaration signature, visibility, definition, instance, or attribute changes.
The new proof closes `GoodCutIdentification.cut_columns` without new holes.
No target meaning changes or definition-based target review is needed.

## Old

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import all Sheaf.Algebra.Homology.UpperTruncationStepSES
import Mathlib.Algebra.Homology.HomologicalComplexLimits
```

## New

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import all WeilConjectures.Algebra.Homology.UpperTruncationStepSES
```

Other imports are unchanged. The private `HomologicalComplexLimits` import is
removed without replacement.

## Users

Ran the source-only command
`python3 tools/downstream.py Sheaf.CategoryTheory.CartanEilenbergGoodCutIdentification --uses homologyFunctorObjQIso`
in the read-only shared repository. It lists the following twelve downstream
modules. None has a claim in that repository's `coord/claims` snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageInjectiveModel | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageTruncationDiagram | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergHorizontalCutComparison | unclaimed | Sole direct importer; already publicly imports PlusSingle itself; no adaptation. |
| Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.CategoryTheory.GrothendieckSpectralSequence | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.Paper.ExtSheafToGlobalSpectralSequence | unclaimed | Unchanged interface through the direct importer; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged interface through the direct importer; no adaptation. |

The sole direct importer imports this item privately and independently publicly
imports `PlusSingle` on line 10. Its full original source was read. Therefore it
retains the same declarations and instances, both for itself and for every
transitive user listed above. Its statement and proof are not changed or
included in the delivery. Scratch compilation checks it against the corrected
item, compiled first in the same scratch overlay.

## Status

landed 20261017T040220-L-2369152 2026-10-17 (merge of deliver/J1/Sheaf.CategoryTheory.CartanEilenbergGoodCutIdentification)
