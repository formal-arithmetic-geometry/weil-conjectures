# AlgebraicGeometry.Etale.singleProjectionIso

## Reason

Repair return 4c020aa80: the item added a private theorem whose statement was
identical to two existing private library helpers. Neither helper was available
through an ordinary import. Make the existing Sheaf helper public and use it
from the item, removing the duplicate entirely. Its module is unclaimed.
The adopted source-library helper and all adopted source files are unchanged.

## Old

```lean
private theorem singleProjectionIso {D : Type*} [Category D] [HasZeroMorphisms D]
    {I : Type*} (G : I → D) [HasProduct G] (i : I)
    (h : ∀ j, j ≠ i → IsZero (G j)) : IsIso (Pi.π G i)
```

## New

```lean
theorem singleProjectionIso {D : Type*} [Category D] [HasZeroMorphisms D]
    {I : Type*} (G : I → D) [HasProduct G] (i : I)
    (h : ∀ j, j ≠ i → IsZero (G j)) : IsIso (Pi.π G i)
```

## Users

`tools/downstream.py ... --uses AlgebraicGeometry.Etale.singleProjectionIso`
found only the defining module as a textual user. The four existing downstream
modules below do not refer to the private helper. Their existing declarations,
imports and proofs need no adaptation; the visibility addition makes the
existing helper available to the item. No hypotheses, universes or proof change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.WeaklyContractibleEtaleConstantModels | unclaimed | Helper made public; its existing proof and internal call unchanged. |
| Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation | P3 | Remove private duplicate, add proof import, use existing helper four times. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | not adapted | No reference to helper; no change required. |
| Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor | not adapted | No reference to helper; no change required. |
| Sheaf.SixFunctors.ConnectedEtalePerfectConstant | not adapted | No reference to helper; no change required. |
| Sheaf.SixFunctors.EtaleStratifiedStalkIdentification | not adapted | No reference to helper; no change required. |

`tools/import_direction.py may` confirms the new import has no cycle.
Both changed files compiled together through lcompile.py.

## Status

landed 20261023T151914-L-422515 2026-10-23 (merge of deliver/P3/Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation)
