# AlgebraicGeometry.Scheme.Modules.scalarTensorCoefficient_unit

## Reason

Retire the duplicate assigned by coord/retire-items.tsv, under the human's
2026-10-20 hand-off in coord/changes/retire-sheaf-twins-20261020.md. This is a
zero-hole retirement, not a proof or a decomposition. The source-library twin
has the identical theorem statement and complete proof. The full source diff
contains only the copyright header, one blank line, and the local monoidal
instance's name and formatting. The instance value is identical.

The three prerequisite copies in the retirement row have already been retired.
The current Sheaf module imports the adopted FieldLinearModuleCohomologyOperations.
There are no live importers of the duplicate. The theorem remains necessary:
the two DAG parents still use it, so its node is retained and reattached to the
upstream declaration, with its statement and proof dependencies unchanged.
No upstream file or target statement is modified.

## Old

The theorem was duplicated in:

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

Module: Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient.
DAG attachment: lem-sc-scalar-tensor-unit-coefficient.
Declaration: AlgebraicGeometry.Scheme.Modules.scalarTensorCoefficient_unit.
The unchanged signature in both copies is:

```lean
theorem scalarTensorCoefficient_unit
    (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    ((scalarSheaf f F) ◁ scalarUnitMorphism f) ≫
        scalarTensorCoefficient f F (SheafOfModules.unit X.ringCatSheaf) ≫
        scalarHom f (ρ_ F).hom = (ρ_ (scalarSheaf f F)).hom ∧
    (scalarUnitMorphism f ▷ (scalarSheaf f F)) ≫
        scalarTensorCoefficient f (SheafOfModules.unit X.ringCatSheaf) F ≫
        scalarHom f (λ_ F).hom = (λ_ (scalarSheaf f F)).hom
```

## New

The duplicate is withdrawn through deleted.txt; the DAG attachment becomes:

```text
module: WeilConjectures.AlgebraicGeometry.ScalarTensorUnitCoefficient
file: lean/WeilConjectures/AlgebraicGeometry/ScalarTensorUnitCoefficient.lean
declaration: AlgebraicGeometry.Scheme.Modules.scalarTensorCoefficient_unit
```

The theorem's signature, proof and all scalar data remain unchanged in the adopted
source library. The withdrawal tool writes an empty module before queue cleanup.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient | P2 | Duplicate withdrawn; node reattached to identical upstream theorem. |
| WeilConjectures.AlgebraicGeometry.ScalarCupUnitIdentities | unclaimed | Already imports the upstream twin and uses the same theorem; unchanged. |
| Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility | K2 | Quarantined, absent from the live library. Its archived import is recorded below; its theorem and DAG dependencies are retained. |

The frozen quarantine archive for ScalarCupResolutionClassCompatibility still
mentions the Sheaf import. Its current rework assignment is held by K2. It is not
a live consumer and is neither deleted nor restored in this packet. Restoration
must use WeilConjectures.AlgebraicGeometry.ScalarTensorUnitCoefficient, with the
same scalarTensorCoefficient_unit applications at archived lines 225 and 433.
The archive's separate stale FieldLinearModuleCohomologyOperations import also
needs its adopted twin, as recorded in the existing rework failure. A scratch
check of those import migrations currently encounters stale compiled copies of
the recently retired field-linear dependency. No proof or declaration in this
quarantined parent has been removed or weakened.

## Status

landed 20261020T154050-L-3039170 2026-10-20 (merge of deliver/P2/Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient)
