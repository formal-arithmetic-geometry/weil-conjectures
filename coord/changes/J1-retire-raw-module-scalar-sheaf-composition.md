# AlgebraicGeometry.Etale.rawModuleScalar_sheaf_composition

## Reason

The assigned module is a retirement item in coord/retire-items.tsv. It has zero holes.
Its sole public theorem is already proved in the adopted upstream module
WeilConjectures.AlgebraicGeometry.RawModuleScalarSheafComposition. The only statement
presentation difference is RawModuleScalarComparison.forget versus moduleAbelianForget.
The former is an abbreviation of the latter, so the statements are definitionally equal.
Retire the local duplicate and point its DAG node at the canonical theorem.

## Old

The file lean/Sheaf/AlgebraicGeometry/RawModuleScalarSheafComposition.lean publicly
imports Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso and declares a
private scalar_unit helper and the following public theorem:

```lean
theorem rawModuleScalar_sheaf_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    RawModuleScalarComparison.pullback Λ h' L ≫
        (RawModuleScalarComparison.forget Λ Y').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) =
      (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
          ((RawModuleScalarComparison.forget Λ S).obj L) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map
          (RawModuleScalarComparison.pullback Λ h L) ≫
        RawModuleScalarComparison.pullback Λ a
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)
```

The node lem-sbc-raw-scalar-sheaf-composition points at that Sheaf module.

## New

Withdraw the local duplicate through deleted.txt. The delivery tool writes an empty
module at its old path. Keep the mathematical node, with its full statement, proof,
proof dependencies, source and unit binding unchanged, and repoint only its lean
attachment to the existing upstream declaration:

```lean
theorem rawModuleScalar_sheaf_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    RawModuleScalarComparison.pullback Λ h' L ≫
        (moduleAbelianForget Λ Y').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) =
      (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
          ((moduleAbelianForget Λ S).obj L) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map
          (RawModuleScalarComparison.pullback Λ h L) ≫
        RawModuleScalarComparison.pullback Λ a
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)
```

No upstream file is edited. No definition is changed. In particular the canonical
unit-compatible scalar comparison and every Challenge target retain their meanings.
A scratch compatibility theorem uses the old signature verbatim and proves it by
applying the upstream theorem. Its server compilation and axiom output are recorded
in report.md; no compatibility wrapper or new declaration is added to the library.

## Users

The current tools/downstream.py --direct --uses scan reports zero direct importers
of the retired module and no external use of its private scalar_unit helper.
pullback_unit_hom, named as missing upstream in the historical retirement row,
is no longer declared or used in the current library. Exact-import and declaration
searches in lean/ and quarantine/ confirm these results. No Lean adaptation is needed.

The three consumers listed in the old retirement row are reconciled as follows.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | J1 | Withdrawn duplicate; its mathematical node points to the canonical upstream theorem. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted | unclaimed | Already reexports the upstream coefficient theorem; no import of the retired path. Its upstream proof privately imports and applies the canonical composition theorem. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Already reexports the upstream source-class theorem; no import of the retired path. Its upstream proof privately imports and applies the canonical composition theorem. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceSquare | unclaimed | Already withdrawn before this delivery. Its mathematical node and references to the composition node are retained. |

The DAG parents lem-sbc-raw-scalar-coefficient-unshifted,
lem-sbc-raw-module-scalar-source-class-formula and lem-sbc-raw-scalar-source-square
continue to cite lem-sbc-raw-scalar-sheaf-composition. The theorem those citations
require is preserved by the upstream attachment, so no parent dependency is removed.
No quarantined parent imports the retired Sheaf path. The unit sk-lem-failure-field
has no realized entry for this module or its node; its route is unchanged.

## Status

landed 20261025T051856-L-4174676 2026-10-25 (merge of deliver/J1/Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition)
