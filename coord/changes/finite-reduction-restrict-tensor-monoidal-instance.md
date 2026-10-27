# AlgebraicGeometry.FiniteReduction.extend_restrict_tensor

## Reason

Restore the quarantined module after upstream sync 8bd69aede. The archived definition
fails at the call to `Sheaf.presheafToSheafCompTensorRightIso`: synthesis of
`J.W.IsMonoidal` exceeds the default 20000 typeclass heartbeats. The construction and
its signature are correct. Supply the existing Mathlib instance by its declaration,
`GrothendieckTopology.W.monoidal`, locally inside the definition. No limit is raised.

## Old

```lean
def extend_restrict_tensor (f : A →+* B) :
    extend J f ⋙ Sheaf.restrictScalars J f ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} A)).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) := by
  letI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f)
  let S := sheafToPresheaf J (ModuleCat.{u + 1} A)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{u + 1} f)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} B)
  let a := presheafToSheaf J (ModuleCat.{u + 1} A)
  let U := Sheaf.restrictScalars J f
  let X := (Functor.const Cᵒᵖ).obj ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))
  exact Functor.associator S (W ⋙ a') U ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W a' U) ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerLeft W
      (sheafComposeNatIso J (ModuleCat.restrictScalars f)
        (sheafificationAdjunction J (ModuleCat.{u + 1} B))
        (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm) ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W _ a).symm ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight _ _ _).mapIso
          (ModuleCat.extendScalarsCompRestrictScalarsIso f) ≪≫
        whiskeringRightTensorRightIso _) a) ≪≫
    Functor.isoWhiskerLeft S (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
    (Functor.associator S a (tensorRight (a.obj X))).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit)
      (tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
```

## New

```lean
def extend_restrict_tensor (f : A →+* B) :
    extend J f ⋙ Sheaf.restrictScalars J f ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} A)).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) := by
  have : (J.W (A := ModuleCat.{u + 1} A)).IsMonoidal :=
    GrothendieckTopology.W.monoidal
  letI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f)
  let S := sheafToPresheaf J (ModuleCat.{u + 1} A)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{u + 1} f)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} B)
  let a := presheafToSheaf J (ModuleCat.{u + 1} A)
  let U := Sheaf.restrictScalars J f
  let X := (Functor.const Cᵒᵖ).obj ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))
  exact Functor.associator S (W ⋙ a') U ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W a' U) ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerLeft W
      (sheafComposeNatIso J (ModuleCat.restrictScalars f)
        (sheafificationAdjunction J (ModuleCat.{u + 1} B))
        (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm) ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W _ a).symm ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight _ _ _).mapIso
          (ModuleCat.extendScalarsCompRestrictScalarsIso f) ≪≫
        whiskeringRightTensorRightIso _) a) ≪≫
    Functor.isoWhiskerLeft S (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
    (Functor.associator S a (tensorRight (a.obj X))).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit)
      (tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
```

## Users

`tools/downstream.py --allow-missing --uses` reports zero live consumers because this
module and its consumers are quarantined. Searching both `lean/` and `quarantine/`
finds the following consumers and transitive consumers. All are unclaimed when checked.
The four direct consumers use the comparison only as an isomorphism; none unfolds it.
There is no change to the statement, object, or maps of the comparison. The definition
only binds a local proof of the monoidal-localization property, whose proof is irrelevant.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteReductionDerivedExtension | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionFlatExtension | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionEtaleConstructibility | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |
| Sheaf.Paper.ReductionOpenEtaleOrigin | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionConstructibility | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionSystemExistence | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionSystemCoherence | unclaimed | Quarantined consumer; signature and comparison unchanged; no adaptation. |

All four direct consumers were compiled unchanged against the repaired sandbox module
with exit code 0 and no warnings.

The same delivery contains no consumer edits. The target statements and the unit route
are unchanged; no target meaning review is reopened by this elaboration repair.

## Status

landed 20261023T123533-L-1206927 2026-10-23 (merge of deliver/G2/Sheaf.Paper.FiniteReductionRestrictTensor)
