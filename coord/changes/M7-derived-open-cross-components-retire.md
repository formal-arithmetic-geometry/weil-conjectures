# AlgebraicGeometry.derived_open_cross_components_isIso

## Reason

The assigned Sheaf module already contains a complete proof and duplicates the adopted
source theorem in WeilConjectures.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso.
It is listed in coord/retire-items.tsv. Its former DIFFERENT classification described
duplicate foundational imports; its current public restriction-map import and private
intersection-mate import now both point to WeilConjectures. There are no remaining Lean
importers of the Sheaf module, including in quarantine. Retire that copy and reattach
its existing node to the complete adopted proof. No source-library file changes.

## Old

In lean/Sheaf/AlgebraicGeometry/DerivedOpenCrossComponentsIsIso.lean:

```lean
theorem derived_open_cross_components_isIso
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let rW := (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let AU := (schemeDerivedDirectImage U.ι).obj A;
    let BV := (schemeDerivedDirectImage V.ι).obj B;
    let a := adjW.homEquiv AU (sV.obj B)
      (eU.inv.app AU ≫ sU.map (adjU.counit.app A) ≫ c.hom);
    let b := adjW.homEquiv BV (sV.obj B)
      (eV.inv.app BV ≫ sV.map (adjV.counit.app B));
    IsIso (rU.map b) ∧ IsIso (rV.map a)
```

## New

The existing theorem in
lean/WeilConjectures/AlgebraicGeometry/DerivedOpenCrossComponentsIsIso.lean:

```lean
theorem derived_open_cross_components_isIso
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let AU := (schemeDerivedDirectImage U.ι).obj A;
    let BV := (schemeDerivedDirectImage V.ι).obj B;
    let a := adjW.homEquiv AU (sV.obj B)
      (eU.inv.app AU ≫ sU.map (adjU.counit.app A) ≫ c.hom);
    let b := adjW.homEquiv BV (sV.obj B)
      (eV.inv.app BV ≫ sV.map (adjV.counit.app B));
    IsIso (rU.map b) ∧ IsIso (rV.map a)
```

The sole syntactic type difference is the unused rW let-binding. Exact application of
the upstream theorem proves the original type without rewriting. The Sheaf module is
withdrawn through deleted.txt; no replacement declaration is added.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso | unclaimed (assigned to M7 by dispatcher) | Withdraw the duplicate; its DAG node retains the same declaration in the upstream module. |
| WeilConjectures.AlgebraicGeometry.RelativeOpenDifferenceDiagram | unclaimed | Already imports the upstream module and applies this theorem at line 228; no adaptation. |

The downstream command reports zero module importers of the Sheaf module. Its sole
DAG parent is lem-sc-relative-open-difference-diagram, already attached to the adopted
consumer above. The parent's dependency remains the same node, now realized upstream;
its proof and statement do not change. No quarantined parent imports the retired copy.
The unit sk-thm-picard-duality has no realized statement or proof step assigned to this
module. All dependencies and the two-step proof of the existing node are retained.
No target type or definition changes, and no target statement review is reopened.

## Status

landed 20261020T211800-L-3501434 2026-10-20 (merge of deliver/M7/Sheaf.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso)
