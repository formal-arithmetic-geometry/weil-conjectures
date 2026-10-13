# moduleCup_globalComparison

## Reason

Repeated transport through quotientCompQhIso caused elaboration to exceed the
single-file limit. Factor the unchanged construction through its natural
transformation moduleCup_comparisonNatTrans, whose component is definitionally
the original map. comparison_app proves this component equality by rfl.
The original signature stays identical. No mathematical meaning changes.
The canonical localization lax tensor instance is also named moduleCup_sourceLax
in the new helper, and used by both modules; its data is the original inferred
instance, not an existence witness or a new axiom.

## Old

```lean
def moduleCup_globalComparison
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
      (DerivedCategory.Q.obj K) :=
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  (DerivedCategory.quotientCompQhIso
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).inv.app _ ≫
    S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    S.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).hom.app K)
```

## New

```lean
def moduleCup_globalComparison
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj
      (DerivedCategory.Q.obj K) :=
  (moduleCup_comparisonNatTrans X).app K
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ModuleCupNaiveDerivedCompatibility | G4 | Body refactored through the same natural transformation; signature unchanged. |

| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unchanged, no adaptation | Local instances use the same sheaf tensor construction. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unchanged, no adaptation | Local instances use the same sheaf tensor construction. |
| Sheaf.Paper.ModuleCupRealizationEvaluation | unchanged, no adaptation | Local instances use the same sheaf tensor construction. |
| Sheaf.Paper.ModuleCupResolutionInvariance | unchanged, no adaptation | Local instances use the same sheaf tensor construction. |

The downstream.py --uses check lists only this module as a direct declaration
user. ModuleCupEqualDerivedMapsClass is the current direct importer and uses the compatibility module only in its proof; it needs no
adaptation. The five Challenge signatures are untouched; the comparison is
definitionally the same transported derived unit. There are no forced adaptations.

## Status

landed 20261013T153500-L-1085119 2026-10-13 (merge of deliver/G4/Sheaf.Paper.ModuleCupNaiveDerivedCompatibility)
