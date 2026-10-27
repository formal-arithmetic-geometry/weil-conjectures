# closedFibreModuleEvaluation, closedFibreModuleSectionsRestriction, closedFibreModuleDerivedRestriction

## Reason

The generic weakly etale localization comparison uses the evaluation constructions and is needed by the proper rigidity proof. Move their unchanged definitions to a standalone module to avoid an import cycle. This is a mathematical interface extraction, not a compile-time workaround. No statement, body, attribute or universe changes.

## Old

In Sheaf.Paper.ProperWContractibleClosedFibreRigidity:

```lean
/-- Evaluation of an internal module at a small pro-etale site object, forgetting its action.
Source: the derived-evaluation convention in the proper closed-fibre comparison
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
abbrev closedFibreModuleEvaluation (X : Scheme.{u}) (U : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op U)

/-- Restriction of sections along a map from Z to the evaluating object over X.
It is the module adjunction unit, evaluated at U, followed by the presheaf restriction
along the map from the terminal Z-object to the base change of U.
Source: the canonical restriction described in the node, final paragraph
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def closedFibreModuleSectionsRestriction {X Z : Scheme.{u}} (a : Z ⟶ X)
    (U : X.ProEt) (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a) :
    closedFibreModuleEvaluation Λ X U ⟶
      upperStar Λ a ⋙ closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z)) :=
  Functor.whiskerRight (upperStarLowerStarAdjunction Λ a).unit
      (closedFibreModuleEvaluation Λ X U) ≫
    Functor.whiskerLeft (upperStar Λ a)
      (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ Z))
        ((sheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}).map
          (MorphismProperty.Over.homMk
            (pullback.lift φ (𝟙 Z) (hφ.trans (Category.id_comp a).symm))
            (pullback.lift_snd _ _ _)).op))

/-- The ordinary unbounded derived restriction map. Exact inverse image acts termwise;
the right-derived pullback is characterized by the evaluation map and derived units.
Source: the node's canonical derived restriction, final paragraph
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def closedFibreModuleDerivedRestriction {X Z : Scheme.{u}} (a : Z ⟶ X)
    (U : X.ProEt) (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a) :
    (closedFibreModuleEvaluation Λ X U).rightDerivedFunctor ⟶
      (upperStar Λ a).mapDerivedCategory ⋙
        (closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z))).rightDerivedFunctor :=
  Functor.rightDerivedPullback (upperStar Λ a)
    (closedFibreModuleSectionsRestriction Λ a U φ hφ)
```

## New

Exactly the same declarations and bodies, now in Sheaf.Paper.ClosedFibreModuleEvaluation. The original module publicly imports the new module. Thus every original import still sees the same names and definitions. The new module uses the same namespace, public section and universe.

```lean
/-- Evaluation of an internal module at a small pro-etale site object, forgetting its action.
Source: the derived-evaluation convention in the proper closed-fibre comparison
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
abbrev closedFibreModuleEvaluation (X : Scheme.{u}) (U : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op U)

/-- Restriction of sections along a map from Z to the evaluating object over X.
It is the module adjunction unit, evaluated at U, followed by the presheaf restriction
along the map from the terminal Z-object to the base change of U.
Source: the canonical restriction described in the node, final paragraph
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def closedFibreModuleSectionsRestriction {X Z : Scheme.{u}} (a : Z ⟶ X)
    (U : X.ProEt) (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a) :
    closedFibreModuleEvaluation Λ X U ⟶
      upperStar Λ a ⋙ closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z)) :=
  Functor.whiskerRight (upperStarLowerStarAdjunction Λ a).unit
      (closedFibreModuleEvaluation Λ X U) ≫
    Functor.whiskerLeft (upperStar Λ a)
      (Functor.whiskerLeft (Mod.forget (condensedRingObj Λ Z))
        ((sheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}).map
          (MorphismProperty.Over.homMk
            (pullback.lift φ (𝟙 Z) (hφ.trans (Category.id_comp a).symm))
            (pullback.lift_snd _ _ _)).op))

/-- The ordinary unbounded derived restriction map. Exact inverse image acts termwise;
the right-derived pullback is characterized by the evaluation map and derived units.
Source: the node's canonical derived restriction, final paragraph
(blueprint: lem-sfb-proper-wcontractible-closed-fibre-rigidity). -/
def closedFibreModuleDerivedRestriction {X Z : Scheme.{u}} (a : Z ⟶ X)
    (U : X.ProEt) (φ : Z ⟶ U.left) (hφ : φ ≫ U.hom = a) :
    (closedFibreModuleEvaluation Λ X U).rightDerivedFunctor ⟶
      (upperStar Λ a).mapDerivedCategory ⋙
        (closedFibreModuleEvaluation Λ Z (Scheme.ProEt.mk (𝟙 Z))).rightDerivedFunctor :=
  Functor.rightDerivedPullback (upperStar Λ a)
    (closedFibreModuleSectionsRestriction Λ a U φ hφ)
```

## Users

The downstream scan was run separately for each of the three names. Its six downstream modules are listed below; only ClosedTestLocalizedModelData directly mentions the names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedTestComparisonTestNaturality | unclaimed (no module claim) | Identical declarations publicly reexported; no source change. |
| Sheaf.Paper.ClosedTestDerivedComparisonNormalization | unclaimed (no module claim) | Identical declarations publicly reexported; no source change. |
| Sheaf.Paper.ClosedTestGeometricSectionCoherence | unclaimed (no module claim) | Identical declarations publicly reexported; no source change. |
| Sheaf.Paper.ClosedTestLocalizedModelCoherence | unclaimed (no module claim) | Identical declarations publicly reexported; no source change. |
| Sheaf.Paper.ClosedTestLocalizedModelData | unclaimed (no module claim) | Identical declarations publicly reexported; no source change. |
| Sheaf.Paper.ClosedTestLocalizedRestrictionNormalization | unclaimed (no module claim) | Identical declarations publicly reexported; no source change. |
| Sheaf.Paper.ProperWContractibleClosedFibreRigidity | D9 | Publicly imports the construction module; proof uses the same definitions. |
| Sheaf.Paper.WeaklyEtaleDerivedEvaluationRestriction | new in D9 | Imports the generic construction without importing its consumer. |

## Status

landed 20261024T204548-L-3795262 2026-10-24 (merge of deliver/D9/Sheaf.Paper.ProperWContractibleClosedFibreRigidity)
