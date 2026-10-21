# AlgebraicGeometry.Scheme.closedCostalkEtaleModules and the five associated operations

## Reason

The site-specific projection formula is a separate theorem used by the costalk proof.
It needs the existing etale module and pushforward definitions but cannot import its
consumer ClosedCostalkDuality without a cycle. Extract the six declarations into
ClosedCostalkEtaleOperations and publicly import that module from the original.
Every existing signature, instance attribute, universe and defining term stays identical.
Only the blueprint tags in the moved docstrings point to their new definition node.
No target statement or definition meaning changes.

## Old

In `lean/Sheaf/SixFunctors/ClosedCostalkDuality.lean`:

```lean
abbrev closedCostalkEtaleModules (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard ordinary unbounded localization on the small etale site.
Source: Stacks, Tag 05RU (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable instance closedCostalkEtaleModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    HasDerivedCategory (closedCostalkEtaleModules X R) :=
  HasDerivedCategory.standard _

/-- Ring inverse image, by left Kan extension and sheafification on the actual etale sites.
Source: Stacks, Tags 00VC and 00WX (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleRingPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology CommRingCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The canonical ring-sheaf adjunction determining the coefficient unit.
Source: Stacks, Tag 00YV (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    closedCostalkEtaleRingPullback f ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- Actual closed direct image with scalars restricted through the inverse-image unit.
Source: Stacks, Modules on Sites, Tag 03D6
(blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleModulePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R) ⥤
      closedCostalkEtaleModules Y R :=
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.pullback @Etale ⊤ f)
    (J := Y.smallGrothendieckTopology @Etale) (K := X.smallGrothendieckTopology @Etale)
    (S := (sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (R := (sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((closedCostalkEtaleRingPullback f).obj R))
    ⟨Functor.whiskerRight ((closedCostalkEtaleRingAdjunction f).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Closed direct image is additive since its linear components are unchanged.
Source: Stacks, Tag 03D6 (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable instance closedCostalkEtaleModulePush_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    (closedCostalkEtaleModulePush f R).Additive where
  map_add := by intros; rfl
```

## New

In `lean/Sheaf/SixFunctors/ClosedCostalkEtaleOperations.lean`, re-exported by
`public import Sheaf.SixFunctors.ClosedCostalkEtaleOperations` in the original module:

```lean
abbrev closedCostalkEtaleModules (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard ordinary unbounded localization on the small etale site.
Source: Stacks, Tag 05RU (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable instance closedCostalkEtaleModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    HasDerivedCategory (closedCostalkEtaleModules X R) :=
  HasDerivedCategory.standard _

/-- Ring inverse image, by left Kan extension and sheafification on the actual etale sites.
Source: Stacks, Tags 00VC and 00WX (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable def closedCostalkEtaleRingPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology CommRingCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The canonical ring-sheaf adjunction determining the coefficient unit.
Source: Stacks, Tag 00YV (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable def closedCostalkEtaleRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    closedCostalkEtaleRingPullback f ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- Actual closed direct image with scalars restricted through the inverse-image unit.
Source: Stacks, Modules on Sites, Tag 03D6
(blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable def closedCostalkEtaleModulePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R) ⥤
      closedCostalkEtaleModules Y R :=
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.pullback @Etale ⊤ f)
    (J := Y.smallGrothendieckTopology @Etale) (K := X.smallGrothendieckTopology @Etale)
    (S := (sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (R := (sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((closedCostalkEtaleRingPullback f).obj R))
    ⟨Functor.whiskerRight ((closedCostalkEtaleRingAdjunction f).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Closed direct image is additive since its linear components are unchanged.
Source: Stacks, Tag 03D6 (blueprint: def-weil-closed-costalk-etale-operations). -/
noncomputable instance closedCostalkEtaleModulePush_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    (closedCostalkEtaleModulePush f R).Additive where
  map_add := by intros; rfl
```

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.ClosedCostalkDuality --uses
closedCostalkEtaleModules` reports zero downstream modules and one direct user,
ClosedCostalkDuality itself. Searches for each of the other five names give no
external consumer. No module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ClosedCostalkDuality | V4 | Publicly re-exports the six unchanged declarations. |
| Sheaf.SixFunctors.ClosedCostalkEtaleOperations | new in V4 | Contains the six identical declarations. |
| Sheaf.SixFunctors.EtaleClosedTensorProjection | new in V4 | Proves the projection identity using the extracted operations. |
| Sheaf.SixFunctors.EtaleNativeTensorPullback | new in V4 | Proves native tensor pullback using the extracted operations. |

## Status

landed 20261021T011047-L-2034296 2026-10-21 (merge of deliver/V4/Sheaf.SixFunctors.ClosedCostalkDuality)
