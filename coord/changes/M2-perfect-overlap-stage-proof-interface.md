# AlgebraicGeometry.nestedCounit

## Reason

The restored adapter exceeded the 60-second compiler limit. Local transparency
settings and the cached abelian preadditive instance prevent repeated expansion of the same restriction, homotopy, and
localization constructions. The private counit interfaces now use an explicitly
typed alias of the existing canonical pinned counit. The alias chooses no new data;
its left-derived property is proved from the existing selected composition theorem.
`nestedSourceTriangle` receives the same private interface adjustment.

The interface checker conservatively flags local attributes in a public section.
All four public theorem signatures match the published module verbatim. Public
imports and all six canonical source constructions are unchanged. No existing
definition body changes; the new private alias is used only in theorem proofs.

## Old

Changed local attribute blocks, verbatim:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackCompositionIso
attribute [local instance 2000] schemeOpenRestriction_additive
  schemeOpenRestriction_preservesFiniteLimits schemeOpenRestriction_preservesFiniteColimits
  schemeOpenOverlapRestriction_additive schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits
set_option maxHeartbeats 400000 in
-- Comparing the selected tensor and localization data requires extra heartbeats.
private theorem nestedCounit (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)) :
    (overlapOpenInclusionPullbackIso X i).inv.app (DerivedCategory.Qh.obj P) ≫
        (pinnedPullbackCounit.{u,w} (X.homOfLE (leOfHom i))).app P =
      (schemeOpenOverlapRestriction X i).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (nestedTensorOpenIso X i).inv (.up ℤ)).app P) := by
  classical
  have : PreservesFiniteLimits (schemeOpenOverlapRestriction X i) :=
    schemeOpenOverlapRestriction_preservesFiniteLimits X i
  have : PreservesFiniteColimits (schemeOpenOverlapRestriction X i) :=
    schemeOpenOverlapRestriction_preservesFiniteColimits X i
  let f := X.homOfLE (leOfHom i)
  let T : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let e : schemeOpenOverlapRestriction X i ≅ T := (nestedTensorOpenIso X i).symm
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w}))) f
  have := hL
  have hα : overlapOpenInclusionPullbackIso X i =
      Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback f)
        (pinnedPullbackCounit.{u,w} f) T.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)) ≪≫
        (Functor.mapDerivedCategoryNatIso e).symm := by
    rfl
  exact exactDerivedComparisonCounit T (schemeOpenOverlapRestriction X i)
    (derivedPullback f) (pinnedPullbackCounit.{u,w} f) e
    (overlapOpenInclusionPullbackIso X i) hα P

attribute [local irreducible] nestedRestrictionIso nestedTensorOpenIso
  overlapOpenInclusionPullbackIso perfectHomComposition
  singleComplexOpenPullbackIso openPinnedTensorOpenIso
attribute [local instance 2000] schemeOpenRestriction_additive
  schemeOpenRestriction_preservesFiniteLimits schemeOpenRestriction_preservesFiniteColimits
  schemeOpenOverlapRestriction_additive schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits
private theorem pinnedComposition_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pinnedPullbackComposition.{u,w} f g = perfectHomComposition f g := by
  unfold perfectHomComposition
  rfl

attribute [local irreducible] overlapOpenInclusionPullbackIso
  singleComplexOpenPullbackIso openPinnedTensorOpenIso perfectHomComposition
  schemeDerivedOpenRestrictionCompIso
```

The two existing private signatures, verbatim:

```lean
private theorem nestedCounit (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)) :
    (overlapOpenInclusionPullbackIso X i).inv.app (DerivedCategory.Qh.obj P) ≫
        (pinnedPullbackCounit.{u,w} (X.homOfLE (leOfHom i))).app P =
      (schemeOpenOverlapRestriction X i).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (nestedTensorOpenIso X i).inv (.up ℤ)).app P)

private theorem nestedSourceTriangle
    (X : Scheme.{u}) (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme)
    (k : Y ⟶ X) (h : j ≫ U.ι = k)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
        (DerivedCategory.Qh.{w}.obj P)) ≫
      (perfectHomComposition j U.ι ≪≫ eqToIso
        (congrArg (fun l ↦ derivedPullback.{u,w} l) h)).hom.app
          (DerivedCategory.Qh.{w}.obj P) ≫
      (pinnedPullbackCounit.{u,w} k).app P ≫
      (DerivedCategory.Qh.{w}
        (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
        ((Functor.mapHomotopyCategoryCompIso
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm
          (Scheme.Modules.tensorPullback j :
            SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
              SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι k h).symm)
        (.up ℤ)).inv.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u,w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P)
```

There was no private `comparisonCounit` alias or property theorem.

## New

Replacement and added local attribute blocks, verbatim:

```lean
attribute [local instance 3000] Abelian.toPreadditive

attribute [local irreducible] Scheme.Modules.overEquiv
  Scheme.Modules.overMapCompOverEquiv Scheme.Modules.overFunctorEquiv

attribute [local irreducible] tensorRestrictIso

attribute [local irreducible] nestedRestrictionIso

attribute [local irreducible] nestedTensorOpenIso

attribute [local irreducible] Functor.mapHomotopyCategory DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh Functor.mapDerivedCategory
  schemeDerivedOpenRestrictionCompIso

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackCompositionIso
attribute [local instance 2000] schemeOpenRestriction_additive
  schemeOpenRestriction_preservesFiniteLimits schemeOpenRestriction_preservesFiniteColimits
  schemeOpenOverlapRestriction_additive schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits
private noncomputable def comparisonCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh.{w} ⋙ derivedPullback.{u,w} f ⟶
      (Scheme.Modules.tensorPullback f :
        SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings X.toRingedSpace)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh.{w} :=
  pinnedPullbackCounit.{u,w} f

attribute [local irreducible] comparisonCounit

attribute [local irreducible] overlapOpenInclusionPullbackIso perfectHomComposition
  singleComplexOpenPullbackIso openPinnedTensorOpenIso
attribute [local instance 2000] schemeOpenRestriction_additive
  schemeOpenRestriction_preservesFiniteLimits schemeOpenRestriction_preservesFiniteColimits
  schemeOpenOverlapRestriction_additive schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits
private theorem pinnedComposition_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pinnedPullbackComposition.{u,w} f g = perfectHomComposition f g := by
  unfold perfectHomComposition
  rfl

attribute [local irreducible] overlapOpenInclusionPullbackIso
  singleComplexOpenPullbackIso openPinnedTensorOpenIso perfectHomComposition
  perfectOverlapStageObjectIso
  IsPullback.isoPullback Scheme.Opens.toScheme
attribute [local implicit_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  Monotone.functor TopCat.Hom.frameHom TopologicalSpace.Opens.instCompleteLattice
  TopologicalSpace.Opens.instFrame CompleteLattice.toConditionallyCompleteLattice
  ConditionallyCompleteLattice.toLattice Lattice.toSemilatticeInf SemilatticeInf.toMin
  min SemilatticeInf.inf Lattice.inf Set.inter perfectOverlapStageEquivalence
  overlapSchemeIsoDerivedEquivalence CategoryTheory.Equivalence.mk
```

The two private signatures now refer to the definitionally identical canonical alias:

```lean
private theorem nestedCounit (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)) :
    (overlapOpenInclusionPullbackIso X i).inv.app (DerivedCategory.Qh.obj P) ≫
        (comparisonCounit.{u,w} (X.homOfLE (leOfHom i))).app P =
      (schemeOpenOverlapRestriction X i).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (nestedTensorOpenIso X i).inv (.up ℤ)).app P)

private theorem nestedSourceTriangle
    (X : Scheme.{u}) (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme)
    (k : Y ⟶ X) (h : j ≫ U.ι = k)
    (P : HomotopyCategory (SheafOfModules.{u}
      (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
        (DerivedCategory.Qh.{w}.obj P)) ≫
      (perfectHomComposition j U.ι ≪≫ eqToIso
        (congrArg (fun l ↦ derivedPullback.{u,w} l) h)).hom.app
          (DerivedCategory.Qh.{w}.obj P) ≫
      (comparisonCounit.{u,w} k).app P ≫
      (DerivedCategory.Qh.{w}
        (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
        ((Functor.mapHomotopyCategoryCompIso
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm
          (Scheme.Modules.tensorPullback j :
            SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
              SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι k h).symm)
        (.up ℤ)).inv.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (comparisonCounit.{u,w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P)
```

The complete new private counit API is:

```lean
private noncomputable def comparisonCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh.{w} ⋙ derivedPullback.{u,w} f ⟶
      (Scheme.Modules.tensorPullback f :
        SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings X.toRingedSpace)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh.{w} :=
  pinnedPullbackCounit.{u,w} f

private theorem comparisonCounit_isLeftDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback.{u,w} f).IsLeftDerivedFunctor (comparisonCounit f)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) := by
  exact (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u,w}))) f

attribute [local irreducible] comparisonCounit
```

The public statements, visibility, and public imports stay identical. The only added
import is a private proof import of the existing source associativity lemma. The
remaining changes are proof bodies, including the stage equation proved first as
an equality of natural isomorphisms and then evaluated at its component.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence --uses
nestedCounit nestedSourceTriangle overlapOpenInclusionPullbackIso_whiskerLeft
overlapOpenInclusionPullbackIso_hom_comp overlapOpenInclusionPullbackIso_inv_comp
perfectOverlapStageObjectIso_hom_app` listed the four downstream modules below.
Both changed private names are used only in the item itself. No consumer file is
changed or requires adaptation. The archived consumers also retain the same public
API and the same six canonical source constructions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence | M2 | Assigned item: proof optimization, local attributes, and private counit alias. |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase | unclaimed | Public signatures and constructions unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositeAbstract | unclaimed | Public signatures and constructions unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrism | unclaimed | Public signatures and constructions unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrismHom | unclaimed | Public signatures and constructions unchanged; no adaptation required. |

## Status

landed 20261021T003510-L-1644238 2026-10-21 (merge of deliver/M2/Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence)
