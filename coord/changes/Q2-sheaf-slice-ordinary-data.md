# CategoryTheory.RingedSheafSliceOrdinaryComparison

## Reason

The ordinary Stacks 04IF square is a separate result from its unbounded derived
comparison. Its theorem must import the ordinary data without importing the parent
derived theorem. Move the three ordinary interfaces to
`Sheaf.Paper.SheafSliceOrdinaryData`, re-exported publicly by the original module.
Every signature and field of these interfaces is preserved verbatim. The derived
output definition and the assigned theorem signature stay verbatim in the parent.

The new `RingedSheafSliceSquare` records the geometric and module square fields
only. The proved ordinary comparison theorem adds exactness and preservation of
K-flat and K-injective complexes to that square. It does not replace or weaken the
existing ordinary interface.

## Old

In `Sheaf.Paper.SheafSliceDerivedComparison`:

```lean
def sheafSliceUnderlyingRestriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    elementModulePullback.{u, u} (localCoefficientRings R) A ⋙
        underlying (presentationElementRing R A) ≅
      underlying R ⋙ elementSheafPullback A :=
  Iso.refl _

structure SheafSliceSetLocalization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A : Sheaf J (Type u)}
    (S : RingedSheafSliceAdjunctionData R A) where
  iso : Over.star A ⋙ S.fibreEquivalence.inverse ≅ elementSheafPullback A
  sections : ∀ (F : Sheaf J (Type u)) (U : Cᵒᵖ) (s : A.obj.obj U)
    (x : (S.fibreEquivalence.inverse.obj ((Over.star A).obj F)).obj.obj
      (elementObj A U s)),
    (iso.hom.app F).hom.app (elementObj A U s) x =
      (prod.snd : A ⨯ F ⟶ F).hom.app U
        (((S.fibre_iso.hom.app ((Over.star A).obj F)).app (elementObj A U s) x).val)

structure RingedSheafSliceOrdinaryComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u)) where
  sourceSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A)
  targetSlice : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A
  sourceLocalization : SheafSliceSetLocalization sourceSlice
  targetLocalization : SheafSliceSetLocalization targetSlice
  slice : RingedToposMorphism
    (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
    (localCoefficientRings (presentationElementRing RY A))
  sliceInverse : slice.inverse ≅ targetSlice.fibreEquivalence.functor ⋙
    Over.post f.inverse ⋙ sourceSlice.fibreEquivalence.inverse
  starComparison : Over.star A ⋙ Over.post f.inverse ≅
    f.inverse ⋙ Over.star (f.inverse.obj A)
  starComparison_formula : ∀ F : Sheaf K (Type u),
    (starComparison.hom.app F).left = prodComparison f.inverse A F
  sets : elementSheafPullback A ⋙ slice.inverse ≅
    f.inverse ⋙ elementSheafPullback (f.inverse.obj A)
  sets_formula : ∀ F : Sheaf K (Type u), sets.hom.app F =
    slice.inverse.map (targetLocalization.iso.inv.app F) ≫
      sliceInverse.hom.app (targetSlice.fibreEquivalence.inverse.obj ((Over.star A).obj F)) ≫
      sourceSlice.fibreEquivalence.inverse.map ((Over.post f.inverse).map
        (targetSlice.fibreEquivalence.counitIso.hom.app ((Over.star A).obj F))) ≫
      sourceSlice.fibreEquivalence.inverse.map (starComparison.hom.app F) ≫
      sourceLocalization.iso.hom.app (f.inverse.obj F)
  structural : sets.hom.app ((sheafCompose K (forget RingCat)).obj
      (localCoefficientRings RY)) ≫
      (elementSheafPullback (f.inverse.obj A)).map f.ringMap = slice.ringMap
  pullback : modules RY ⥤ modules RX
  [pullbackAdditive : pullback.Additive]
  ordinaryAdjunction : pullback ⊣ f.modules
  slicePullback : ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RY) A) ⥤
    ringedSiteModules.{u, u, u, u}
      (elementRing (localCoefficientRings RX) (f.inverse.obj A))
  [slicePullbackAdditive : slicePullback.Additive]
  sliceOrdinaryAdjunction : slicePullback ⊣ slice.modules
  sigma : elementModulePullback.{u, u} (localCoefficientRings RY) A ⋙ slicePullback ≅
    pullback ⋙ elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)
  delta : f.modules ⋙ elementModulePullback.{u, u} (localCoefficientRings RY) A ≅
    elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A) ⋙ slice.modules
  ordinary_mate :
    (mateEquiv ordinaryAdjunction sliceOrdinaryAdjunction
      (TwoSquare.mk _ _ _ _ sigma.hom)).natTrans = delta.hom
  delta_underlying : ∀ E : modules RX,
    (underlying (presentationElementRing RY A)).map (delta.hom.app E) ≫
      slice.underlying.hom.app
        ((elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).obj E) =
    (sheafSliceUnderlyingRestriction RY A).hom.app (f.modules.obj E) ≫
      (elementSheafPullback A).map (f.underlying.hom.app E) ≫
      (mateEquiv f.adj slice.adj (TwoSquare.mk _ _ _ _ sets.hom)).natTrans.app
        ((underlying RX).obj E) ≫
      slice.direct.map ((sheafSliceUnderlyingRestriction RX (f.inverse.obj A)).inv.app E)
  [targetRestrictionAdditive :
    (elementModulePullback.{u, u} (localCoefficientRings RY) A).Additive]
  [sourceRestrictionAdditive :
    (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).Additive]
  [targetRestrictionLimits :
    PreservesFiniteLimits (elementModulePullback.{u, u} (localCoefficientRings RY) A)]
  [sourceRestrictionLimits :
    PreservesFiniteLimits
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))]
  [targetRestrictionColimits :
    PreservesFiniteColimits (elementModulePullback.{u, u} (localCoefficientRings RY) A)]
  [sourceRestrictionColimits :
    PreservesFiniteColimits
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))]
  targetKFlat : ∀ T : CochainComplex (modules RY) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := RY) T →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := RY) (T.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing RY A)
        ((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (R := presentationElementRing RY A)
        (((onComplex (elementModulePullback.{u, u} (localCoefficientRings RY) A)).obj T).X n)
  sourceKInjective : ∀ I : CochainComplex (modules RX) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective ((onComplex
      (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A))).obj I)
```

## New

The same three declarations above, including all their fields and bodies, now live
in `Sheaf.Paper.SheafSliceOrdinaryData`. Only their blueprint docstrings point to
the new definition node. The original module adds:

```lean
public import Sheaf.Paper.SheafSliceOrdinaryData
```

The new square-only record has the same fields from `sourceSlice` through
`delta_underlying`, and omits the six restriction instance fields and the two
resolution-preservation fields. It is used only as input to the new ordinary
comparison theorem, which proves and supplies every omitted field.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SheafSliceDerivedComparison | Q2 | Publicly re-exports the three unchanged interfaces and proves the derived comparison from the ordinary square. |
| Sheaf.Paper.SheafSliceOrdinaryData | new in Q2 | Owns the moved interfaces and the new square-only record. |
| Sheaf.Paper.SheafSliceOrdinarySquare | new in Q2 | States the separate ordinary Stacks 04IF result. |
| Sheaf.Paper.SheafSliceOrdinaryComparison | new in Q2 | Supplies the restriction exactness and resolution-preservation fields by proof. |

`tools/downstream.py` reports zero downstream modules for the original module.
The declaration-use searches for all three moved names find only that original
module. Thus no other consumer needs adaptation. No module under
`WeilConjectures/` is changed. No target statement or meaning is changed: all
existing types, fields and constructions retain their text.

The parent node's `lean.declarations` now contains just the two declarations that
remain in that file; the moved interfaces attach to the new definition node. The
parent proof route points through the new ordinary theorem and the actual derived
construction. The parent statement-dependency list is unchanged. Only its proof route and
Lean declaration attachment change; the new ordinary-data node owns the moved
interfaces. No target or statement dependency is altered.

## Status

landed 20261021T140856-L-2767715 2026-10-21 (merge of deliver/Q2/Sheaf.Paper.SheafSliceDerivedComparison)
