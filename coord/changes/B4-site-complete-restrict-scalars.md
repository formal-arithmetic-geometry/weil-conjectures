# CategoryTheory.siteCompleteRestrictScalars

## Reason

Expose the explicit restriction functor on complete full subcategories, completing step 1
of the assigned equivalence proof. The delivery tool requests a change record for this
new public definition. No existing declaration, target statement, or meaning is changed.

## Old

No declaration named `CategoryTheory.siteCompleteRestrictScalars` existed.

## New

```lean
noncomputable def siteCompleteRestrictScalars
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))] :
    ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⥤
      ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) :=
  ObjectProperty.lift (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion)
    (ObjectProperty.ι
      (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
        siteDerivedRestrictScalars φ)
    (fun M ↦ (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I M.obj).mpr M.property)
```

The supporting preservation/reflection theorem identifies the specified exact derived
functor with restriction computed on a complex representative. The definition uses an
explicit full-subcategory lift; its object and map data are those of derived restriction.
It chooses no object from an existence theorem.

## Users

`tools/downstream.py Sheaf.Paper.FlatRingedIdealCompleteEquivalence --uses
siteCompleteRestrictScalars` reports no existing users or downstream modules. The existing
`siteDerivedRestrictScalars` is used only within the assigned module. No adaptations are
needed; the old declarations retain their signatures, visibility, and definitions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | B4 | Adds the explicit complete restriction functor and its conservativity proof. |

## Status

landed 20261018T103529-L-18130 2026-10-18 (merge of deliver/B4/Sheaf.Paper.FlatRingedIdealCompleteEquivalence)
