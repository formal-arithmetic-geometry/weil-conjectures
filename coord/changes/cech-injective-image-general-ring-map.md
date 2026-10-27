# CategoryTheory.CechInjectiveImage.cech_injective_image_augmentation

## Reason

The Cartesian ring-map assumption is unused by the complete existing proof. Removing it allows the assigned arbitrary-ring-map pushforward model to use its sectionwise exact augmentation directly. No definition or target signature changes.

## Old

```lean
theorem cech_injective_image_augmentation {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} [HasDerivedCategory.{w} (ringedSiteModules.{u} S)] (f : RingedToposMorphism R S) [IsIso f.ringMap] (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R) [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse] (_fAdj : fInverse ⊣ f.modules) (_commR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a) (_commS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a) (D : CoherentCechImageModel R) (V : Sheaf J (Type u)) [Epi (terminal.from V)] (I : CochainComplex (ringedSiteModules.{u} R) ℕ) (_injective : ∀ q : ℕ, Injective (I.X q)) : ExactAugmentation f D V I
```

## New

```lean
theorem cech_injective_image_augmentation {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}} [HasDerivedCategory.{w} (ringedSiteModules.{u} S)] (f : RingedToposMorphism R S) (fInverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R) [fInverse.Additive] [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse] (_fAdj : fInverse ⊣ f.modules) (_commR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a) (_commS : ∀ (U : Xᵒᵖ) (a b : S.obj.obj U), a * b = b * a) (D : CoherentCechImageModel R) (V : Sheaf J (Type u)) [Epi (terminal.from V)] (I : CochainComplex (ringedSiteModules.{u} R) ℕ) (_injective : ∀ q : ℕ, Injective (I.X q)) : ExactAugmentation f D V I
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CechInjectiveImageAugmentation | unclaimed | The existing proof is unchanged and compiles without the unused instance. |
| Sheaf.CategoryTheory.CechPushforwardAugmentedModel | V4 | Directly applies the strengthened theorem. |

The declaration-use search finds only the defining module; the module downstream audit finds the assigned item only. DAG citers are audited in statement_change.

## Status

landed 20261025T164550-L-1034685 2026-10-25 (merge of deliver/V4/Sheaf.CategoryTheory.CechPushforwardAugmentedModel)
