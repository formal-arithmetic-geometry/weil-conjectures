# representableSliceModuleRestrictionMate

## Reason

The old definition takes the localization mate and immediately its inverse, then
takes the horizontal inverse mate. Evaluate that cancellation before constructing
the horizontal mate. The result is the same fixed map by
`Equiv.symm_apply_apply`; no slice choice affects it. Explicit result types on the
comparison definitions and three named module adjunctions keep elaboration from
expanding chosen adjoint constructions. All are the same canonical adjunctions.
No statement or target is weakened.

## Old

```lean
def representableSliceModuleRestrictionMate
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
  ((mateEquiv (SheafOfModules.pullbackPushforwardAdjunction
    (SheafOfModules.ringedSiteModuleMap U a))
    (SheafOfModules.pullbackPushforwardAdjunction (representableSliceRingMap U a V))).symm
      (TwoSquare.mk _ _ _ _
        (((mateEquiv (representableSliceLocalizationAdjunction targetSlices)
          (representableSliceLocalizationAdjunction sourceSlices)).symm
            (representableSliceModuleLocalizationSquare U a V sourceSlices
              targetSlices)).natTrans))).natTrans
```

## New

```lean
def representableSliceModuleRestrictionMate
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    elementModulePullback ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (J.uliftYoneda.{u}.obj V) ⋙ representableSliceModulePullback U a V ⟶
      SheafOfModules.pullback.{u} (SheafOfModules.ringedSiteModuleMap U a) ⋙
        elementModulePullback ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)) :=
  representableSliceModulePullbackMap U a V


```

The module also gives the fixed continuous module adjunctions the names
`representableSliceModuleAdjunction`, `representableSliceGlobalModuleAdjunction`,
and `representableSliceLocalizedModuleAdjunction`. These are the existing
Mathlib `pullbackPushforwardAdjunction` values, with explicit result types.
The comparison definitions receive explicit, definitionally unchanged result types.
The localized module coefficient map is written as `sliceModuleRingMap U
(ringedSiteModuleMap U a) V`, which is definitionally the same componentwise map
as `ringedSiteModuleMap (Over.post U) (localizedRingedSiteMap U a V)`.
Four proved `HasSheafCompose` instances cache preservation of sheaves under the
forgetful functors from commutative rings, rings and additive groups. Their values
come from Mathlib's existing preservation-of-limits instances; they introduce no
new mathematical hypotheses or data choices. The proved instances
`representableSlice_setRightAdjoint` and `representableSlice_moduleRightAdjoint`
likewise cache Mathlib's existing continuous pullback constructions, avoiding
repeated searches for the same adjunctions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.RepresentableSliceLocalizedRingedMorphism | S3 | Uses the simplified canonical mate and folded adjunction interface. |

No shared source imports this absent item yet. Its recorded parent theorem still
uses its node and is preserved. No adaptation to a module held by another group
is necessary. The public theorem statement remains unchanged.

## Status

landed 20261024T191008-L-206118 2026-10-24 (merge of deliver/S3/Sheaf.CategoryTheory.Sites.RepresentableSliceLocalizedRingedMorphism)
