# schemeMV_image_resolution_comparison_intersection

## Reason

Repair of reviewer X-8738a, E2 / point 4. The universal claim fails for h=id,
U=V=top, nonzero E and the zero short-complex morphism. The construction must
fix all three components from one normalized chain map.

## Old

```lean
theorem schemeMV_image_resolution_comparison_intersection
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let S := schemeMayerVietorisComplex X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I
    let T := schemeMayerVietorisComplex Y U V J
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∀ m : S.map F ⟶ T,
      (schemeDerivedDirectImage h).map
          (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
              schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
              (schemeMVResolutionIso X E).inv ≫
            (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
              (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv) ≫
          (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
            (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I)).hom ≫
          DerivedCategory.Q.map m.τ₃ =
        (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
          (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
              schemeDerivedDirectImage (U ⊓ V).ι).map
              (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
            (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
              (schemeMVAdjunction Y (U ⊓ V))).inv)
```

## New

```lean
theorem schemeMV_image_resolution_comparison_intersection
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
        schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
    (hf : (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map f ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let m := schemeMVImageChainMap (h := h) U V I J f
    (schemeDerivedDirectImage h).map
        (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
            schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
            (schemeMVResolutionIso X E).inv ≫
          (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
            (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv) ≫
        (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
          (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I)).hom ≫
        DerivedCategory.Q.map m.τ₃ =
      (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
        (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
            schemeDerivedDirectImage (U ⊓ V).ι).map
            (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
          (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
            (schemeMVAdjunction Y (U ⊓ V))).inv)
```

`schemeMVImageChainMap` is constructed with first component f, middle component
biprod.lift of the two projection/comparison/restriction maps, and third component
the intersection comparison/restriction map. Its data contains no sorry.
`schemeMV_normalized_chain_map_exists` is proved using Mathlib fullness on maps
into K-injective targets; the parent chooses a witness in its proof, not in a definition.
The sectionwise isomorphism and general localization maps are explicit constructions.
The restriction comparison is an abbreviation of the existing
`schemeMVUnderivedOpenRestriction`; no alternative notion is introduced.
Their chain-square and source-localization compatibilities are separate named theorems.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection | C4 | Correct the false signature and prove the corrected transport identity. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparison | unclaimed | Forced proof/import adaptation: use one normalized f and its constructed m for both equations; signature and visibility identical. |

These are exactly the modules returned by downstream.py --uses for the changed
name. All transitive users of the parent keep its existing statement. No target
statement or definition used to interpret a target has changed.

The parent's removed First import was proof-only. Its replacement proof uses the
new normalized-chain-map existence theorem and the explicit construction; the
old arbitrary m obtained from First supplies no intersection-component equation.
The original parent must fail against the corrected signature at the application
passing m in place of f (and missing hf). The delivered proof replaces only that
necessary choice/application and its obsolete proof import.

## Status

landed 20261013T222359-L-1221444 2026-10-13 (merge of deliver/C4/Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection)
