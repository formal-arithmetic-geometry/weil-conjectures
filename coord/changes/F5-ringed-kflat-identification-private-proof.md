# CategoryTheory.RingedKFlatModel.ringed_kFlat_native_model_identification

## Reason

The completed proof adds generic private helpers, the `ZeroObject` scoped
notation, local elaboration options and local registrations of cached existing
complex and derived monoidal instances. These commands support the private proof only. Every public definition
and signature, and every original public import, is preserved. No target meaning changes.
Private imports reuse proved localization, tensor-generator and ordinary-constraint uniqueness helpers.

## Old

```lean
theorem ringed_kFlat_native_model_identification
    (_flatResolution : Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ RingedTensorModules.{c, v, u} J R))
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    (∀ P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
      P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor) ∧
    (∃! ε : Localization.{c, v, u, w} J R S, LocalizationNormalized.{c, v, u, w} J R S T ε) ∧
    ∀ ε : Localization.{c, v, u, w} J R S, LocalizationNormalized.{c, v, u, w} J R S T ε →
      ∃ e : nativeTensor.{c, v, u, w} J R ≅ S.tensor,
        Normalized.{c, v, u, w} J R S T e ∧
        (∀ e' : nativeTensor.{c, v, u, w} J R ≅ S.tensor,
          Normalized.{c, v, u, w} J R S T e' → e' = e) ∧
        (∀ U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
          e.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ≫ ε.app (U, V) =
            nativeLocalization.{c, v, u, w} J R U V) ∧
        (∀ U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
          (U.IsKFlatIndependentCoefficients ∨ V.IsKFlatIndependentCoefficients) →
            IsIso (ε.app (U, V)) ∧ IsIso (nativeLocalization.{c, v, u, w} J R U V)) ∧
        (∀ (U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
          (hU : U.IsKFlatIndependentCoefficients) (hV : V.IsKFlatIndependentCoefficients),
          (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V (Or.inl hU)).hom ≫
            e.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) =
              (hc.tensorIso U V (Or.inl hU)).hom) ∧
        Constraints (RingedDerivedNative.monoidal.{c, v, u, w} J R) S.monoidal
          (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
          (RingedDerivedNative.unitIso.{c, v, u, w} J R) hc.unitIso e
```

## New

```lean
theorem ringed_kFlat_native_model_identification
    (_flatResolution : Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ RingedTensorModules.{c, v, u} J R))
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    (∀ P : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
      P.IsKFlatIndependentCoefficients ↔ P.IsKFlatForTotalTensor) ∧
    (∃! ε : Localization.{c, v, u, w} J R S, LocalizationNormalized.{c, v, u, w} J R S T ε) ∧
    ∀ ε : Localization.{c, v, u, w} J R S, LocalizationNormalized.{c, v, u, w} J R S T ε →
      ∃ e : nativeTensor.{c, v, u, w} J R ≅ S.tensor,
        Normalized.{c, v, u, w} J R S T e ∧
        (∀ e' : nativeTensor.{c, v, u, w} J R ≅ S.tensor,
          Normalized.{c, v, u, w} J R S T e' → e' = e) ∧
        (∀ U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
          e.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) ≫ ε.app (U, V) =
            nativeLocalization.{c, v, u, w} J R U V) ∧
        (∀ U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
          (U.IsKFlatIndependentCoefficients ∨ V.IsKFlatIndependentCoefficients) →
            IsIso (ε.app (U, V)) ∧ IsIso (nativeLocalization.{c, v, u, w} J R U V)) ∧
        (∀ (U V : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
          (hU : U.IsKFlatIndependentCoefficients) (hV : V.IsKFlatIndependentCoefficients),
          (RingedDerivedNative.tensorIso.{c, v, u, w} J R U V (Or.inl hU)).hom ≫
            e.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj V) =
              (hc.tensorIso U V (Or.inl hU)).hom) ∧
        Constraints (RingedDerivedNative.monoidal.{c, v, u, w} J R) S.monoidal
          (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
          (RingedDerivedNative.unitIso.{c, v, u, w} J R) hc.unitIso e
```

The theorem now has a complete proof. All added definitions and lemmas are private and proved;
none adds a public instance or API. The private instance caches avoid repeated synthesis of the existing monoidal structures.
Their registrations are local; the constructions themselves are unchanged. Graded tensor existence
caches are proved specializations of the existing helpers at the same independent universes.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RingedKFlatNativeModelIdentification --uses
ringed_kFlat_native_model_identification` lists no downstream importers and only the item itself
as a textual user. The DAG parents remain unchanged; none needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedKFlatNativeModelIdentification | F5 | Complete proof; unchanged public API. |

## Status

landed 20261025T003315-L-3226485 2026-10-25 (merge of deliver/F5/Sheaf.Algebra.Homology.RingedKFlatNativeModelIdentification)
