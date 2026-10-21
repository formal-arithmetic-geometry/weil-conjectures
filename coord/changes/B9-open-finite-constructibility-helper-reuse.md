# Shared open-extension and zero-sheaf helper theorems

## Reason

The returned B9 delivery duplicated private helpers. Make the existing proved helpers public
in their unclaimed Sheaf modules, then import them in OpenFiniteConstructibilityInterval.
No theorem type, theorem proof, definition, instance, attribute or public import changes.
The remaining two duplicates (realization_constructible_iff and constantPresheaf_zero) are
needed only by the existing helpers and are removed entirely from the item.

## Old

`Sheaf.Paper.OpenExtensionFiniteTor`:

```lean
private theorem extension_constructible {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules U (proEtaleConstantRing U A))
    (hF : IsConstructibleProEtaleModuleSheaf U A F) :
    IsConstructibleProEtaleModuleSheaf Y A ((sfIntrinsicExtensionByZero j A).obj F)
```

`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:

```lean
private theorem locallyConstant_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheaf Y A F
```

`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:

```lean
private theorem finite_stalk_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    [Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)] :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) G)
```

`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:

```lean
private theorem finite_stalk_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)
```

## New

`Sheaf.Paper.OpenExtensionFiniteTor`:

```lean
theorem extension_constructible {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules U (proEtaleConstantRing U A))
    (hF : IsConstructibleProEtaleModuleSheaf U A F) :
    IsConstructibleProEtaleModuleSheaf Y A ((sfIntrinsicExtensionByZero j A).obj F)
```

`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:

```lean
theorem locallyConstant_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheaf Y A F
```

`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:

```lean
theorem finite_stalk_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    [Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)] :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) G)
```

`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`:

```lean
theorem finite_stalk_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenExtensionFiniteTor | unclaimed | Existing internal uses of extension_constructible unchanged. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | Existing internal uses of all three helpers unchanged. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Textual hit is the distinct private WeilConjectures.finite_stalk_of_iso; no adaptation needed. |
| Sheaf.Paper.OpenFiniteConstructibilityInterval | B9 | Imports and uses the four canonical theorems; removes six duplicates. |

The downstream.py --uses checks identify the owning modules and the distinct private helper in TwistPreservesFiniteness.
The names were private, so existing external modules cannot use these declarations. Existing
private helpers with the same short names in other modules keep their distinct internal names.
No existing consumer statement or definition changes, and no adaptation is forced.
No target meaning changes: only theorem visibility increases.

## Status

landed 20261021T110953-L-3848931 2026-10-21 (merge of deliver/B9/Sheaf.Paper.OpenFiniteConstructibilityInterval)
