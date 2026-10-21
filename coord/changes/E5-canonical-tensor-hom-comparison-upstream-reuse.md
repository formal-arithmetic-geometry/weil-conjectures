# Canonical tensor-Hom comparison: quarantine repair by upstream reuse

## Reason

The upstream sync quarantined the assigned module because its theorem refers to the
removed predicate `IsAcyclicTensorKFlat`. The canonical upstream module already
contains the complete comparison proof using `IsKFlatTensor`. Its extension and
descent consumers also have complete upstream counterparts. Restore the three
old import paths as compatibility re-exports, without duplicating any declaration.
The DAG attachments now name the canonical upstream declarations.


## Old

### CanonicalTensorHomUncurryNormalizedComparison

```lean
theorem tensorHomUncurry_normalized_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L')
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M')
    (h : DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv =
      a.hom ≫ DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv ≫
          (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
            (b.hom.op, c.inv)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M =
      (a.hom ⊗ₘ b.hom) ≫ pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M' ≫ c.inv
```

### CanonicalTensorHomUncurryDescentExtension

```lean
theorem exists_tensorHomUncurry_descent_extension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsAcyclicTensorKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) :
    letI := schemeDerivedTensorMonoidal X
    ∃ s : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsAcyclicTensorKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          s (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv)) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      s K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ s K L M f ≫ c.hom
```

### CanonicalTensorHomUncurryDescent

```lean
theorem exists_tensorHomUncurry_descent (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsAcyclicTensorKFlat →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom
```


## New

### CanonicalTensorHomUncurryNormalizedComparison

Compatibility module:

```lean
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison
```

The exported canonical statement is:

```lean
theorem tensorHomUncurry_normalized_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hP' : P'.IsKFlatTensor)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (b : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj L')
    (c : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj M')
    (h : DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv =
      a.hom ≫ DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv ≫
          (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).map
            (b.hom.op, c.inv)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M =
      (a.hom ⊗ₘ b.hom) ≫ pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M' ≫ c.inv
```

### CanonicalTensorHomUncurryDescentExtension

Compatibility module:

```lean
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension
```

The exported canonical statement is:

```lean
theorem exists_tensorHomUncurry_descent_extension (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M))
    (ht : ∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) :
    letI := schemeDerivedTensorMonoidal X
    ∃ s : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          s (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv)) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      s K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ s K L M f ≫ c.hom
```

### CanonicalTensorHomUncurryDescent

Compatibility module:

```lean
module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent
```

The exported canonical statement is:

```lean
theorem exists_tensorHomUncurry_descent (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := schemeDerivedTensorMonoidal X
    ∃ t : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M),
      (∀ (P L M : CochainComplex
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
        P.IsKFlatTensor →
        ∀ φ : P ⟶ homComplex (R := X.sheaf) L
            ((schemeHomKInjectiveResolution X).obj M),
          t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
              (DerivedCategory.Q.map φ ≫
                (schemeDerivedInternalHomResolutionIso X L M).inv) =
            pullbackTensorModelMap X P L ≫
              DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
                schemeHomResolutionInverse X M) ∧
    ∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ≅ K) (b : L' ≅ L) (c : M ≅ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
      t K' L' M' (a.hom ≫ f ≫
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).map (b.hom.op, c.hom)) =
        (a.hom ⊗ₘ b.hom) ≫ t K L M f ≫ c.hom
```


## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison | E5 | Restored compatibility path; upstream comparison is re-exported. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | unclaimed | Restored compatibility path; upstream extension is re-exported. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Restored compatibility path; upstream descent is re-exported. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | unclaimed | Existing consumer already imports the upstream comparison; unchanged. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Existing consumer already imports the upstream extension; unchanged. |
| WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence | unclaimed | Existing consumer already imports upstream descent; unchanged. |

These are all direct declaration users found by source search; `tools/downstream.py`
with the three qualified theorem names reported no additional users. The only
quarantined imports of the old comparison path are included in this packet.
The old descent module also imported the quarantined representative module;
its canonical counterpart already uses the upstream representative, so no repair
of that separately assigned module is necessary here. No upstream source file,
target, definition, or proof is changed. No target meaning review is reopened:
only the historical predicate name in the stale DAG Lean signatures is updated.

## Status

landed 20261021T165814-L-2250573 2026-10-21 (merge of deliver/E5/Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison)
