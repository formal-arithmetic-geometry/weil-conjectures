# Retire the unused cone-normalization branch

## Reason

The supplied route note asks for a natural comparison and an all-shifts five-term argument upstream, cutting both the diagonal and projection applications. The former route demanded a coherent normalized cone comparison that those applications do not use. A full reverse-import audit found exactly this 28-module closed branch with the two changed applications as its only external consumers. Every withdrawn module is unclaimed except the assigned P3 item. All modules and declaration names are listed below. Unit statement/steps are preserved.

## Old

### Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_derivedMonoidalPullback_unitalShift`:

```lean
theorem exists_derivedMonoidalPullback_unitalShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sL : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sL
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Y} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Y)).flip.map b) ℤ) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Z)).flip.map b) ℤ) ∧
      (∀ M : schemeDerivedCategory Y,
        NatTrans.CommShift (F₁ := tensorRight M ⋙ derivedPullback f)
          (F₂ := derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M))
          ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M) ℤ) ∧
      NatTrans.CommShift (rightUnitorNatIso (schemeDerivedCategory Y)).hom ℤ
```

### Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.Algebra.Homology.KFlat`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.derivedMonoidalPullback_unitalShift_kFlat_one`:

```lean
theorem derivedMonoidalPullback_unitalShift_kFlat_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sF
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Y} (b : M ⟶ N)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((curriedTensor (schemeDerivedCategory Y)).flip.map b)
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫ (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((tensorRight N).commShiftIso (1 : ℤ)).hom.app K) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Z.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((curriedTensor (schemeDerivedCategory Z)).flip.map b)
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫ (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((tensorRight N).commShiftIso (1 : ℤ)).hom.app K) ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K) ∧
      (∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := (rightUnitorNatIso (schemeDerivedCategory Y)).hom
        ((tensorRight (𝟙_ (schemeDerivedCategory Y))).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((𝟭 (schemeDerivedCategory Y)).commShiftIso
            (1 : ℤ)).hom.app K)
```

### Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.Algebra.Homology.KFlat`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`, `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift`.

`AlgebraicGeometry.derivedPullback_canonicalTensorShift_one`:

```lean
theorem derivedPullback_canonicalTensorShift_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    letI := schemeCanonicalTensorShift Y
    letI := schemeCanonicalTensorShift Z
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    letI : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    ∃ (sF : (derivedPullback f).CommShift ℤ),
      letI := sF
      (derivedPullback f).IsTriangulated ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K)
```

### Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`, `Sheaf.Algebra.Homology.KFlat`, `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.

`AlgebraicGeometry.exists_derivedPullback_kFlat_cone_counit_normalization`:

```lean
theorem exists_derivedPullback_kFlat_cone_counit_normalization
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z),
        (∀ P : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
        ∀ (P Q : CochainComplex
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
          CochainComplex.IsKFlat (R := Y.sheaf) P →
          CochainComplex.IsKFlat (R := Y.sheaf) Q →
          let C := CochainComplex.mappingCone.triangleh p
          let T := (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y).mapTriangle.obj C
          let W := ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).mapTriangle.obj C
          ε.app C.obj₃ ≫ W.mor₃ =
            (derivedPullback f).map T.mor₃ ≫
              ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
                asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                  ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
                tensorIso e (Iso.refl _) ≪≫
                schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom ≫
                  (ε.app C.obj₁)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitShiftAdjustment

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`, `Sheaf.Algebra.Homology.KFlat`, `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.

`AlgebraicGeometry.exists_derivedPullback_kFlat_counit_shift_adjustment`:

```lean
theorem exists_derivedPullback_kFlat_counit_shift_adjustment
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε₀ : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε₀ : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      IsIso (ε₀.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f),
        let ε := a.hom ≫ ε₀
        ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        ε.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (ε.app X)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.derivedPullback_tensorShift`:

```lean
theorem derivedPullback_tensorShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sF
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated) ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Z)).flip.map b) ℤ) ∧
      (∀ M : schemeDerivedCategory Y,
        NatTrans.CommShift
          (F₁ := tensorRight M ⋙ derivedPullback f)
          (F₂ := derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M))
          ((Functor.flipping.functor.map
            (Functor.OplaxMonoidal.δNatTrans (derivedPullback f))).app M) ℤ)
```

### Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.Algebra.Homology.KFlat`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.derivedPullback_tensorShift_kFlat_one`:

```lean
theorem derivedPullback_tensorShift_kFlat_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sF
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated) ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Z.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((curriedTensor (schemeDerivedCategory Z)).flip.map b)
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫ (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((tensorRight N).commShiftIso (1 : ℤ)).hom.app K) ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.flipping.functor.map
          (Functor.OplaxMonoidal.δNatTrans (derivedPullback f))).app M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K)
```

### Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.derivedPullbackTensorUnitShiftIso`:

```lean
def derivedPullbackTensorUnitShiftIso {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (K : schemeDerivedCategory Y) :
    (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ ((derivedPullback f).obj K)⟦(1 : ℤ)⟧
```

`AlgebraicGeometry.exists_derivedPullback_tensorUnitShift`:

```lean
theorem exists_derivedPullback_tensorUnitShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧),
      letI := sF
      (derivedPullback f).IsTriangulated ∧
      ∀ K : schemeDerivedCategory Y,
        ((derivedPullback f).commShiftIso (1 : ℤ)).hom.app K =
          (derivedPullbackTensorUnitShiftIso f e K).hom
```

### Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitKFlatCones

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`, `Sheaf.Algebra.Homology.KFlat`.

`AlgebraicGeometry.exists_derivedPullback_translatedUnit_kFlat_cones`:

```lean
theorem exists_derivedPullback_translatedUnit_kFlat_cones
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∀ (P Q : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) (p : P ⟶ Q),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        CochainComplex.IsKFlat (R := Y.sheaf) Q →
        let Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y := DerivedCategory.Qh
        let T := Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh p)
        Triangle.mk ((derivedPullback f).map T.mor₁) ((derivedPullback f).map T.mor₂)
          ((derivedPullback f).map T.mor₃ ≫
            ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom) ∈
          distTriang (schemeDerivedCategory Z)
```

### Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_derivedPullback_translatedUnit_triangles`:

```lean
theorem exists_derivedPullback_translatedUnit_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∀ T₀ : Triangle
          (HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (ComplexShape.up ℤ)),
        T₀ ∈ distTriang (HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) →
        let Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y := DerivedCategory.Qh
        let T := Qh.mapTriangle.obj T₀
        Triangle.mk ((derivedPullback f).map T.mor₁) ((derivedPullback f).map T.mor₂)
          ((derivedPullback f).map T.mor₃ ≫
            ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom) ∈
          distTriang (schemeDerivedCategory Z)
```

### Sheaf.AlgebraicGeometry.FlatTelescopeBoundedNormalizationExtension

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization`.

`AlgebraicGeometry.exists_flat_telescope_comparison_of_bounded_normalization`:

```lean
theorem exists_flat_telescope_comparison_of_bounded_normalization
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (β : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hβnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (β X' hX').hom =
            (β X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hβshift : ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
        (hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (β (X⟦(1 : ℤ)⟧) ⟨P, hb, hf, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (β X ⟨P, hb, hf, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧') :
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.FlatTelescopeConeNormalizationDescent

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization`.

`AlgebraicGeometry.exists_flat_telescope_cone_normalization_descent`:

```lean
theorem exists_flat_telescope_cone_normalization_descent
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (β : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hβnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (β X' hX').hom =
            (β X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (σ₀ : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E)
        (DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
          ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).obj X)
    (σ₁ : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)),
        let X := ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E))⟦(1 : ℤ)⟧
        (DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
          ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).obj X)
    (hσ0ι : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) (n : ℕ),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Sigma.ι E n)) ≫
            σ₀ E hb hf =
          (β
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (E n))
            ⟨E n, hb n, hf n, Or.inl rfl⟩).hom ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Sigma.ι E n)))
    (hσ1ι : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) (n : ℕ),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Sigma.ι E n))⟦(1 : ℤ)⟧') ≫
            σ₁ E hb hf =
          (β (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (E n))⟦(1 : ℤ)⟧)
            ⟨E n, hb n, hf n, Or.inr rfl⟩).hom ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              (Sigma.ι E n))⟦(1 : ℤ)⟧'))
    (hσ0nat : ∀ (E E' : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
        (hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E' n).X i))
        (hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i))
        (a : ∀ n : ℕ, E n ⟶ E' n),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Limits.Sigma.map a)) ≫
            σ₀ E' hb' hf' =
          σ₀ E hb hf ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Limits.Sigma.map a)))
    (hσ1nat : ∀ (E E' : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i))
        (hb' : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E' n).X i))
        (hf' : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E' n).X i))
        (a : ∀ n : ℕ, E n ⟶ E' n),
        (DerivedCategory.Qh ⋙ derivedPullback f).map
          (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Limits.Sigma.map a))⟦(1 : ℤ)⟧') ≫
            σ₁ E' hb' hf' =
          σ₁ E hb hf ≫
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z)).map (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              (Limits.Sigma.map a))⟦(1 : ℤ)⟧'))
    (hσshift : ∀ (E : ℕ → CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
        (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E)
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        σ₁ E hb hf ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            σ₀ E hb hf⟦(1 : ℤ)⟧') :
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        (∀ (X : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hb : boundedFlatShiftRepresentative Y X), α X hX = (β X hb).hom) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.FlatTelescopeModelShiftGauge

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_flat_telescope_model_shift_gauge`:

```lean
theorem exists_flat_telescope_model_shift_gauge
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    [(derivedPullback f).CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ a : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            (DerivedCategory.Qh ⋙ derivedPullback f).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hX' : flatTelescopeShiftRepresentative Y X') (s : X ⟶ X'),
          flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (a X' hX').hom =
            (a X hX).hom ≫ (DerivedCategory.Qh ⋙ derivedPullback f).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
          (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        (a (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            ((DerivedCategory.Qh ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            ((a X ⟨P, htel, Or.inl rfl⟩).hom)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationMorphisms

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization`.

`AlgebraicGeometry.exists_flat_telescope_normalization_morphisms`:

```lean
theorem exists_flat_telescope_normalization_morphisms
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (β : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hβnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (β X' hX').hom =
            (β X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hβshift : ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
        (hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (β (X⟦(1 : ℤ)⟧) ⟨P, hb, hf, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (β X ⟨P, hb, hf, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧') :
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        (∀ (X : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hb : boundedFlatShiftRepresentative Y X), α X hX = (β X hb).hom) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.FlatTelescopeShiftGauge

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_flat_telescope_shift_gauge`:

```lean
theorem exists_flat_telescope_shift_gauge
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    [(derivedPullback f).CommShift ℤ] [NatTrans.CommShift ε ℤ] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f),
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
          (_ : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        a.hom.app (X⟦(1 : ℤ)⟧) ≫
            ((DerivedCategory.Qh ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (a.hom.app X)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.NormalizedDerivedPullbackKFlatCounit

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_normalized_derivedPullback_kFlat_counit`:

```lean
theorem exists_normalized_derivedPullback_kFlat_counit
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε₀ : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε₀ : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      IsIso (ε₀.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            (DerivedCategory.Qh : HomotopyCategory
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
              schemeDerivedCategory Z),
        (∀ P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
        ∀ P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        ε.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (ε.app X)⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_normalized_flat_telescope_comparison`:

```lean
theorem exists_normalized_flat_telescope_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeStageComparison

Public imports: `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.exists_normalized_flat_telescope_stage_comparison`:

```lean
theorem exists_normalized_flat_telescope_stage_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison

Public imports: `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.kFlatShiftRepresentative`:

```lean
def kFlatShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop
```

`AlgebraicGeometry.exists_normalized_kFlat_representative_comparison`:

```lean
theorem exists_normalized_kFlat_representative_comparison
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        kFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : kFlatShiftRepresentative Y X) (hX' : kFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX').hom =
            (α X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlat (R := Y.sheaf) P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, hP, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, hP, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧'
```

### Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.CategoryTheory.Triangulated.Subcategory`.

`AlgebraicGeometry.pinnedProjectionCounit_exactShift`:

```lean
theorem pinnedProjectionCounit_exactShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [(schemeDerivedQCohProperty Y).IsTriangulated]
    [(schemeDerivedQCohProperty Z).IsTriangulated]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (E : schemeDerivedQCohCategory Z)
    (hTensor : ∀ K : schemeDerivedQCohCategory Y,
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (ε : (⟨(schemeDerivedDirectImage f).obj E.obj, hRf E⟩ :
      schemeDerivedQCohCategory Y) ⟶ ⟨𝟙_ _, hO⟩)
    (ν : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj)
      hTensor ⋙ (schemeDerivedQCohProperty Y).lift
        ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⟶
      𝟭 (schemeDerivedQCohCategory Y))
    (hν : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ E.obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj E.obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj) ∧
        (ν.app K).hom = pf.hom ≫ K.obj ◁ ε.hom ≫ (ρ_ K.obj).hom) :
    let Q := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙ tensorRight E.obj) hTensor
    let R := (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf
    ∃ (sQ : Q.CommShift ℤ) (sR : R.CommShift ℤ),
      letI := sQ
      letI := sR
      Q.IsTriangulated ∧ R.IsTriangulated ∧ NatTrans.CommShift ν ℤ
```

### Sheaf.AlgebraicGeometry.ProjectionComparisonExact

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.CategoryTheory.Triangulated.Functor`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.projectionComparisonNatTrans`:

```lean
def projectionComparisonNatTrans
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedCategory Z) :
    tensorRight ((schemeDerivedDirectImage f).obj E) ⟶
      (derivedPullback f ⋙ tensorRight E) ⋙ schemeDerivedDirectImage f
```

`AlgebraicGeometry.projectionComparison_exact`:

```lean
theorem projectionComparison_exact
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedQCohCategory Z) :
    ∃ (s : (tensorRight ((schemeDerivedDirectImage f).obj E.obj)).CommShift ℤ)
      (t : ((derivedPullback f ⋙ tensorRight E.obj) ⋙
        schemeDerivedDirectImage f).CommShift ℤ),
      letI := s
      letI := t
      (tensorRight ((schemeDerivedDirectImage f).obj E.obj)).IsTriangulated ∧
      ((derivedPullback f ⋙ tensorRight E.obj) ⋙
        schemeDerivedDirectImage f).IsTriangulated ∧
      NatTrans.CommShift (projectionComparisonNatTrans f a E.obj) ℤ
```

### Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.projectionComparison_triangles`:

```lean
theorem projectionComparison_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (E : schemeDerivedQCohCategory Z) :
    let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
      IsIso ((a.homEquiv _ _)
        ((Functor.Monoidal.μIso (derivedPullback f) K.obj
          ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app E.obj))
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C)
```

### Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.rightAdjointTensorComparison_diagrams`:

```lean
theorem rightAdjointTensorComparison_diagrams
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (τ : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
      ⟶ c)
    (hτ : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) :
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ)
      (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) →
      ∃ (eF : ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          (((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj)⟦n⟧))
        (ec : (c.obj B).obj ≅ (c.obj A).obj⟦n⟧),
        (τ.app B).hom ≫ ec.hom =
          eF.hom ≫ (shiftFunctor (schemeDerivedCategory Z) n).map (τ.app A).hom) ∧
    (∀ (A B C : schemeDerivedQCohCategory Y)
      (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
      T ∈ Pretriangulated.distinguishedTriangles →
      Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
      Nonempty (T.obj₃ ≅ C.obj) →
      ∃ (T₁ T₂ : Pretriangulated.Triangle (schemeDerivedCategory Z)) (m : T₁ ⟶ T₂),
        T₁ ∈ Pretriangulated.distinguishedTriangles ∧
        T₂ ∈ Pretriangulated.distinguishedTriangles ∧
        ∃ (eF₁ : T₁.obj₁ ≅ ((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₁ : T₂.obj₁ ≅ (c.obj A).obj)
          (eF₂ : T₁.obj₂ ≅ ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₂ : T₂.obj₂ ≅ (c.obj B).obj)
          (eF₃ : T₁.obj₃ ≅ ((derivedPullback f).obj C.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₃ : T₂.obj₃ ≅ (c.obj C).obj),
          m.hom₁ = eF₁.hom ≫ (τ.app A).hom ≫ ec₁.inv ∧
          m.hom₂ = eF₂.hom ≫ (τ.app B).hom ≫ ec₂.inv ∧
          m.hom₃ = eF₃.hom ≫ (τ.app C).hom ≫ ec₃.inv)
```

### Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.rightAdjointTensorComparison_shift`:

```lean
theorem rightAdjointTensorComparison_shift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (τ : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
      ⟶ c)
    (hτ : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) :
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ)
      (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) →
      ∃ (eF : ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          (((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj)⟦n⟧))
        (ec : (c.obj B).obj ≅ (c.obj A).obj⟦n⟧),
        (τ.app B).hom ≫ ec.hom =
          eF.hom ≫ (shiftFunctor (schemeDerivedCategory Z) n).map (τ.app A).hom)
```

### Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonTriangle

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.rightAdjointTensorComparison_triangle`:

```lean
theorem rightAdjointTensorComparison_triangle
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (τ : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
      ⟶ c)
    (hτ : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) :
    (∀ (A B C : schemeDerivedQCohCategory Y)
      (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
      T ∈ Pretriangulated.distinguishedTriangles →
      Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
      Nonempty (T.obj₃ ≅ C.obj) →
      ∃ (T₁ T₂ : Pretriangulated.Triangle (schemeDerivedCategory Z)) (m : T₁ ⟶ T₂),
        T₁ ∈ Pretriangulated.distinguishedTriangles ∧
        T₂ ∈ Pretriangulated.distinguishedTriangles ∧
        ∃ (eF₁ : T₁.obj₁ ≅ ((derivedPullback f).obj A.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₁ : T₂.obj₁ ≅ (c.obj A).obj)
          (eF₂ : T₁.obj₂ ≅ ((derivedPullback f).obj B.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₂ : T₂.obj₂ ≅ (c.obj B).obj)
          (eF₃ : T₁.obj₃ ≅ ((derivedPullback f).obj C.obj ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj))
          (ec₃ : T₂.obj₃ ≅ (c.obj C).obj),
          m.hom₁ = eF₁.hom ≫ (τ.app A).hom ≫ ec₁.inv ∧
          m.hom₂ = eF₂.hom ≫ (τ.app B).hom ≫ ec₂.inv ∧
          m.hom₃ = eF₃.hom ≫ (τ.app C).hom ≫ ec₃.inv)
```

### Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.rightAdjointTensor_compatibleExactStructures`:

```lean
theorem rightAdjointTensor_compatibleExactStructures
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [(schemeDerivedQCohProperty Y).IsStableUnderShift ℤ]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (τ : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩))
      ⟶ c)
    (hτ : ∀ K : schemeDerivedQCohCategory Y,
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
        pf.inv = (a.homEquiv _ _)
          ((Functor.Monoidal.μIso (derivedPullback f) K.obj
            ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
            (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
        τ.app K = ((adj.homEquiv
          ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
            hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
          (ObjectProperty.homMk (pf.hom ≫
            K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))) :
    let F := (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback f ⋙
        tensorRight (c.obj ⟨𝟙_ _, hO⟩).obj)
      (fun K ↦ hTensor K (c.obj ⟨𝟙_ _, hO⟩)) ⋙ (schemeDerivedQCohProperty Z).ι
    let G := c ⋙ (schemeDerivedQCohProperty Z).ι
    ∃ (sF : F.CommShift ℤ) (sG : G.CommShift ℤ),
      letI := sF
      letI := sG
      NatTrans.CommShift (Functor.whiskerRight τ (schemeDerivedQCohProperty Z).ι) ℤ ∧
      ∀ S : Pretriangulated.Triangle (schemeDerivedQCohCategory Y),
        (schemeDerivedQCohProperty Y).ι.mapTriangle.obj S ∈
          Pretriangulated.distinguishedTriangles →
        F.mapTriangle.obj S ∈ Pretriangulated.distinguishedTriangles ∧
        G.mapTriangle.obj S ∈ Pretriangulated.distinguishedTriangles
```

### Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.CategoryTheory.ObjectProperty.Retract`, `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`.

`AlgebraicGeometry.rightAdjointTensorLocus_localizing`:

```lean
theorem rightAdjointTensorLocus_localizing
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [HasCoproducts.{u} (schemeDerivedQCohCategory Y)]
    [HasCoproducts.{u} (schemeDerivedQCohCategory Z)]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
    (hsums : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) c) :
    let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
    (∀ (A B : schemeDerivedQCohCategory Y), P A → Nonempty (A ≅ B) → P B) ∧
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P B →
      Nonempty (Retract A.obj B.obj) → P A) ∧
    (∀ (J : Type u) (E : J → schemeDerivedQCohCategory Y),
      ∀ (S : schemeDerivedCategory Y) (ι : ∀ j, (E j).obj ⟶ S),
        IsColimit (Cofan.mk S ι) →
        ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ S) →
          (∀ j, P (E j)) → P B)
```

### Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles

Public imports: `Sheaf.AlgebraicGeometry.DerivedTensorStructure`, `Sheaf.AlgebraicGeometry.DerivedPullback`, `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `Mathlib.AlgebraicGeometry.Noetherian`.

`AlgebraicGeometry.rightAdjointTensorLocus_triangles`:

```lean
theorem rightAdjointTensorLocus_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory Z,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory Z),
      schemeDerivedQCohProperty Z (((derivedPullback f).obj K.obj) ⊗ E.obj))
    [Functor.Monoidal (derivedPullback f)]
    (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c) :
    let P : ObjectProperty (schemeDerivedQCohCategory Y) := fun K ↦
      ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))
    (∀ (A : schemeDerivedQCohCategory Y) (n : ℤ), P A →
      ∀ (B : schemeDerivedQCohCategory Y), Nonempty (B.obj ≅ A.obj⟦n⟧) → P B) ∧
    (∀ (A B : schemeDerivedQCohCategory Y), P A → P B →
      ∀ (T : Pretriangulated.Triangle (schemeDerivedCategory Y)),
        T ∈ Pretriangulated.distinguishedTriangles →
        Nonempty (T.obj₁ ≅ A.obj) → Nonempty (T.obj₂ ≅ B.obj) →
        ∀ (C : schemeDerivedQCohCategory Y), Nonempty (T.obj₃ ≅ C.obj) → P C)
```

## New

The two application theorem signatures and all their public imports are unchanged. Their private normalization/triangle proof imports are replaced by the three proved helper modules. Each path in `deleted.txt` is withdrawn as an empty module by the delivery tool:

```lean
module
```

No new hypothesis, semantic definition change, or replacement weakened cone-normalization theorem is introduced. The 28 original statements remain in their DAG nodes with `lean: null` in the delivery, removing their stale Lean attachments. Other now-unreachable modules remain in the repository because the audited withdrawn set is the closed upstream branch.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitShiftAdjustment | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitKFlatCones | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.FlatTelescopeBoundedNormalizationExtension | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.FlatTelescopeConeNormalizationDescent | P3 | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.FlatTelescopeModelShiftGauge | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationMorphisms | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.FlatTelescopeShiftGauge | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.NormalizedDerivedPullbackKFlatCounit | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeStageComparison | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.ProjectionComparisonExact | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | original signature/public imports preserved; proof rerouted |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonTriangle | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | withdrawn together; no remaining importer |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | original signature/public imports preserved; proof rerouted |

## Status

landed 20261014T140636-L-118125 2026-10-14 (merge of deliver/P3/Sheaf.AlgebraicGeometry.FlatTelescopeConeNormalizationDescent)
