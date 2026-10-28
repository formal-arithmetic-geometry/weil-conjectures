# AlgebraicGeometry.ProEtale.KummerPureKernelNormalization

## Reason

Move the definition verbatim into Sheaf.Paper.KummerPureKernelNormalizationData,
which the assigned module publicly re-exports through its statement module. Its fully proved generic triangle
criterion is compiled there. Profiling found 17 seconds for this criterion and
48 seconds for its concrete specialization; explicit categorical APIs and folded
propositions had already removed the expensive concrete reassociation. Keeping
the two self-contained parts in separate modules satisfies the per-file limit.
No semantic definition, attribute, universe or public name changes.

## Old

```lean
@[irreducible] def KummerPureKernelNormalization
    {A B : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [Category B] [abB : Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)]
    (F : ∀ n, C n ⥤ B)
    (V : ∀ n, C n ⥤ A)
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop)
    (σ : ∀ n, V n ≅ F n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    : Prop :=
    ∀ (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    ∃ (roots : H ⋙ U ≅ rootsTower)
      (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
      (∀ n, rootNorm H roots n (t n)) ∧
      ∀ n, (η n).unit.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map b.hom ≫
        ((diagonalEvaluationForget U n).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        (((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).hom.app
          H)⟦(2 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map
          (U.map (t n).hom ≫ (σ n).inv.app (P n)))⟦(2 : ℤ)⟧' =
        -((κ n).hom⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
            ((DerivedCategory.singleFunctor A 0).obj ((V n).obj (P n))))
```

## New

The definition below is byte-for-byte identical; its module home changes and the
original module re-exports it.

```lean
@[irreducible] def KummerPureKernelNormalization
    {A B : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    [Category B] [abB : Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (ℓ : ℕ) (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U)
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)]
    (F : ∀ n, C n ⥤ B)
    (V : ∀ n, C n ⥤ A)
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop)
    (σ : ∀ n, V n ≅ F n ⋙ U) (η : ∀ n, DiagonalEvaluationUnit U ad D n)
    : Prop :=
    ∀ (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    ∃ (roots : H ⋙ U ≅ rootsTower)
      (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
      (∀ n, rootNorm H roots n (t n)) ∧
      ∀ n, (η n).unit.app (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧) ≫
        (diagonalEvaluationForget U n).mapDerivedCategory.map b.hom ≫
        ((diagonalEvaluationForget U n).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H) ≫
        (((diagonalEvaluationForget U n).mapDerivedCategorySingleFunctor 0).hom.app
          H)⟦(2 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A 0).map
          (U.map (t n).hom ≫ (σ n).inv.app (P n)))⟦(2 : ℤ)⟧' =
        -((κ n).hom⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).inv.app
            ((DerivedCategory.singleFunctor A 0).obj ((V n).obj (P n))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictKummerPureKernelNormalization | A7 | Re-exports the new home; unchanged hypotheses and definitionally equal conclusion. |
| Sheaf.Paper.StrictKummerUnitNormalization | unclaimed | Original source is compiled against the delivery; no adaptation intended. |

## Status

landed 20261028T020145-L-2471939 2026-10-28 (merge of deliver/A7/Sheaf.Paper.StrictKummerPureKernelNormalization)
