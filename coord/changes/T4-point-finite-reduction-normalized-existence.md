# point_sections_finite_reduction_complex

## Reason

STATEMENT-DISPUTED: the previous statement demanded the normalized counit square for
every natural isomorphism family e. If l=3, n=j=1 and P is the degree-zero constant
rank-one module, multiply a comparison by -1. This is still a natural isomorphism but
cannot have the same normalized value on 1: the square would force 1=-1 in the residue
field of characteristic 3. The source and the parent theorem require construction of
one normalized family. The repaired intermediate theorem existentially constructs it,
together with its generator and counit compatibility. This proves the required parent
statement without changing that statement or any target signature.

## Old

```lean
theorem point_sections_finite_reduction_complex (_hl : IsUnit (l : k))
    (e : ∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙ pointFiniteReductionSections k l E j) :
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      ∀ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
        (_hbound : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (P.X q))
        (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pointFiniteReductionRingSheaf k l E n) (P.X q)),
      ∃ hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P),
      ∃ q :
        (pointFiniteReductionComplexTensor l E n j hjn).obj
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≅
        (pointFiniteReductionSectionComplex k l E j).obj
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P),
      (∀ (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
        (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)),
        q.hom.f a
          (pointFiniteReductionTensorGenerator l E n j hjn
            ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
          (b * c) • pointFiniteReductionSectionGenerator k l E n j hjn (P.X a) x) ∧
      (pointFiniteReductionModuleTensor l E n j hjn).map
          (pointFiniteReductionSectionFactors k l E n P).hom ≫
        (pointFiniteReductionModuleCounit l E n j hjn).app
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≫
        DerivedCategory.Q.map q.hom =
      (e n j hn hj hjn).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
        (pointFiniteReductionSections k l E j).map
          (pointFiniteReductionSheafCounit k l E n j hjn P) ≫
        (pointFiniteReductionSectionFactors k l E j
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P)).hom
```

## New

```lean
theorem point_sections_finite_reduction_complex (_hl : IsUnit (l : k)) :
    ∃ e : ∀ (n j : ℕ) (_hn : 1 ≤ n) (_hj : 1 ≤ j) (hjn : j ≤ n),
      (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSections k l E n ⋙ pointFiniteReductionModuleTensor l E n j hjn ≅
        (pointFiniteReductionBoundedAbove k l E n).ι ⋙
          pointFiniteReductionSheafTensor k l E n j hjn ⋙ pointFiniteReductionSections k l E j,
    ∀ (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n),
      ∀ (P : CochainComplex (pointFiniteReductionSheaves k l E n) ℤ)
        (_hbound : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (P.X q))
        (_hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pointFiniteReductionRingSheaf k l E n) (P.X q)),
      ∃ hP : pointFiniteReductionBoundedAbove k l E n (DerivedCategory.Q.obj P),
      ∃ q :
        (pointFiniteReductionComplexTensor l E n j hjn).obj
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≅
        (pointFiniteReductionSectionComplex k l E j).obj
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P),
      (∀ (a : ℤ) (b c : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E j))
        (x : (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).obj (P.X a)),
        q.hom.f a
          (pointFiniteReductionTensorGenerator l E n j hjn
            ((pointFiniteReductionSectionComplex k l E n).obj P) a b c x) =
          (b * c) • pointFiniteReductionSectionGenerator k l E n j hjn (P.X a) x) ∧
      (pointFiniteReductionModuleTensor l E n j hjn).map
          (pointFiniteReductionSectionFactors k l E n P).hom ≫
        (pointFiniteReductionModuleCounit l E n j hjn).app
          ((pointFiniteReductionSectionComplex k l E n).obj P) ≫
        DerivedCategory.Q.map q.hom =
      (e n j hn hj hjn).hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≫
        (pointFiniteReductionSections k l E j).map
          (pointFiniteReductionSheafCounit k l E n j hjn P) ≫
        (pointFiniteReductionSectionFactors k l E j
          ((pointFiniteReductionSheafComplexTensor k l E n j hjn).obj P)).hom
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointSectionsFiniteReduction | T4 | Assembly obtains the family and its normalized complex comparison from the repaired theorem, then adds the existing boundedness clause. Parent signature unchanged. |

The only DAG citer is lem-trf-point-sections-finite-reduction; its use holds and its proof
route is updated in the same packet. The iso theorem keeps its existing weaker existence
signature and is independently proved. No target statement changes. The old false
universal-e statement is not claimed as proved.

## Status

landed 20261021T061705-L-1812936 2026-10-21 (merge of deliver/T4/Sheaf.Paper.PointSectionsFiniteReduction)
