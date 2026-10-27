# WeilConjectures.CompactSupportCondensedRealization.shiftCoherentClauses

## Reason

The original definition repeatedly elaborates geometric and triangulation instances.
Reuse the supplied instances and explicitly bind composite shift instances to avoid
expanding the full models. The signature and nine mathematical clauses are retained.

## Old

```lean
def shiftCoherentClauses (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    [IsNoetherian X.scheme] [IsNoetherian Y.scheme]
    [Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n)]
    [Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))]
    (c : Compactification f)
    (sI : (integralSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sQ : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sX : (A.realization.atObject X).realization.functor.CommShift ℤ)
    (sY : (A.realization.atObject Y).realization.functor.CommShift ℤ)
    (sRX : (A.reduction X.scheme).reduction.CommShift ℤ)
    (sRY : (A.reduction Y.scheme).reduction.CommShift ℤ)
    (sLX : (coefficientSequenceLimit l E X.scheme).CommShift ℤ)
    (sLY : (coefficientSequenceLimit l E Y.scheme).CommShift ℤ)
    (sPX : (purCoefficientModel l E X.scheme).functor.CommShift ℤ)
    (sPY : (purCoefficientModel l E Y.scheme).functor.CommShift ℤ)
    (sS : (systemSupport l E c).CommShift ℤ)
    (sVX : (pbcRationalization X.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ)
    (sVY : (pbcRationalization Y.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ) : Prop := by
  letI := base_noetherian k X
  letI := base_noetherian k Y
  letI := pbcIntegralTriangulated l E X.scheme (base_dimension k X) (base_primeUnit l k X)
  letI := pbcIntegralTriangulated l E Y.scheme (base_dimension k Y) (base_primeUnit l k Y)
  letI := pbcRationalShift l E X.scheme (base_dimension k X) (base_primeUnit l k X)
  letI := pbcRationalShift l E Y.scheme (base_dimension k Y) (base_primeUnit l k Y)
  letI := (pbcRationalTriangulationData l E X.scheme
    (base_dimension k X) (base_primeUnit l k X)).choose_spec.choose_spec.2.choose_spec.choose
  letI := (pbcRationalTriangulationData l E Y.scheme
    (base_dimension k Y) (base_primeUnit l k Y)).choose_spec.choose_spec.2.choose_spec.choose
  letI := (A.realization.atObject X).encodingAdditive
  letI := (A.realization.atObject Y).encodingAdditive
  letI := (A.realization.atObject X).encodingInverseAdditive
  letI := (A.realization.atObject Y).encodingInverseAdditive
  letI := sI
  letI := sQ
  letI := sX
  letI := sY
  letI := sRX
  letI := sRY
  letI := sLX
  letI := sLY
  letI := sPX
  letI := sPY
  letI := sS
  letI := sVX
  letI := sVY
  letI : (reconstructedSystem l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ := by
    unfold reconstructedSystem
    infer_instance
  letI : (CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  letI : (CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  let I := integralSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let Q := rationalSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let hI : Prop := I.IsTriangulated
  let hRX : Prop := NatTrans.CommShift (A.reduction X.scheme).adjunction.counit ℤ
  let hRY : Prop := NatTrans.CommShift (A.reduction Y.scheme).adjunction.counit ℤ
  let hLimit : Prop := NatTrans.CommShift
    (limitPresentation l E c A.reduction (A.atCompactification X Y f c).integral).hom ℤ
  let hAlpha : Prop := NatTrans.CommShift
    (alpha l E c A.reduction (A.atCompactification X Y f c).integral) ℤ
  let hSX : Prop := NatTrans.CommShift (A.realization.atObject X).scalarExtension.hom ℤ
  let hSY : Prop := NatTrans.CommShift (A.realization.atObject Y).scalarExtension.hom ℤ
  let hReal : Prop := NatTrans.CommShift (A.atCompactification X Y f c).realization.hom ℤ
  exact hI ∧ hRX ∧ hRY ∧ hLimit ∧ hAlpha ∧ hSX ∧ hSY ∧ hReal ∧
        ∀ (K : CondensedERealization.Integral l E X.scheme) (n : ℤ),
          HEq ((Q.commShiftIso n).hom.app
              (ScalarLocalization.mk K))
            ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
              (I.commShiftIso n).hom.app K)
```

## New

```lean
def shiftCoherentClauses (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    [IsNoetherian X.scheme] [IsNoetherian Y.scheme]
    [Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n)]
    [Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))]
    (c : Compactification f)
    (sI : (integralSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sQ : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sX : (A.realization.atObject X).realization.functor.CommShift ℤ)
    (sY : (A.realization.atObject Y).realization.functor.CommShift ℤ)
    (sRX : (A.reduction X.scheme).reduction.CommShift ℤ)
    (sRY : (A.reduction Y.scheme).reduction.CommShift ℤ)
    (sLX : (coefficientSequenceLimit l E X.scheme).CommShift ℤ)
    (sLY : (coefficientSequenceLimit l E Y.scheme).CommShift ℤ)
    (sPX : (purCoefficientModel l E X.scheme).functor.CommShift ℤ)
    (sPY : (purCoefficientModel l E Y.scheme).functor.CommShift ℤ)
    (sS : (systemSupport l E c).CommShift ℤ)
    (sVX : (pbcRationalization X.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ)
    (sVY : (pbcRationalization Y.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ) : Prop := by
  let := (pbcRationalTriangulationData l E X.scheme
    (base_dimension k X) (base_primeUnit l k X)).choose_spec.choose_spec.2.choose_spec.choose
  let := (pbcRationalTriangulationData l E Y.scheme
    (base_dimension k Y) (base_primeUnit l k Y)).choose_spec.choose_spec.2.choose_spec.choose
  let := (A.realization.atObject X).encodingAdditive
  let := (A.realization.atObject Y).encodingAdditive
  let := (A.realization.atObject X).encodingInverseAdditive
  let := (A.realization.atObject Y).encodingInverseAdditive
  let := sI
  let := sQ
  let := sX
  let := sY
  let := sRX
  let := sRY
  let := sLX
  let := sLY
  let := sPX
  let := sPY
  let := sS
  let := sVX
  let := sVY
  let : (reconstructedSystem l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ := by
    unfold reconstructedSystem
    infer_instance
  let : (CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  let : (CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  let I := integralSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let Q := rationalSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let hI : Prop := I.IsTriangulated
  let hRX : Prop := NatTrans.CommShift (A.reduction X.scheme).adjunction.counit ℤ
  let hRY : Prop := NatTrans.CommShift (A.reduction Y.scheme).adjunction.counit ℤ
  let hLimit : Prop := NatTrans.CommShift
    (limitPresentation l E c A.reduction (A.atCompactification X Y f c).integral).hom ℤ
  let hAlpha : Prop := NatTrans.CommShift
    (alpha l E c A.reduction (A.atCompactification X Y f c).integral) ℤ
  let : ((A.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral ⋙
      (A.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let hSX : Prop := NatTrans.CommShift (A.realization.atObject X).scalarExtension.hom ℤ
  let hSY : Prop := NatTrans.CommShift (A.realization.atObject Y).scalarExtension.hom ℤ
  let hReal : Prop := NatTrans.CommShift (A.atCompactification X Y f c).realization.hom ℤ
  exact hI ∧ hRX ∧ hRY ∧ hLimit ∧ hAlpha ∧ hSX ∧ hSY ∧ hReal ∧
        ∀ (K : CondensedERealization.Integral l E X.scheme) (n : ℤ),
          HEq ((Q.commShiftIso n).hom.app
              (ScalarLocalization.mk K))
            ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
              (I.commShiftIso n).hom.app K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompactSupportCondensedRealization` | Y5 | The shift witness field uses the same signature and clauses. |

The declaration-use scan found no external direct user. The 19 transitive importers
retain the same exported interfaces. No consumer edit is included.

## Status

landed 20261025T144348-L-1233470 2026-10-25 (merge of deliver/Y5/Sheaf.Paper.CompactSupportCondensedRealization)
