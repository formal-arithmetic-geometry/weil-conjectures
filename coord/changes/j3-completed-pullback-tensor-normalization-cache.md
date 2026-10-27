# Completed pullback tensor normalization predicates

## Reason

The unmodified selection definitions repeatedly type-checked large normalization
predicates. Named profiling measured about 2.3 seconds for the tensor selection,
2.5 seconds for derived evaluation, and 4 seconds for the quotient selection.
The parent exceeded the 60-second compile limit. The refactored parent compiles
cleanly in 45.2 seconds. Give these three predicates
names so their later occurrences share a small constant application. The named
predicates are locally irreducible while this module is elaborated; importers
retain their normal transparency. A delivery compile still measured 65 seconds,
so these local attributes prevent the remaining eager expansion.

## Old

The following theorem signatures contained the predicates inline. Their proofs
and sources are preserved; the first and third remain the same named holes.

```lean
theorem pullbackTensorIntegralTensorModel_existsUnique (W : Scheme.{u}) :
    ∃! e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        e.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
          (integralCompletedTensorComparison l E W).app (P,Q) ≪≫
            (pullbackTensorReferenceTensorModel l E W P Q).symm
```

```lean
theorem pullbackTensorDerivedEvaluation_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f,
      ∀ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P))
```

```lean
theorem pullbackTensorQuotient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f,
      ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _
            (pullbackTensorFiniteGood l E f m P hP)).hom ≫
          DerivedCategory.Q.map ((pullbackTensorQuotientComplex l E f h).hom.app P)
```

## New

Each definition below is the old predicate verbatim. Unfolding it restores the
old theorem signature definitionally. The selected isomorphisms, their full
normalization squares, and every target statement are unchanged. The proved
evaluation existence theorem starts by unfolding its named predicate and then
uses its existing proof. No theorem is weakened and no new hole is added. Local irreducibility on
`pullbackTensorIntegralTensorNormalization`,
`pullbackTensorDerivedEvaluationNormalization`, and
`pullbackTensorQuotientNormalization` affects only this file; no public
reducibility attribute changes.

```lean
/-- The full strict tensor-model normalization, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorIntegralTensorNormalization (W : Scheme.{u})
    (e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        e.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
          (integralCompletedTensorComparison l E W).app (P,Q) ≪≫
            (pullbackTensorReferenceTensorModel l E W P Q).symm

theorem pullbackTensorIntegralTensorModel_existsUnique (W : Scheme.{u}) :
    ∃! e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W,
      pullbackTensorIntegralTensorNormalization l E W e
```

```lean
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived in
attribute [local irreducible] pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic in
/-- The full cochain normalization of finite evaluation, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorDerivedEvaluationNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f) : Prop :=
  ∀ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P))

theorem pullbackTensorDerivedEvaluation_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f,
      pullbackTensorDerivedEvaluationNormalization l E f n e
```

```lean
/-- The full K-flat normalization of quotient pullback, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorQuotientNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m)
    (e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f) : Prop :=
  ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _
            (pullbackTensorFiniteGood l E f m P hP)).hom ≫
          DerivedCategory.Q.map ((pullbackTensorQuotientComplex l E f h).hom.app P)

theorem pullbackTensorQuotient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f,
      pullbackTensorQuotientNormalization l E f h e
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | J3 | Uses the named predicates to select the same uniquely normalized isomorphisms. |
| `Sheaf.SixFunctors.PrimitiveQuotientAugmentations` | unclaimed (done) | Applies the tensor normalization theorem; its old application unfolds the predicate. Compiled against the refactored parent without changing its source. |

The source search of both library roots found no other direct consumers of the
three refactored existence declarations. Existing selector signatures and their
data remain definitionally equal to their prior versions. No forced adaptation
is needed. No external source file is included as a change.

## Status

landed 20261026T070030-L-3344536 2026-10-26 (merge of deliver/J3/Sheaf.Paper.CompletedPullbackTensorComparison)
