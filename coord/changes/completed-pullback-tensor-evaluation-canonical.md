# WeilConjectures.completedPullbackTensor_evaluation_cube_model

## Reason

The node already specifies the canonical finite comparison, but the Lean theorem
quantifies an arbitrary natural isomorphism `ν` without any normalization relating
it to the finite pullback tensor construction. Pasting the other faces cannot
identify this arbitrary map. For a nonzero tensor in odd characteristic, multiplying
the canonical comparison by minus one changes the right-hand path while leaving
all hypotheses fixed. The current queue marks the item disputed for this route.
The repair specializes the conclusion to the canonical comparison stated by the
node. No target statement or definition changes. The sole parent already supplies
this canonical comparison, and its public statements remain verbatim.

## Old

```lean
theorem completedPullbackTensor_evaluation_cube_model {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (ν : finiteIntrinsicDerivedTensor l E Y n ⋙ finiteDerivedPullback l E n f ≅
      (finiteDerivedPullback l E n f).prod (finiteDerivedPullback l E n f) ⋙
        finiteIntrinsicDerivedTensor l E X n)
    (hn : CoefficientEvaluationTensorNormalization l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction)
    (hx : CoefficientEvaluationTensorNormalization l E X
      (pullbackTensorCalculus l E X).toCoefficientDerivedSystemReduction)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
      ν.hom.app ((coefficientSequenceDerivedEvaluation l E Y n).obj M,
        (coefficientSequenceDerivedEvaluation l E Y n).obj N)
```

## New

```lean
theorem completedPullbackTensor_evaluation_cube_model {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (c : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
    (hc : ∀ (A : normalizedDVRModules l E Y n) (U : Y.ProEt)
      (x : A.val.obj (op U)),
      (c.hom.app A).val.app (op ((proEtaleBaseChange f).obj U))
        (((coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1}
            (finiteCoefficientRing l E (n + 1))))).unit.app A).val.app (op U) x) =
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).unit.app A).val.app (op U) x)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f)
    (he : ∀ A : CochainComplex (coefficientSequenceModules l E Y) ℤ,
      e.hom.app (DerivedCategory.Q.obj A) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app A) ≫
        (sfIntrinsicPullback
          (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
        ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app A) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj A)))
    (hn : CoefficientEvaluationTensorNormalization l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction)
    (hx : CoefficientEvaluationTensorNormalization l E X
      (pullbackTensorCalculus l E X).toCoefficientDerivedSystemReduction)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) Q) :
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M, N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (e.hom.app M)
          (e.hom.app N)) =
    e.hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M, N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M, N)) ≫
      (finitePullbackTensorConstructionIso l E f n).hom.app
      ((coefficientSequenceDerivedEvaluation l E Y n).obj M,
        (coefficientSequenceDerivedEvaluation l E Y n).obj N)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPullbackTensorEvaluationCube | Q1 | Repair the unconstrained comparison and supply the categorical transport proof. |
| Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives | unclaimed | Remove the now-superfluous canonical-comparison argument at the sole call; keep every signature unchanged. |

The direct-import and declaration-use searches both found only the listed parent.
Its importers see the same statements. No adopted source-library file changes.
The repaired cube and the adapted parent were compiled in import order against
the delivered model-diagonal lemma: 37.5 s and 15.5 s respectively, with no errors
or warnings. The parent keeps the same statement and uses the same canonical
finite comparison after its redundant argument is removed. The final import-order
check compiled all fourteen delivered files, each within 60 s, with no errors or
warnings. A fresh server check still finds the parent unclaimed.

## Status

landed 20261027T234142-L-15064 2026-10-27 (merge of deliver/Q1/Sheaf.Paper.CompletedPullbackTensorEvaluationCube)
