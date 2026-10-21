# WeilConjectures.SemilinearSections.Geometry

## Reason

The interface describes the actual termwise inverse image on strict semilinear systems,
but it specified evaluation only on component objects and morphisms. Its existing
normalizations did not explicitly state the horizontal transition square needed to
localize that construction. The theorem `semilinearDerivedSections` produces a geometry
with a derived pull-transition condition; it does not give that condition for the arbitrary
`G : Geometry` quantified over in this item. Add `ordinaryPullTransition`, the ordinary
horizontal-map normalization from Zheng Construction 4.1 and Lemma 4.10.

This is not the theorem's derived push-transition conclusion or its resolution formula:
it concerns an ordinary input system and its exact inverse image, with no derived
right adjoints, coefficient extension, resolutions, or scalar transposes. Localizing
it and taking mates supplies the derived transition argument in this delivery.
Equal indices, zero systems, zero rings, and non-flat coefficient transitions satisfy
the ordinary equation without additional hypotheses.

## Old

```lean
structure Geometry extends GeometryBase.{c, v, r} J B τ J' uInv uPush adjSet where
  /-- The same derived adjunction at each level. -/
  derivedLevelAdjunction : ∀ n : ℕ,
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules) ⊣ (levelPush n).rightDerivedFunctor
  /-- The level derived adjunction is the canonical localization of the actual
  ordinary module adjunction. This equality fixes its hom-equivalence, so a
  sign-twisted choice cannot satisfy the interface. -/
  derivedLevelAdjunction_canonical : ∀ n : ℕ,
    derivedLevelAdjunction n =
      (levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
  /-- The system derived adjunction is the canonical localization of the
  ordinary system adjunction. -/
  derivedAdjunction_canonical :
    adjunction = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  /-- Exact inverse image evaluation. -/
  pullEvaluation : ∀ n : ℕ,
    pull.mapDerivedCategory ⋙ e.{c, v, max c v r} J' coefficients coefficientTransition n ≅
      e.{c, v, max c v r} J B τ n ⋙ (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules)
  /-- Derived direct-image evaluation; no K-injective evaluation assumption is made. -/
  pushEvaluation : ∀ n : ℕ,
    push.rightDerivedFunctor ⋙ e.{c, v, max c v r} J B τ n ≅
      e.{c, v, max c v r} J' coefficients coefficientTransition n ⋙ (levelPush
        n).rightDerivedFunctor
  /-- The evaluation identifications respect the actual adjunction units. -/
  unit_evaluation : ∀ (n : ℕ) (M : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J B τ n).map (adjunction.unit.app M) ≫
        (pushEvaluation n).hom.app (pull.mapDerivedCategory.obj M) ≫
        (levelPush n).rightDerivedFunctor.map ((pullEvaluation n).hom.app M) =
      (derivedLevelAdjunction n).unit.app ((e.{c, v, max c v r} J B τ n).obj M)
  /-- The evaluation identifications respect the actual adjunction counits. -/
  counit_evaluation : ∀ (n : ℕ)
    (N : DS.{c, v, max c v r} J' coefficients coefficientTransition),
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).map ((pushEvaluation n).hom.app N) ≫
        (derivedLevelAdjunction n).counit.app
          ((e.{c, v, max c v r} J' coefficients coefficientTransition n).obj N) =
      (pullEvaluation n).inv.app (push.rightDerivedFunctor.obj N) ≫
        (e.{c, v, max c v r} J' coefficients coefficientTransition n).map (adjunction.counit.app N)
  /-- The coefficient tensor/inverse-image comparison whose mate is b. -/
  coefficientPullback : ∀ {m n : ℕ} (h : n ≤ m),
    (Data.scalar.{c, v, r} A h).T ⋙
        ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules) :
          D.{c, v, max c v r} J (B n) ⥤ D.{c, v, max c v r} J' (coefficients n)) ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B m)
          (coefficients m) (inverseImage m).modules) :
        D.{c, v, max c v r} J (B m) ⥤ D.{c, v, max c v r} J' (coefficients m)) ⋙
          (Data.scalar.{c, v, r} target h).T
  /-- The canonical tensor comparison for inverse image of systems. -/
  tensorPullback : A.closed.tensor ⋙ pull.mapDerivedCategory ≅
    (pull.mapDerivedCategory.prod pull.mapDerivedCategory) ⋙ target.closed.tensor

  /-- Tensor/inverse-image comparison at each actual coefficient level. -/
  levelTensorPullback : ∀ n : ℕ,
    (A.levelClosed n).tensor ⋙
        derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).prod
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules)) ⋙ (target.levelClosed n).tensor
  /-- The tensor comparison evaluates to the specified level comparison. -/
  tensorPullback_evaluation : ∀ (n : ℕ) (M P : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J' coefficients coefficientTransition n).map
        (tensorPullback.hom.app (M, P)) ≫
        (target.tensorEvaluation n).hom.app
          (pull.mapDerivedCategory.obj M, pull.mapDerivedCategory.obj P) ≫
        (target.levelClosed n).tensor.map
          (Prod.mkHom ((pullEvaluation n).hom.app M) ((pullEvaluation n).hom.app P)) =
      (pullEvaluation n).hom.app (A.closed.tensor.obj (M, P)) ≫
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).map
            ((A.tensorEvaluation n).hom.app (M, P)) ≫
        (levelTensorPullback n).hom.app
          ((e.{c, v, max c v r} J B τ n).obj M, (e.{c, v, max c v r} J B τ n).obj P)
  /-- The chosen ordinary realization acts as the identity on the actual
  component section carriers. This rules out twisting the evaluation by a sign. -/
  ordinaryPullEvaluation_sections : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : C'ᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).obj
      (pull.obj M)).val.obj U),
    HEq ((((ordinaryPullEvaluation n).hom.app M).val.app U) x) x
  /-- Ordinary direct image has its actual componentwise realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅ evaluation.{c, v, max c v r} J' coefficients
      coefficientTransition n ⋙ levelPush n
  /-- The ordinary push evaluation is the identity on the component carriers. -/
  ordinaryPushEvaluation_sections : ∀ (n : ℕ)
    (M : Systems.{c, v, max c v r} J' coefficients coefficientTransition) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((ordinaryPushEvaluation n).hom.app M).val.app U) x) x
  /-- The ordinary system unit is the level unit under these realizations. -/
  ordinary_unit_evaluation : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.unit.app M) ≫
      (ordinaryPushEvaluation n).hom.app (pull.obj M) ≫
      (levelPush n).map ((ordinaryPullEvaluation n).hom.app M) =
        (levelAdjunction n).unit.app ((evaluation.{c, v, max c v r} J B τ n).obj M)
  /-- On a K-injective target the derived Hom equivalence is the ordinary one. -/
  derivedLevel_transpose_model : ∀ (n : ℕ)
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (I : CochainComplex (Mod.{c, v, max c v r} J' (coefficients n)) ℤ)
    [I.IsKInjective]
    (f : ((inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    ((derivedLevelAdjunction n).homEquiv _ _)
        ((Functor.mapDerivedCategoryFactors (inverseImage n).modules).hom.app P ≫
          DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((((levelAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv P I) f) ≫
          ((levelPush n).rightDerivedFunctorObjQIso I).inv
  /-- The system derived adjunction is normalized before taking any evaluation. -/
  derived_transpose_model : ∀
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (I : CochainComplex (Systems.{c, v, max c v r} J' coefficients coefficientTransition) ℤ)
    [I.IsKInjective] (f : (pull.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    (adjunction.homEquiv _ _)
        ((Functor.mapDerivedCategoryFactors pull).hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I) f) ≫
          (push.rightDerivedFunctorObjQIso I).inv
  /-- Exact derived pull evaluation is the localization of its ordinary realization. -/
  pullEvaluation_model : ∀ n : ℕ,
    pullEvaluation n = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryPullEvaluation n) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
  /-- Restricting coefficient actions commutes with inverse image. -/
  restrictionPullback : ∀ {m n : ℕ} (h : n ≤ m),
    res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) ⋙ (inverseImage m).modules ≅
      (inverseImage n).modules ⋙ res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
        coefficients coefficientTransition h)
  /-- The ordinary restriction comparison is the identity on the inverse-image
  underlying sheaf; this excludes an unrelated scalar or sign automorphism. -/
  restrictionPullback_underlying : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J' (coefficients m)).map ((restrictionPullback h).hom.app M) ≫
      (inverseImage n).moduleUnderlying.hom.app M =
        (inverseImage m).moduleUnderlying.hom.app ((res.{c, v, max c v r} (coefficientMap.{c, v,
          max c v r} J B τ h)).obj M)
  /-- Coefficient pullback is the scalar-adjunction transpose of the localized
  identity-on-underlying-sheaves restriction comparison. -/
  coefficientPullback_transpose : ∀ {m n : ℕ} (h : n ≤ m)
    (P : D.{c, v, max c v r} J (B m)),
    ((target.scalar h).adjunction.homEquiv _ _) ((coefficientPullback h).inv.app P) =
      (derivedExact.{c, v, max c v r, c, v} J J' (B m) (coefficients m) (inverseImage
        m).modules).map
        ((A.scalar h).adjunction.unit.app P) ≫
      (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (restrictionPullback h) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app ((A.scalar h).T.obj P))
  /-- Level tensor pullback is fixed on the signed total K-flat representatives. -/
  levelTensorModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r} J J' (B n) (coefficients n) (inverseImage n).modules
      (A.levelClosed n) (target.levelClosed n) (A.levelTensorModels n)
        (target.levelTensorModels n) (levelTensorPullback n)
  /-- Its ordinary maps are the inverse images of pure tensors. -/
  levelTensor_pure : ∀ n : ℕ,
    InverseTensorPure.{c, v, r} J J' uInv (B n) (coefficients n) (inverseImage n)
      (levelTensorModel n).ordinary
  /-- The system comparison is localized on the system category itself. -/
  tensorModel : TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J)
    (coefficientSequenceTopology J') (systemRing.{c, v, max c v r} J B τ)
      (systemRing.{c, v, max c v r} J' coefficients coefficientTransition) pull A.closed
        target.closed
        A.tensorModels target.tensorModels tensorPullback
  /-- The ordinary system tensor map is fixed by ordinary, faithful evaluations. -/
  tensor_ordinary_evaluation : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).map
      (tensorModel.ordinary M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' coefficients coefficientTransition n (pull.obj M)
        (pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (coefficients n)
        ((ordinaryPullEvaluation n).hom.app M) ((ordinaryPullEvaluation n).hom.app N) =
      (ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J
          B τ) M N) ≫
      (inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      ((levelTensorModel n).ordinary ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom
```

## New

```lean
structure Geometry extends GeometryBase.{c, v, r} J B τ J' uInv uPush adjSet where
  /-- The same derived adjunction at each level. -/
  derivedLevelAdjunction : ∀ n : ℕ,
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules) ⊣ (levelPush n).rightDerivedFunctor
  /-- The level derived adjunction is the canonical localization of the actual
  ordinary module adjunction. This equality fixes its hom-equivalence, so a
  sign-twisted choice cannot satisfy the interface. -/
  derivedLevelAdjunction_canonical : ∀ n : ℕ,
    derivedLevelAdjunction n =
      (levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
  /-- The system derived adjunction is the canonical localization of the
  ordinary system adjunction. -/
  derivedAdjunction_canonical :
    adjunction = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  /-- Exact inverse image evaluation. -/
  pullEvaluation : ∀ n : ℕ,
    pull.mapDerivedCategory ⋙ e.{c, v, max c v r} J' coefficients coefficientTransition n ≅
      e.{c, v, max c v r} J B τ n ⋙ (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules)
  /-- Derived direct-image evaluation; no K-injective evaluation assumption is made. -/
  pushEvaluation : ∀ n : ℕ,
    push.rightDerivedFunctor ⋙ e.{c, v, max c v r} J B τ n ≅
      e.{c, v, max c v r} J' coefficients coefficientTransition n ⋙ (levelPush
        n).rightDerivedFunctor
  /-- The evaluation identifications respect the actual adjunction units. -/
  unit_evaluation : ∀ (n : ℕ) (M : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J B τ n).map (adjunction.unit.app M) ≫
        (pushEvaluation n).hom.app (pull.mapDerivedCategory.obj M) ≫
        (levelPush n).rightDerivedFunctor.map ((pullEvaluation n).hom.app M) =
      (derivedLevelAdjunction n).unit.app ((e.{c, v, max c v r} J B τ n).obj M)
  /-- The evaluation identifications respect the actual adjunction counits. -/
  counit_evaluation : ∀ (n : ℕ)
    (N : DS.{c, v, max c v r} J' coefficients coefficientTransition),
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).map ((pushEvaluation n).hom.app N) ≫
        (derivedLevelAdjunction n).counit.app
          ((e.{c, v, max c v r} J' coefficients coefficientTransition n).obj N) =
      (pullEvaluation n).inv.app (push.rightDerivedFunctor.obj N) ≫
        (e.{c, v, max c v r} J' coefficients coefficientTransition n).map (adjunction.counit.app N)
  /-- The coefficient tensor/inverse-image comparison whose mate is b. -/
  coefficientPullback : ∀ {m n : ℕ} (h : n ≤ m),
    (Data.scalar.{c, v, r} A h).T ⋙
        ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules) :
          D.{c, v, max c v r} J (B n) ⥤ D.{c, v, max c v r} J' (coefficients n)) ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B m)
          (coefficients m) (inverseImage m).modules) :
        D.{c, v, max c v r} J (B m) ⥤ D.{c, v, max c v r} J' (coefficients m)) ⋙
          (Data.scalar.{c, v, r} target h).T
  /-- The canonical tensor comparison for inverse image of systems. -/
  tensorPullback : A.closed.tensor ⋙ pull.mapDerivedCategory ≅
    (pull.mapDerivedCategory.prod pull.mapDerivedCategory) ⋙ target.closed.tensor

  /-- Tensor/inverse-image comparison at each actual coefficient level. -/
  levelTensorPullback : ∀ n : ℕ,
    (A.levelClosed n).tensor ⋙
        derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).prod
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules)) ⋙ (target.levelClosed n).tensor
  /-- The tensor comparison evaluates to the specified level comparison. -/
  tensorPullback_evaluation : ∀ (n : ℕ) (M P : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J' coefficients coefficientTransition n).map
        (tensorPullback.hom.app (M, P)) ≫
        (target.tensorEvaluation n).hom.app
          (pull.mapDerivedCategory.obj M, pull.mapDerivedCategory.obj P) ≫
        (target.levelClosed n).tensor.map
          (Prod.mkHom ((pullEvaluation n).hom.app M) ((pullEvaluation n).hom.app P)) =
      (pullEvaluation n).hom.app (A.closed.tensor.obj (M, P)) ≫
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).map
            ((A.tensorEvaluation n).hom.app (M, P)) ≫
        (levelTensorPullback n).hom.app
          ((e.{c, v, max c v r} J B τ n).obj M, (e.{c, v, max c v r} J B τ n).obj P)
  /-- The chosen ordinary realization acts as the identity on the actual
  component section carriers. This rules out twisting the evaluation by a sign. -/
  ordinaryPullEvaluation_sections : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : C'ᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).obj
      (pull.obj M)).val.obj U),
    HEq ((((ordinaryPullEvaluation n).hom.app M).val.app U) x) x
  /-- Ordinary direct image has its actual componentwise realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅ evaluation.{c, v, max c v r} J' coefficients
      coefficientTransition n ⋙ levelPush n
  /-- The ordinary push evaluation is the identity on the component carriers. -/
  ordinaryPushEvaluation_sections : ∀ (n : ℕ)
    (M : Systems.{c, v, max c v r} J' coefficients coefficientTransition) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((ordinaryPushEvaluation n).hom.app M).val.app U) x) x
  /-- The ordinary system unit is the level unit under these realizations. -/
  ordinary_unit_evaluation : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.unit.app M) ≫
      (ordinaryPushEvaluation n).hom.app (pull.obj M) ≫
      (levelPush n).map ((ordinaryPullEvaluation n).hom.app M) =
        (levelAdjunction n).unit.app ((evaluation.{c, v, max c v r} J B τ n).obj M)
  /-- On a K-injective target the derived Hom equivalence is the ordinary one. -/
  derivedLevel_transpose_model : ∀ (n : ℕ)
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (I : CochainComplex (Mod.{c, v, max c v r} J' (coefficients n)) ℤ)
    [I.IsKInjective]
    (f : ((inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    ((derivedLevelAdjunction n).homEquiv _ _)
        ((Functor.mapDerivedCategoryFactors (inverseImage n).modules).hom.app P ≫
          DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((((levelAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv P I) f) ≫
          ((levelPush n).rightDerivedFunctorObjQIso I).inv
  /-- The system derived adjunction is normalized before taking any evaluation. -/
  derived_transpose_model : ∀
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (I : CochainComplex (Systems.{c, v, max c v r} J' coefficients coefficientTransition) ℤ)
    [I.IsKInjective] (f : (pull.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    (adjunction.homEquiv _ _)
        ((Functor.mapDerivedCategoryFactors pull).hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I) f) ≫
          (push.rightDerivedFunctorObjQIso I).inv
  /-- Exact derived pull evaluation is the localization of its ordinary realization. -/
  pullEvaluation_model : ∀ n : ℕ,
    pullEvaluation n = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryPullEvaluation n) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
  /-- Restricting coefficient actions commutes with inverse image. -/
  restrictionPullback : ∀ {m n : ℕ} (h : n ≤ m),
    res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) ⋙ (inverseImage m).modules ≅
      (inverseImage n).modules ⋙ res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
        coefficients coefficientTransition h)
  /-- The ordinary restriction comparison is the identity on the inverse-image
  underlying sheaf; this excludes an unrelated scalar or sign automorphism. -/
  restrictionPullback_underlying : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J' (coefficients m)).map ((restrictionPullback h).hom.app M) ≫
      (inverseImage n).moduleUnderlying.hom.app M =
        (inverseImage m).moduleUnderlying.hom.app ((res.{c, v, max c v r} (coefficientMap.{c, v,
          max c v r} J B τ h)).obj M)
  /-- Termwise inverse image carries the horizontal transition of the actual
  system to the coefficient-restriction inverse image of that transition.
  This equation is imposed before taking complexes or localizing; specifying
  evaluation on component objects alone does not specify horizontal maps. -/
  ordinaryPullTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ),
    (transition.{c, v, max c v r} J' coefficients coefficientTransition h).app (pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
          coefficients coefficientTransition h)).map ((ordinaryPullEvaluation n).hom.app M) =
      (ordinaryPullEvaluation m).hom.app M ≫
        (inverseImage m).modules.map
          ((transition.{c, v, max c v r} J B τ h).app M) ≫
        (restrictionPullback h).hom.app ((evaluation.{c, v, max c v r} J B τ n).obj M)
  /-- Coefficient pullback is the scalar-adjunction transpose of the localized
  identity-on-underlying-sheaves restriction comparison. -/
  coefficientPullback_transpose : ∀ {m n : ℕ} (h : n ≤ m)
    (P : D.{c, v, max c v r} J (B m)),
    ((target.scalar h).adjunction.homEquiv _ _) ((coefficientPullback h).inv.app P) =
      (derivedExact.{c, v, max c v r, c, v} J J' (B m) (coefficients m) (inverseImage
        m).modules).map
        ((A.scalar h).adjunction.unit.app P) ≫
      (((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (restrictionPullback h) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app ((A.scalar h).T.obj P))
  /-- Level tensor pullback is fixed on the signed total K-flat representatives. -/
  levelTensorModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r} J J' (B n) (coefficients n) (inverseImage n).modules
      (A.levelClosed n) (target.levelClosed n) (A.levelTensorModels n)
        (target.levelTensorModels n) (levelTensorPullback n)
  /-- Its ordinary maps are the inverse images of pure tensors. -/
  levelTensor_pure : ∀ n : ℕ,
    InverseTensorPure.{c, v, r} J J' uInv (B n) (coefficients n) (inverseImage n)
      (levelTensorModel n).ordinary
  /-- The system comparison is localized on the system category itself. -/
  tensorModel : TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J)
    (coefficientSequenceTopology J') (systemRing.{c, v, max c v r} J B τ)
      (systemRing.{c, v, max c v r} J' coefficients coefficientTransition) pull A.closed
        target.closed
        A.tensorModels target.tensorModels tensorPullback
  /-- The ordinary system tensor map is fixed by ordinary, faithful evaluations. -/
  tensor_ordinary_evaluation : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).map
      (tensorModel.ordinary M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' coefficients coefficientTransition n (pull.obj M)
        (pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (coefficients n)
        ((ordinaryPullEvaluation n).hom.app M) ((ordinaryPullEvaluation n).hom.app N) =
      (ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J
          B τ) M N) ≫
      (inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      ((levelTensorModel n).ordinary ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom
```

## Users

`tools/downstream.py Sheaf.Paper.SemilinearGeometryDerived --uses Geometry` lists
the downstream modules and the following 14 modules mentioning Geometry. Source search
found no `Geometry.mk` application or structure literal supplying its normalization fields.
Thus no existing construction requires adaptation. All existing field signatures and
all existing theorem signatures stay verbatim. No source-library file is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NormalizedOperationSystemModels | unclaimed | OperationPullLaws and CoefficientsIdentified take Geometry as input; HasOperationSystemModels asserts existence of the canonical termwise model. No constructor literal; the ordinary equation holds for the intended model and preserves the operation assertions. |
| Sheaf.Paper.QuotientDiagramProjectionEvaluation | unclaimed | Presentation has a Geometry field and the theorem asserts a canonical quotient-diagram presentation exists. Its geometry is the termwise construction, which obeys the ordinary square. No constructor literal or adaptation; the projection and evaluation statements retain their meaning. |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.RingedCoefficientProjectionData | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.RingedCoefficientPullbackCoherence | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.RingedCoefficientPullbackComparison | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.RingedCoefficientPullbackShifts | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.RingedCommonQuotientPullbackComparison | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.SemilinearDerivedSections | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.SemilinearGeometryDerived | unclaimed | Repairs the ordinary transition normalization; no existing field changes. |
| Sheaf.Paper.SemilinearGeometryOps | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.SemilinearOperationsExistence | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.SystemNormalizedTensorClosure | unclaimed | Takes Geometry as input or quantifies over its existence; no constructor literal or adaptation. |
| Sheaf.Paper.SystemPushforwardRestrictionTransition | C5 | Uses the repaired transition square in the proof; theorem signature unchanged. |

The transitive consumers inherit the same intended geometric operations. Since this
repairs a definition reachable from the targets, the statement-meaning review for any
affected target must be reopened under AGENTS.md §4. No `Challenge.lean` declaration
is changed. DAG citers are audited in the definition node's `statement_change`.

## Status

landed 20261021T143849-L-14061 2026-10-21 (merge of deliver/C5/Sheaf.Paper.SystemPushforwardRestrictionTransition)

The preflight of 2026-10-21 found two consumers and one DAG citer added since the
initial audit. Both source modules have now been read and are included above; the
additional citer is included in the definition node's `statement_change.citers`.
