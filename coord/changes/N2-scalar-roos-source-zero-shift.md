# scalarModelRoosZeroLift source zero-shift repair

## Reason

Three successive intermediate splits dropped the source zero-shift hypothesis on f. Their coordinate predicate sees only the unshifted product projection. A shifted lim^1 class can remain invisible to it. Restore the hypothesis already present in the outer scalarModelRoosZeroLift_existence theorem, and use the proved strict core with that hypothesis. The original unrestricted assertions are not counted as proved. No definition or Challenge target changes.

## Old

ScalarModelRoosZeroLiftFactorizationFromCoordinates

```lean
theorem scalarModelRoosZeroLift_factorization_from_coordinates
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D)
    (hh : scalarModelRoosZeroLiftZero l E L F ι j X SL P D h)
    (hcoord : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h) :
    ((completedDerivedScalarExtension l L F j X).map
          (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
        (completedScalarComparison l L F j X).app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        b.realization.hom.app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonDerivedSequenceScalar l L F j X).map
            (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
        (integralComparisonRoosBridge l F X ρF _).hom =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h)
```

ScalarModelRoosZeroLiftFactorizationExistence

```lean
theorem scalarModelRoosZeroLift_factorization_exists
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor) :
    ∃ h : scalarModelRoosZeroLiftType l E L F ι j X SL P D,
      scalarModelRoosZeroLiftZero l E L F ι j X SL P D h ∧
      scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h ∧
      ((completedDerivedScalarExtension l L F j X).map
          (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
        (completedScalarComparison l L F j X).app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        b.realization.hom.app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonDerivedSequenceScalar l L F j X).map
            (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
        (integralComparisonRoosBridge l F X ρF _).hom =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h)
```

ScalarModelRoosZeroLiftFactorization

```lean
theorem scalarModelRoosZeroLift_factorization
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D)
    (hh : scalarModelRoosZeroLiftZero l E L F ι j X SL P D h)
    (hcoord : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h) :
    scalarModelRoosZeroLiftFactorization l E L F ι j X SL ρL ρF b P D f h
```

## New

ScalarModelRoosZeroLiftFactorizationFromCoordinates

```lean
theorem scalarModelRoosZeroLift_factorization_from_coordinates
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D)
    (hh : scalarModelRoosZeroLiftZero l E L F ι j X SL P D h)
    (hcoord : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h) :
    ((completedDerivedScalarExtension l L F j X).map
          (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
        (completedScalarComparison l L F j X).app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        b.realization.hom.app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonDerivedSequenceScalar l L F j X).map
            (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
        (integralComparisonRoosBridge l F X ρF _).hom =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h)
```

ScalarModelRoosZeroLiftFactorizationExistence

```lean
theorem scalarModelRoosZeroLift_factorization_exists
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0) :
    ∃ h : scalarModelRoosZeroLiftType l E L F ι j X SL P D,
      scalarModelRoosZeroLiftZero l E L F ι j X SL P D h ∧
      scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h ∧
      ((completedDerivedScalarExtension l L F j X).map
          (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
        (completedScalarComparison l L F j X).app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        b.realization.hom.app
          ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonDerivedSequenceScalar l L F j X).map
            (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
        (coefficientSequenceLimit l F X).map
          ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
        (integralComparisonRoosBridge l F X ρF _).hom =
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h)
```

ScalarModelRoosZeroLiftFactorization

```lean
theorem scalarModelRoosZeroLift_factorization
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D)
    (hh : scalarModelRoosZeroLiftZero l E L F ι j X SL P D h)
    (hcoord : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h) :
    scalarModelRoosZeroLiftFactorization l E L F ι j X SL ρL ρF b P D f h
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationFromCoordinates | N2 | Assigned theorem: source hf restored, strict coordinates proved, target-system normalization separated. |
| Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence | unclaimed | Signature gains hf and forwards it to the repaired theorem; uses the proved core, removing the arbitrary-source strict-existence import. |
| Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization | unclaimed | Signature gains hf and forwards it to factorization_exists; existing uniqueness proof retained. |
| Sheaf.TraceFormula.ScalarModelRoosZeroLiftExistence | unclaimed | Signature unchanged: passes its existing hf directly to factorization_from_coordinates, removing the duplicate factorization wrappers from the target route. |

The declaration-use searches have exactly the three successive callers above. Every direct importer of a changed existing signature is included and compiled in dependency order. The unchanged outer existence interface preserves its further consumers. Claims were checked against current server records on 2026-10-28. The removed StrictExistence dependency is held by N3; that module is not edited or withdrawn.

The target-system normalization is now stated in Sheaf.TraceFormula.ScalarModelRoosCounitNormalization as scalarModelRoos_counit_normalization. It is a public, named remaining theorem, with its own node and proof plan. This is a decomposition, not an assertion that normalization has been proved.

## Status

landed 20261028T055724-L-801094 2026-10-28 (merge of deliver/N2/Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationFromCoordinates)
