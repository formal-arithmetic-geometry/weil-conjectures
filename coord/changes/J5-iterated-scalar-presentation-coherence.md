# scalarModelIteratedStrictCalculation

## Reason

Landing return af4aa4783 identified a newly proved consumer of the changed scalar
normalization interface. Its old proof applies bEL.normalization to arbitrary
e without a whole-system coherence witness. CoefficientReductionPresentation
only fixes e after finite derived evaluation, which is conservative but not
faithful; it cannot supply that witness. The tensor identification q and its
generator formula do not mention e, and cannot fix an invisible twist of e.
Thus this is an explicit correction to an intermediate statement, not a
proof-only adaptation or a claim to prove the old arbitrary-presentation version.
The same missing-coherence defect and edge test are documented in
J5-scalar-presentation-coherence.md. That record's derived-complete invisible-twist
example applies to the endpoint presentation here too. In the identity-coefficient
case the intermediate statement would otherwise assert its normalization for
every such twist. STATEMENT-DISPUTED: the old arbitrary-presentation form.

The module is unclaimed in the current local mirror; its proof was delivered by
E9 and its original statement by D2. Under the stage-3 unclaimed-module repair
rule, add the existing IsIntegralComparisonPresentationCoherent hypothesis and
pass it to normalization. The complete conclusion, other hypotheses, public name, visibility, imports and
all remaining proof lines stay identical. The corrected module compiles with ScalarModelAssociativity, ScalarModelUnit
and the unchanged direct whole-counit importer (exit 0; 58.0 s, 16.3 s,
37.6 s, 41.3 s respectively). A 61.3-second initial compile required adding
coefficientConstantTowerLimit and completedOrdinaryScalarComplex to its existing
local irreducibility list. This local optimization changes no exported attribute
or body; final source has no profiling options. The separate unit proof edit
only passes its already available coherence witness. This packet
makes the statement change explicit for independent review. The only caller is
ScalarModelAssociativity, already in this delivery: it has hcoh from
coherentPrimitiveReductionPresentation and now passes it to the calculation.
The parent associativity statement is unchanged. No target statement changes,
no blueprint unit is bypassed, and no hole is added or removed by this repair.

The zero complex, identity/repeated coefficient embeddings, empty schemes and
all flat-term K-flat good inputs admit canonical coherent presentations. No
geometric, boundedness or Tor-amplitude restriction is introduced into the parent.

## Old

```lean
theorem scalarModelIteratedStrictCalculation
    (SE : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (bEL : IntegralComparisonScalarModel l E L ι X SE ρL)
    (bLF : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj)
    (hC : CoefficientReductionPresentation l E X SE.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ)
    (q : (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E F (j.comp ι) X).obj P.obj)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l F X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l F X
            ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E F (j.comp ι) X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E F (j.comp ι) X n (P.obj.X i) U s x) :
    ((completedDerivedScalarExtension l L F j X).map
        ((completedScalarComparison l E L ι X).app (DerivedCategory.Q.obj P.obj)) ≫
      (completedScalarComparison l L F j X).app
        ((integralScalarExtensionOfUniverses l E L ι X).obj (DerivedCategory.Q.obj P.obj)) ≫
      (integralScalarExtensionOfUniverses l L F j X).map
        (bEL.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
      bLF.realization.hom.app
        ((coefficientSequenceLimit l L X).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj (DerivedCategory.Q.obj P.obj))))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSystemScalarComposition l E L F ι j X).hom.app
          (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l E F (j.comp ι) X).map e.hom) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).ε.app C) ≫
      (integralComparisonRoosBridge l F X ρF _).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
    (completedDerivedScalarExtension l L F j X).map
        (completedScalarCounit l E L ι X P.obj) ≫
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫
      DerivedCategory.Q.map
        ((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
          (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P.obj) ≫
      DerivedCategory.Q.map
        ((completedScalarChainComparison l E F (j.comp ι) X).app P.obj)
```

## New

```lean
theorem scalarModelIteratedStrictCalculation
    (SE : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (bEL : IntegralComparisonScalarModel l E L ι X SE ρL)
    (bLF : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj)
    (hC : CoefficientReductionPresentation l E X SE.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ)
    (hcoh : IsIntegralComparisonPresentationCoherent l E X SE P.obj C e κ)
    (q : (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E F (j.comp ι) X).obj P.obj)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l F X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l F X
            ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E F (j.comp ι) X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E F (j.comp ι) X n (P.obj.X i) U s x) :
    ((completedDerivedScalarExtension l L F j X).map
        ((completedScalarComparison l E L ι X).app (DerivedCategory.Q.obj P.obj)) ≫
      (completedScalarComparison l L F j X).app
        ((integralScalarExtensionOfUniverses l E L ι X).obj (DerivedCategory.Q.obj P.obj)) ≫
      (integralScalarExtensionOfUniverses l L F j X).map
        (bEL.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
      bLF.realization.hom.app
        ((coefficientSequenceLimit l L X).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj
            (SE.reduction.obj (DerivedCategory.Q.obj P.obj))))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSystemScalarComposition l E L F ι j X).hom.app
          (SE.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l E F (j.comp ι) X).map e.hom) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l E F (j.comp ι) X).ε.app C) ≫
      (integralComparisonRoosBridge l F X ρF _).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
    (completedDerivedScalarExtension l L F j X).map
        (completedScalarCounit l E L ι X P.obj) ≫
      completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫
      DerivedCategory.Q.map
        ((CompletedLineTensor.scalarAssociatorComplex l E X L ι F j
          (CompletedLineTensor.associatorData l E X L ι F j).sheaf).hom.app P.obj) ≫
      DerivedCategory.Q.map
        ((completedScalarChainComparison l E F (j.comp ι) X).app P.obj)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation | unclaimed in current local mirror; E9 proof/D2 statement | Explicitly requires whole-system coherence and passes it to bEL.normalization. |
| Sheaf.TraceFormula.ScalarModelAssociativity | D2 (previous return) | Only caller and only direct importer: passes its existing hcoh; public theorem unchanged. |

## Status

landed 20261027T180651-L-3888388 2026-10-27 (merge of deliver/J5/Sheaf.Paper.AmbientComparisonSystemExistence)
