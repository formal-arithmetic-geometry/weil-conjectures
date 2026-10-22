# CategoryTheory.ringedOrdinaryEvaluation_localization

## Reason

Complete the unsigned ordinary evaluation and fixed-augmentation localization proof in
`Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization`. The added section commands,
private notation and local attributes cause stage-3 preflight to request this record.
All seven existing public signatures, all six existing definition bodies, and both
public imports are unchanged. No adopted source-library file is modified.

The context supplies cached instances for the ordinary complex tensor construction.
Local irreducibility prevents repeated unfolding of the Hom, tensor, complex-category
and quasi-isomorphism constructions during instance matching. The proof uses their
existing APIs. Every new helper is private and proved; no global instance or simp rule
is added. Proof-only imports are private.

## Old

Original theorem signature, verbatim:

```lean
theorem ringedOrdinaryEvaluation_localization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃ aEF : (coefficientTotalTensor.{u, c, v} J R).obj
        (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
          homComplex (R := R) E F,
      RingedOrdinaryEvaluationFormula.{c, v, u} J R E F aEF ∧
      (∀ bEF, RingedOrdinaryEvaluationFormula.{c, v, u} J R E F bEF → bEF = aEF) ∧
      ∀ (hF : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F)
        (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))),
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) →
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E F) →
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) ∧
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E F) ∧
        (T.iso J R S F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) hF hD).hom ≫
          S.tensor.map (𝟙 (DerivedCategory.Q.obj F),
            ringedOrdinaryHomComparison.{c, v, u, w} J R E
              (ringedTensorUnitComplex.{c, v, u} J R)) ≫
          ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
            (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map aEF ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F
```

The derived definitions and theorem shared the existing `HasDerivedCategory` variable.
There was no intervening ordinary-evaluation proof section or local monoidal context.

## New

The theorem signature is unchanged, verbatim:

```lean
theorem ringedOrdinaryEvaluation_localization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (E F : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) :
    ∃ aEF : (coefficientTotalTensor.{u, c, v} J R).obj
        (F, homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ⟶
          homComplex (R := R) E F,
      RingedOrdinaryEvaluationFormula.{c, v, u} J R E F aEF ∧
      (∀ bEF, RingedOrdinaryEvaluationFormula.{c, v, u} J R E F bEF → bEF = aEF) ∧
      ∀ (hF : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F)
        (hD : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))),
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) →
        QuasiIso (ringedHomAugmentationMap.{c, v, u} J R E F) →
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E
          (ringedTensorUnitComplex.{c, v, u} J R)) ∧
        IsIso (ringedOrdinaryHomComparison.{c, v, u, w} J R E F) ∧
        (T.iso J R S F
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) hF hD).hom ≫
          S.tensor.map (𝟙 (DerivedCategory.Q.obj F),
            ringedOrdinaryHomComparison.{c, v, u, w} J R E
              (ringedTensorUnitComplex.{c, v, u} J R)) ≫
          ringedDualTensorHom.{c, v, u, w} J R S coh.unitIso
            (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
        DerivedCategory.Q.map aEF ≫ ringedOrdinaryHomComparison.{c, v, u, w} J R E F
```

`section DerivedDefinitions` now scopes the existing derived-definition variable,
ending after the unchanged `ringedDualTensorHom` body. The private proof context begins
as follows, verbatim:

```lean
section OrdinaryHelpers

set_option linter.unusedSectionVars false

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

open MonoidalCategory CochainComplex

attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local instance 1000] RingedDerivedNative.baseLimits RingedDerivedNative.baseColimits
  RingedDerivedNative.gradedTensor RingedDerivedNative.gradedTensorFour
  RingedDerivedNative.gradedTensorLeft RingedDerivedNative.gradedTensorRight
  RingedDerivedNative.baseClosed RingedDerivedNative.auxTensorLeftColimits
  RingedDerivedNative.auxTensorRightColimits
attribute [local instance] SheafOfModules.cochainModulesPreadditive
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option hygiene false in
local notation "Mod" => RingedDerivedNative.Modules.{c, v, u} J R
```

Within this section the following local irreducibility commands occur; intervening
proved declarations are omitted from this inventory:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor

attribute [local irreducible] ordinaryCurry

attribute [local irreducible] ordinaryAssociator ordinaryRightUnitor
  coefficientTotalTensor coefficientTensorGenerator

attribute [local irreducible] ordinaryEvaluation

attribute [local irreducible] coefficientHomResolution coefficientHomResolutionIso

attribute [local irreducible] HomologicalComplex.quasiIso
  HomologicalComplex.instCategory Preadditive.preadditiveHasZeroMorphisms

attribute [local irreducible] CoefficientClosedStructure.tensor
  CoefficientClosedStructure.transpose ringedOrdinaryHomComparison ringedDualTensorHom
  derivedInternalHomOfUniverses CoefficientTensorModels.iso ringedTensorUnitComplex
```

The nested `DerivedAdjunction` section introduces only local `Der` and `RHom` notation
and an explicit closed-structure variable for its private proofs. Transparency options
are scoped to the individual helper theorems that require them. `end OrdinaryHelpers`
ends the proof context before the original theorem, whose `HasDerivedCategory` variable
is then reintroduced. File options and private local notation do not install commands
in importing modules. Existing declaration attributes and public imports are preserved.

The new proof constructs evaluation using the existing unsigned chain-level currying
API, proves its formula and uniqueness, then compares two normalized inverse transposes
using the supplied tensor coherence and cancels the resolution isomorphism.
No target statement or definition meaning changes, so no statement review is reopened.

## Users

`python3 tools/downstream.py
Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization --uses
CategoryTheory.ringedOrdinaryEvaluation_localization` reports zero downstream modules.
Its textual declaration search finds only the assigned module. Searches of both Lean
roots also find no importer of the assigned module. No consumer adaptation is needed.
DAG parents and the unit route retain this node and its unchanged statement.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | C9 | Complete proof; unchanged public signatures and definitions; local proof context only. |

The complete current module compiled successfully through `lcompile.py` in 54.8 seconds.

## Status

landed 20261022T013400-L-3558675 2026-10-22 (merge of deliver/C9/Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization)
