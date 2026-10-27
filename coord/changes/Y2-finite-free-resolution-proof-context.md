# Sheaf.Algebra.Homology.FiniteFreeResolutionTensor proof context

## Reason

Preflight requests a record for the new local attributes and proof elaboration
options. They prevent repeated unfolding of the concrete monoidal localization and
derived tensor during the signed-braiding and finite-free augmentation proofs.
All existing public signatures, public imports, and public definition bodies remain
verbatim. No target statement or definition meaning changes. No source-library file
is edited. The five cached structural instances are private proved lemmas registered
only with explicitly local instance attributes. Every new attribute is local.

## Old

Original options, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

The additional private helpers and local attributes below were absent. All four
original theorem signatures are preserved verbatim, with three proof bodies filled
and the main theorem's original hole retained.

## New

Current option and attribute commands, in file order:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local instance] coefficientSheafify coefficientLocalEquivalences
  coefficientCompose coefficientWeakSheafify coefficientMonoidal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local semireducible] ordinaryTensor
attribute [local instance 2000] tensorAdditive tensorObjAdditive tensorHasMapBifunctor
attribute [local instance 2000] tensorAdditive tensorObjAdditive tensorHasMapBifunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true in
attribute [local irreducible] derivedTensor representativeIso
```

The cached local structural instances are fully constructed from the existing
coefficient-universe API:

```lean
private theorem coefficientSheafify : HasSheafify J AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse (J := J)

private theorem coefficientLocalEquivalences : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse (J := J)

private theorem coefficientCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by infer_instance

private theorem coefficientWeakSheafify : HasWeakSheafify J AddCommGrpCat.{r} := by
  infer_instance

private theorem coefficientMonoidal :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).IsMonoidal :=
  SheafOfModules.cochainTensorLocalizationIsMonoidal R

attribute [local instance] coefficientSheafify coefficientLocalEquivalences
  coefficientCompose coefficientWeakSheafify coefficientMonoidal
```

The additional import `import all
Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat` is private and supplies its
proved finite-coproduct flatness helper and specified mono-cokernel augmentation.
There is no exported new instance or reducibility attribute. Public signatures and
public definition bodies are unchanged; consumers require no adaptation.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FiniteFreeResolutionTensor --uses
SheafOfModules.FiniteFreeResolution.coefficientSheafify` found no external use of
the private helper, and the transitive consumers below. Holders are read from the
current claim records. No consumer is changed.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor` | Y2 | Three proofs filled; local proof context added. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | W6 | Public interface unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | J6 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ContinuousAlgClOpenFiniteness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientCategory` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientExchange` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientMaps` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientPullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientReference` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientScalars` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalTowerCoefficients` | E5 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.DiagonalTowerTrace` | E7 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteModelSheafQuotientConstructible` | X7 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteScalarLocalModelComplete` | X9 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.GeneralLfpAdicInputWitness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralAdicInputNormalization` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralConstantModelHeart` | Z8 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralConstructibleHeart` | F5 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralGeneralLfpHomFiniteness` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartLocalModel` | Z9 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralModels` | J8 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralTensorPullback` | H4 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ProjectiveDiagonalPullback` | Q3 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ProperHeartBoundLattice` | G8 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.RationalLocalizedHom` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.RationalTatePullback` | C1 | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | S7 | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion` | unclaimed | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | N1 | Public interface unchanged; no adaptation required. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Public interface unchanged; no adaptation required. |

## Status

landed 20261023T132424-L-2269902 2026-10-23 (merge of deliver/Y2/Sheaf.Algebra.Homology.FiniteFreeResolutionTensor)
