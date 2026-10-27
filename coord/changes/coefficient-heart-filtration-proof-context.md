# coefficientHeartFiltration proof context

## Reason

Preflight requested a change record for the added proof-context commands. They control
only elaboration of the new private proofs. In particular, the smallness proof prevents
unrelated Noetherian-category instance searches, and local irreducibility prevents
expansion of module-sheaf pullbacks and adjunctions. These commands do not change a
public signature, existing definition body, public import, or target meaning. The
smallness registration occurs after all existing definitions and is local.

## Old

The old proof context (verbatim):

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
```

There was no filtrationEssentiallySmall declaration or local transparency block.

## New

The same context is retained, with the following file-local elaboration option:

```lean
set_option backward.isDefEq.respectTransparency false
```

After the four unchanged existing definitions, the new proved helper and local
registration are:

```lean
private theorem filtrationEssentiallySmall
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C
attribute [local instance 2000] filtrationEssentiallySmall
```

The private support proofs use the following local transparency attributes:

```lean
attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction upperStar upperStarComp upperStarCongr
```

The private quotient proofs use:

```lean
attribute [local irreducible] CondensedRing.openImmersionLowerShriekUpperStarAdjunction
  CondensedRing.upperStarLowerStarAdjunction coefficientHeartLocallyClosedExtension
  CondensedRing.upperStar CondensedRing.openImmersionLowerShriek CondensedRing.lowerStar
  CondensedRing.upperStarComp CondensedRing.upperStarCongr
```

Some support proofs also locally set
`backward.isDefEq.respectTransparency.types false`. An unused-variable linter option is
scoped to the public theorem, whose constructibility hypothesis is stronger than this
filtration argument needs. None of these options or local attributes escapes the file.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientHeartFiltration --uses filtrationEssentiallySmall`
finds no consumer of the new private helper. The following downstream importers were
listed; their signatures and proof interfaces are unchanged and no adaptation is needed.
All existing definition bodies and the theorem signature were compared verbatim.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CoefficientHeartFiltration` | D2 | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | not adapted | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound` | not adapted | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | not adapted | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | not adapted | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | not adapted | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing` | not adapted | local proof context only; no interface change |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.AlgClTopologyMateHomBijection` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.AmbientIndDerivedSums` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.AmbientIndDerivedTriangulated` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.BrownHypothesesGeneration` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ClosedSupportConstructible` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.CoefficientHeart` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.CoefficientHeartGeneration` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.CoefficientHeartLisseExtensionConstructible` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.CoefficientHeartLocallyClosedExtension` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.CoefficientHeartSheafConeWitness` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.CondensedBoundedHomContinuity` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ConstructibleCompactness` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ConstructibleCompactnessBounded` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ConstructibleExtContinuity` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ConstructibleHomContinuityDevissage` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ContinuousAlgClFiniteStageDevissage` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ContinuousQbarNormalizedSheafFiltration` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DetIndHeartIISums` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientCategory` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientExchange` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientMaps` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientPullback` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientReference` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientScalars` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerCoefficients` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerLimit` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerTrace` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerTraceLimit` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerTraceModels` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FiniteStageSupportedGeneration` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FiniteWindow` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FiniteWindowBounded` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FiniteWindowUnbounded` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FormalClosedSupport` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FormalClosedSupportII` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.FormalClosedSupportIILimits` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.GeometricCondensedFiniteScalarModel` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IndConstructibleExtensions` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IndConstructibleFilteredColimits` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IndHeartCanonicalPresentation` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IndHeartFullFaithfulness` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IndHeartIIVanishing` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IndHeartKernelsCokernels` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralConstantModelHeart` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralConstructibleCompactness` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralConstructibleExt` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralConstructibleHeart` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralHeartDualizable` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralHeartLocalModel` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralHeartRealizationExact` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralHeartResidueDual` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralIndConstructibleHeartClosure` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralIndConstructibleStability` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralIndHeartRealization` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralIndLowerTail` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralModels` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralStratumExtBound` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralTensorProduct` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralTensorPullback` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.IntegralWindowCoproductComparison` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.LatticeSubquotientFiltration` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.LatticeSupportedHomFiniteComparison` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.NativeAdicCompactSupportSums` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.NormalizedInternalSupportScalars` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ProjectiveDiagonalPullback` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ProperHeartBoundLattice` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.ProperHeartBoundReduction` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.RationalClosedSupportConstructible` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.RationalLocalizedHom` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.RationalTatePullback` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.SupportedCommonFieldScalarData` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.SupportedCommonFieldScalarModels` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.SupportedLatticeHomReductionTower` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.UniformConstructibleExt` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.UniformConstructibleExtRational` | not adapted | local proof context only; no interface change |
| `Sheaf.Paper.UniformConstructibleExtTorsion` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctors.CommonFieldLatticeGenerators` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | not adapted | local proof context only; no interface change |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | not adapted | local proof context only; no interface change |
| `WeilConjectures` | not adapted | local proof context only; no interface change |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | not adapted | local proof context only; no interface change |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing` | not adapted | local proof context only; no interface change |

## Status

landed 20261023T230625-L-3452737 2026-10-23 (merge of deliver/D2/Sheaf.Paper.CoefficientHeartFiltration)
