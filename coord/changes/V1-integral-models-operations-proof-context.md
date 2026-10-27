# IntegralModelsOperations proof elaboration context

## Reason

Prove the four clauses of `AlgebraicGeometry.ProEtale.CondensedRing.integralModelsOperations`.
The static interface comparison conservatively flags the changed command context.
Additional namespace opens are needed for exact functor cohomology, tensor and zero-object APIs.
Local irreducibility keeps the derived functors and support operations behind their comparison
isomorphisms during elaboration. The two backward elaboration options permit the established
module-object definitional comparisons. These commands affect this file's proofs only.
The public theorem signature, public imports and all existing definitions remain verbatim;
there are no new public declarations, exported instances, or target-definition changes.
No consumer needs adaptation and no target statement changes meaning.

## Old

```lean
set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] DerivedCategory.TStructure.t
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
```

After the private tensor helper, the following local attributes additionally prevent
unfolding the immersion functor and projection-map constructions:

```lean
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek supportPullback
attribute [local irreducible] closedSupportProjection openSupportProjection
```

## Users

All transitive importers reported by `tools/downstream.py` are listed below.
The textual `--uses` search for the full theorem name finds only its own declaration.
Holders are the current claim-record snapshot. Each consumer retains the same statement,
module data and exported instance environment; only the proof of an existing proposition
is completed. No consumer source is changed by this packet.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | E5 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | E7 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | Z9 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralModels | J8 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | V1 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | S8 | Unchanged public statement and public imports; local proof context only; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Unchanged public statement and public imports; local proof context only; no adaptation. |

## Status

landed 20261024T021041-L-2703178 2026-10-24 (merge of deliver/V1/Sheaf.Paper.IntegralModelsOperations)
