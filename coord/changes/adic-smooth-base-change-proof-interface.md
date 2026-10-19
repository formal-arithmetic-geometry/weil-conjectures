# WeilConjectures.adicSmoothBaseChange proof interface

## Reason

The target proof requires private helper declarations over two extra universe parameters
and imports the coefficient realization and exact derived comparison modules. The stage-3
static checker classifies these local proof commands as changing the module interface. The
target theorem signature and all public definitions are unchanged.

## Old

```lean
universe u

import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.Paper.NormalizedEtaleOriginWitnesses
```

## New

```lean
universe u v w

import Sheaf.Paper.SbcFiniteExchangeCoefficientRealization
import Sheaf.Paper.PbcActualStrictPullback
import Sheaf.Paper.PbcActualRingedExchange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Sheaf.Paper.LevelwiseAdicTruncations
import Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange
import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
```

The newly added imports are proof-only and compile in the sandbox. Removed imports were
unused after the direct proof route was pruned; the finite site-comparison unit-route import is retained; the proof also uses the exact
comparison modules listed above. The private declarations `evaluations_conservative`,
`pbcCompleteReduction_conservative`, `fixedId`, `functionComparison`, `plus_of_map`,
`pbcConstructibleReduction_criterion`, `sbcFiniteSmoothExchange_isIso`, and
`finiteCohomology_property_of_iso` are all proved and occur only in the target module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothBaseChange | H3 | Proof imports and private helpers only; target signature unchanged. |
| Sheaf.Paper.ExchangeFunctoriality | NJ | Sees the same public target declaration and definitions. |

## Status

landed 20261019T231212-L-560654 2026-10-19 (merge of deliver/H3/Sheaf.Paper.AdicSmoothBaseChange)
