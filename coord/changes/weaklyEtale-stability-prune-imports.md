# AlgebraicGeometry.weaklyEtale_stability imports

## Reason

The complete stability theorem follows from already proved Mathlib and source-library
instances available through `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`.
Neither its statement nor its proof uses principal ind-Zariski algebras or the separate
bundled ring stability theorem. Remove these unused imports and the corresponding DAG
proof dependency. All existing declaration signatures and definitions stay identical.
No target meaning changes.

`tools/downstream.py` reports 32 transitive downstream modules and zero uses there of
`Algebra.IsIndPrincipalZariski`. The eight direct importers import this module only for
proofs; their public statement dependencies already come from their own public imports.
The removed principal-Zariski reexport is unnecessary to their signatures. No downstream
source is changed or delivered. The global build will independently verify this import
pruning after landing.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.RingTheory.IndEtaleStability
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
```

## Users

Holder information is the shared claim snapshot at delivery preparation. No modules
below need adaptation; their statements are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | C8 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverExistence | C9 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.Projective | J1 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.RepleteOnContractible | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative | D5 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition | A9 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences | J2 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | E6 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit | D9 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties | Y5 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.CoefficientFiniteDescentSections | T7 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.CompletedCondensedCoefficients | G5 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.SmoothPurityCoefficientTowers | Y6 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | No use of the principal ind-Zariski definition; unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No use of the principal ind-Zariski definition; unchanged. |

## Status

landed 20261018T135913-L-2961675 2026-10-18 (merge of deliver/M6/Sheaf.AlgebraicGeometry.WeaklyEtaleStability)
