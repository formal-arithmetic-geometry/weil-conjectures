# StrictTower proper/open calculus: proof route and local normalization settings

## Reason

The four alpha clauses follow from a common reverse-comparison cancellation
argument. alpha_cartesian and its existing private identity helper must follow
beta_open_comp, which the common factorization uses. Large concrete rewrite
motives expanded the derived functor data in the kernel; explicit functor
arguments and proved generic component/cancellation APIs avoid that expansion.

## Old

The original alpha_cartesian signature, retained verbatim, was:

```lean
theorem alpha_cartesian {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    alpha B k r p i h = (beta B r k i p h.symm hsq.flip).hom
```

Its proof was sorry and it preceded the open-composition calculation.
alpha_vertical, alpha_horizontal, alpha_baseChange and gamma_evaluation also
had sorry proofs. No CartesianNormalization section existed.

## New

All five signatures and every existing data definition remain unchanged.
The four alpha proofs are complete. gamma_evaluation is reduced to two separate
normalization results using a proved mate-pasting and origin-transport argument.
The item privately imports StrictTowerGammaEvaluation and
SingleProperOpenFiniteNormalization. alpha_cartesian and the unchanged private
alpha_identities proof now follow the shared reverse-comparison helpers.

The CartesianNormalization section extends through alpha_baseChange. It locally
sets backward.isDefEq.respectTransparency and its types variant to true and
marks G, R, J, gComp, gId, jAdj, adj, jComp, jCongr, pi, alpha and
towers_hasDerivedCategory irreducible. beta is locally irreducible after its
inverse formula is recorded. These settings end at the section boundary. No
heartbeat limit is changed. A scoped unusedVariables linter setting on
alpha_baseChange retains the original sp and sr binders: the stronger reverse
cube argument needs only commutativity of those faces. Its statement is retained.

## Users

The direct downstream check found the following importers. They keep their
public interfaces and need no forced adaptation. No other existing module is
edited except the unclaimed arrows module described in the separate API record.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | U3 | Proofs and private helpers changed. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | U1 | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | A5 | Same signatures and data; no adaptation. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.Paper.CompactSupportSiteCoherence | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.Paper.ProperOpenTowerComparison | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.Paper.SystemTensorMateArrows | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | U4 | Same signatures and data; no adaptation. |

## Status

landed 20261021T024203-L-3042570 2026-10-21 (merge of deliver/U3/Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus)
