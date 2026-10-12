# DerivedRHomAlgebraModule imports

## Reason
The direct public import of the injective-components theorem is unused by every signature,
definition and proof in the module. The canonical resolution functor is already publicly
available from DerivedInternalHom. Removing the unused edge compiles without warnings.
No target or definition changes meaning. The degreewise-injectivity theorem remains in
its own source module and is used privately by RingedSiteKInjectiveResolutions.

## Old
```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
```

## New
The displayed unused import is removed; the four other public imports are retained.
All declaration signatures and definition bodies are byte-for-byte unchanged.

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | X2 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | U3 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedFactorization | T1 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | Q2 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | X3 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteRestrictionDerivedRightAdjoint | Q2 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | H1 | Compiled successfully with the removed import; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction | H2 | Compiled successfully with the removed import; no adaptation needed. |

These are the eight direct importers in the packet/import graph. The import-prune check
reports no lost declaration use. No declaration itself changes or is removed.
The global build remains the final check of downstream instance inference.

## Status
landed 20261012T135225-L-1658856 2026-10-12 (merge of deliver/D3/Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule)
