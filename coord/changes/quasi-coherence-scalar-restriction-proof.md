# quasiCoherent_iff_restrictScalars

## Reason
The proof uses the existing source-library cokernel theorem and a new affine
presentation split. No statement, definition, or existing declaration visibility
changes. The redundant public ChangeOfRings import is already publicly exported by
CommAlgebraSheaf, which remains a public import; consequently its API remains available
in every downstream module. All newly added imports of the item are proof-only.

## Old
```lean
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
```

## New
```lean
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.AffineAlgebraModulePresentation
```
The target signature is byte for byte unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.QuasiCoherenceScalarRestriction` | H3 | proof and proof dependencies updated |
| `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence` | not queried; no adaptation | same statement and public API |
| `Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh` | not queried; no adaptation | same statement and public API |
| `Sheaf.AlgebraicGeometry.AffineModuleTensorCoherenceComparisons` | not queried; no adaptation | same statement and public API |
| `Sheaf.AlgebraicGeometry.AffineModuleTensorComparisonIsIso` | not queried; no adaptation | same statement and public API |

These are the four direct importers found by source search. Since the public import
closure is unchanged, transitive users likewise see the same API. No forced adaptations
and no reopening of target statement reviews are required.

## Status
landed 20261012T135242-L-1668797 2026-10-12 (merge of deliver/H3/Sheaf.AlgebraicGeometry.QuasiCoherenceScalarRestriction)
