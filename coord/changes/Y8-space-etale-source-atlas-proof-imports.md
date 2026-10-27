# AlgebraicGeometry.AlgebraicSpace.etale_source_atlas_detection

## Reason

The proof uses representing pullback squares directly and does not use bundled
algebraic-space fibre products. Remove their unused public import and the redundant
public HasPullback import. No declaration signature or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
```

## New

Both import lines are removed. Required pullback-square APIs are already available
from the public AlgebraicSpace import. Add only the private proof import
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`.

## Users

`tools/downstream.py` lists the following transitive consumers. The only direct
importer, ChartwiseEtalePermanence, privately imports this module and publicly imports
both removed modules itself. Thus all downstream public environments are unchanged.
The theorem and every definition retain their exact signatures.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AlgebraicSpacePushforwardAtlasEqualizer` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood` | J1 | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified` | K1 | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse` | S9 | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.RepresentableFiniteStackProperties` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable` | W8 | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas` | unclaimed | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.Paper.NormalLatticeFiniteCoverPresentation` | M6 | No change: the only direct importer independently imports both removed modules. |
| `Sheaf.SecPurity.NormalLocallyConstantFiniteSection` | S8 | No change: the only direct importer independently imports both removed modules. |

## Status

landed 20261023T132458-L-2283666 2026-10-23 (merge of deliver/Y8/Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection)
