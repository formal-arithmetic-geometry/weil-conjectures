# Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers imports

## Reason

The coherent-power statement and proof use no declaration of Ample. Remove its unused public
import. The theorem signature and visibility stay identical; all new helpers are private and proved.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.AlgebraicGeometry.Ample
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication | unclaimed | The sole direct importer imports this module privately and separately imports Ample publicly. No adaptation is required. |

All further importers receive this module through that private proof import, so they do not see
its imports. No target statement or definition changes meaning.

## Status

landed 20261013T054209-L-440566 2026-10-13 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers)
