# AlgebraicGeometry.Scheme.picard_pullback_base_change_dual

## Reason

Prune the redundant public import of FiniteLocallyFreeTensorUnit. This module's
statement uses the adjunction from ModuleBaseChangeMapOpenRestriction and the
ordinary dual API, while the proof now applies the primal theorem to the dual
bundles. No theorem signature or definition changes. This record documents the
importer-visible removal required by stage-3 preflight.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Sheaf.AlgebraicGeometry.PicardPullbackBaseChangePrimal
import Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardPullbackBaseChange | unclaimed | The only direct importer. It already imports FiniteLocallyFreeTensorUnit directly and imports the changed dual module privately. Its theorem and proof remain unchanged. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | The only downstream module mentioning isIso_tensorPullback_unit_of_finiteLocallyFree. It already imports FiniteLocallyFreeTensorUnit directly. Its theorem and proof remain unchanged. |

`tools/downstream.py` reports 161 transitive importers. The dual module has only
one direct importer, PicardPullbackBaseChange, whose import of the dual module
is proof-only. Thus the removed public import is not re-exported through that
importer, and the more distant importers lose no declarations. The `--uses`
search for the finite-unit theorem reports only PicardPullbackEvaluation,
which has its own direct import as recorded above. No modules are adapted,
and no target statement or meaning changes.

## Status

landed 20261012T232905-L-2043709 2026-10-12 (merge of deliver/S2/Sheaf.AlgebraicGeometry.PicardPullbackBaseChangeDual)
