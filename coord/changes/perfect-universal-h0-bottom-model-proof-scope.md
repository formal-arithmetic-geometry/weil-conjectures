# AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model

## Reason

Stage-3 preflight conservatively reports added `open` and `set_option` commands
as an interface change. The proof adds namespace openings and two elaboration
transparency settings to elaborate the proved private helpers. These commands
apply while elaborating this module; they add no instance, attribute, notation,
public declaration, or public import, and do not change the theorem's signature.
Every added helper is private and proved. This record documents the commands
flagged by preflight; no dependent module needs an adaptation.

## Old

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
```

## New

```lean
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open SheafOfModules Modules Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel
--uses AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model` finds the
following textual users. Its 169 transitive importers receive the same public
signature and imports; the two elaboration options and namespace openings are
local to elaboration of this file and require no importer changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel | M2 | Proof elaboration only. |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel | unclaimed | Same statement and visibility; no adaptation. |

No target statement or definition used by a target changes meaning. No module
held by another group is edited.

## Status

landed 20261013T065110-L-899320 2026-10-13 (merge of deliver/M2/Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel)
