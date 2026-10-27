# AlgebraicGeometry.ProEtale.coefficientHeart_curve_complement

## Reason

The completed proof uses the existing private module-support API through a proof-only
`import all Sheaf.Paper.CondensedOpenClosedRecollement`. The returned packet db4455834
had copied four private theorems from that API; all four copies and their extra
namespace block have now been removed. The module retains the elaboration transparency
option used by those categorical proofs. The command-change scanner requires this
record. No public declaration signature, definition, instance, notation, attribute
or public import changes.

## Old

The original module's elaboration commands were:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
```

The additional option only controls elaboration in this file and adds no exported
mathematical data. There is no new `CondensedRing` namespace block or private theorem.
The proof reuses `moduleCounitOfAbelian`, `moduleUnitOfAbelian`,
`openRestrictionPushforwardZero` and `openUnitIsIso` from the existing recollement
module. The public theorem signature remains verbatim and its proof is complete.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientHeartCurveComplement --uses
AlgebraicGeometry.ProEtale.coefficientHeart_curve_complement` reports zero downstream
modules and only the declaration in its own module. No consumer adaptation is needed;
no target meaning or definition used by a target changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientHeartCurveComplement | C1 | Complete proof using existing support lemmas; identical public signature and public imports. |

The shared recollement module is unchanged. The import-direction check confirms it
does not reach the item, so the new proof-only import creates no cycle.

## Status

landed 20261023T151801-L-408753 2026-10-23 (merge of deliver/C1/Sheaf.Paper.CoefficientHeartCurveComplement)
