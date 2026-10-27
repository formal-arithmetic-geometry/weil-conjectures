# CategoryTheory.strictRoosShiftLocalization

## Reason

The completed proof adds private helpers, a proof namespace, local instances and
local irreducibility attributes. The static visibility check requires this record
for those commands. No existing declaration signature, public import, or public
definition changes. All new helpers are private and proved or explicitly constructed.

## Old

The original module proof environment included:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uT vT uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory
```

The only theorem body was `by sorry`.

## New

The original commands remain, with the additional elaboration option:

```lean
set_option backward.defeqAttrib.useBackward true
```

The proof opens `CochainComplex` and adds private constructions and proved helpers
inside `CategoryTheory.StrictRoosShiftProof`, opened for the main proof. Local
instance attributes select the explicit product, evaluation, and transition shift
structures. Local irreducibility attributes keep the explicit shift constructions
from being unfolded by elaboration. These attributes are confined to this module.
The theorem's entire signature and both public imports remain verbatim. Its proof
now establishes the signed coordinate equations, limit comparison, inclusion
compatibility, localization descent, and uniqueness, with zero new holes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.StrictRoosShiftLocalization --uses
strictRoosShiftLocalization` reports zero downstream modules and only the defining
module as a name use. A source search likewise finds no external importer or user.
The unfinished parent proofs recorded in the DAG remain valid with no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.StrictRoosShiftLocalization | P2 | Complete the existing proof; signature unchanged. |

No consumer is adapted and no target meaning changes.

## Status

landed 20261023T090726-L-712043 2026-10-23 (merge of deliver/P2/Sheaf.CategoryTheory.StrictRoosShiftLocalization)
