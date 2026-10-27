# AlgebraicGeometry.ProEtale.closedIdentityOpenHomNormalization

## Reason

The proof compares explicit derived functor constructions through their D+ inclusion
isomorphisms. Backward elaboration must unfold the existing functor abbreviations
consistently. The proof also uses the existing preservation-of-finite-limits/colimits
instances for composites of exact functors. These are proof elaboration settings and
file-local instance registrations; no mathematical interface changes.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

Every existing public declaration signature and definition is unchanged. The added
lemmas are private and proved. The three backward-elaboration options and local
instances affect only elaboration inside this module; they introduce no axioms.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ClosedIdentityOpenHomNormalization | F4 | Proof elaboration only; public signatures and definitions unchanged. |

`tools/downstream.py Sheaf.Paper.ClosedIdentityOpenHomNormalization --uses
closedIdentityOpenHomNormalization` lists zero downstream modules and only the item
itself as a textual user. No consumer adaptation or target-statement review is needed.

## Status

landed 20261025T122851-L-1814834 2026-10-25 (merge of deliver/F4/Sheaf.Paper.ClosedIdentityOpenHomNormalization)
