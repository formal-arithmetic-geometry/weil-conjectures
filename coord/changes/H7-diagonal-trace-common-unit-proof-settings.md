# Sheaf.Paper.DiagonalTraceFinitePushUnitCommon proof settings

## Reason

The common-unit theorem now has a complete proof. The file removes its legacy
transparency overrides and uses explicit instance-search capacity, synchronous theorem
elaboration, and local irreducibility for large derived constructions. The interface
checker conservatively classifies these top-level proof commands as a change requiring
this record. No existing public declaration, instance, attribute or public import changes.

## Old

The old proof settings were:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The file had no local irreducibility attributes and the assigned theorem ended in `by sorry`.

## New

The proof settings are:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
```

The following attributes apply only within this file:

```lean
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard
```

The assigned theorem's signature and original docstring remain verbatim. A proved private
helper records the completed unit's definition equation. The new proof imports are private.
All new public definitions and theorems live in the five new modules of this delivery.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed` | unclaimed in the shared snapshot | Unchanged source checked against the new common-unit proof; no adaptation required. |

This is the only direct importer. No declaration name, class or instance changes, so there
are no indirect users of a changed declaration or instance.

## Status

landed 20261028T055704-L-795643 2026-10-28 (merge of deliver/H7/Sheaf.Paper.DiagonalTraceFinitePushUnitCommon)
