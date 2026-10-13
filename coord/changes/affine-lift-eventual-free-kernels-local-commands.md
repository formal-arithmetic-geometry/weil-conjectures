# AlgebraicGeometry.Scheme.affine_lift_eventual_free_kernels

## Reason

Preflight conservatively classifies the extra universe and declaration-scoped open
commands used by private helpers as an interface change. This record documents
those commands. No existing public signature, public import, instance or definition
changes. The new private declarations are unavailable to importers. The new universe
wA is used only by the private localization-transport construction, and scoped opens
end at their helper declaration. No target statement or definition changes meaning.

## Old

```lean
universe u w
```

There were no declaration-scoped `open MonoidalCategory in` commands and no
private helpers. The existing local instance attribute command is retained.

## New

```lean
universe u w wA
```

Three private theorems have declaration-scoped `open MonoidalCategory in`:
`exactAt_of_tensor_unit_vanishes`, `flat_of_finiteFree`, and
`tensor_exactAt_of_vanishes`. New declaration-scoped elaboration options are used
for private helpers and the main proof. The main proof's extra transparency and
heartbeat settings end at that declaration. All existing declarations retain their
signatures and visibility. No downstream proof is changed.

## Users

The direct uses found by `tools/downstream.py` with
`--uses affine_lift_eventual_free_kernels` are listed below. The full import closure
has 400 modules, but none can name the private helpers and there is no new global
notation, instance, attribute or opened namespace. Thus every importer keeps the
same statement and meaning; no forced adaptation is present.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels | unclaimed | Existing public signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffinePerfectTruncationTriangle | unclaimed | Existing public signature and meaning unchanged; no adaptation required. |

## Status

landed 20261013T111945-L-3070894 2026-10-13 (merge of deliver/Y2/Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels)
