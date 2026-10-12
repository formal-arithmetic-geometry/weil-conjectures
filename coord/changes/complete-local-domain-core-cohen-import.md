# Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularCore: CohenRing export

## Reason

The public signature of complete_local_domain_finite_over_regular_core uses only adic
completeness, regular local rings, and module finiteness. CohenRing is unnecessary as
a public import. Removing it follows the import-pruning rule. The sole direct importer
CompleteLocalDomainFiniteOverRegular imports CohenRing publicly itself and compiles
unchanged against the changed core, as checked by lcompile.py in a sandbox overlay.
No theorem statement, definition, name, universe, or declaration visibility changes.

## Old

```lean
public import Sheaf.RingTheory.CohenRing
```

## New

The import line is removed. CohenRing remains publicly imported by the new parameter-map
module because its statement explicitly uses IsCohenRing; that module is imported only
for the proof in the core.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular | unclaimed | Already directly imports CohenRing publicly; original compiles unchanged against the new core. No adaptation. |

All other consumers see the core through this unchanged direct importer. No target
statement uses a changed definition; no definition is changed and target review is
not reopened.

## Status

landed 20261012T151000-L-2233197 2026-10-12 (merge of deliver/X3/Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegularCore)
