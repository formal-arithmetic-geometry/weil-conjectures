# EllAdicRationalization archive proof imports

## Reason

Restore the zero-hole quarantined item named in `coord/rework.tsv`. The archived
`integral_scalar_map_eq` proof uses private helpers from `IntegralConstructibleSequentialHom`
and public declarations that its private imports no longer expose after the module sync.
The unmodified archive fails with unknown `homColimitProperty` and
`CategoryTheory.homColimit_bounded`, followed by cascading cocone errors.

## Old

The preserved existing import is:

```lean
public import Sheaf.Paper.IntegralConstructibleSequentialHom
```

There was no explicit import of `Sheaf.Paper.IntegralConstructibleSheafHom` and no
`import all` of `Sheaf.Paper.IntegralConstructibleSequentialHom`.
No existing declaration signature, definition or proof is changed.

## New

The existing public import stays verbatim. Added private proof imports:

```lean
import all Sheaf.Paper.IntegralConstructibleSequentialHom
import Sheaf.Paper.IntegralConstructibleSheafHom
```

`import all` makes the already proved private bounded-Hom and isomorphism lemmas usable.
The second import supplies the public sheaf-source continuity API explicitly.
The sync comment is wrapped to 100 columns. A local file option disables
`linter.privateModule`, since all eight preserved declarations are intentionally private.
All proof bodies, signatures, data, public imports and public attributes are preserved.
The repaired file compiles cleanly through `lcompile.py` in 14.6 seconds.
No target meaning changes and no target statement review is reopened.

## Users

The item is currently absent from the live tree, so `tools/downstream.py` reports an
unknown module. An exact module-name import scan across both `lean/` and `quarantine/`
finds no consumers. No DAG node attaches to the item module. Its restored private
helpers retain the complete archive, without withdrawing any associated mathematics.

| module | group holding it | effect |
|---|---|---|
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | T2 | Restore all private proofs; repair their import visibility. |

No consumer needs adaptation. The upstream source module is untouched.

## Status

landed 20261021T154059-L-2789463 2026-10-21 (merge of deliver/T2/Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization)
