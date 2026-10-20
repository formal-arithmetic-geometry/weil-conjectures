# Sheaf.AlgebraicGeometry.BertiniIrreducibleMember

## Reason

The proof compares the existing tensor-pullback unit with the universal incidence
construction. Local irreducibility attributes keep elaboration from expanding the
large tensor-pullback implementation and the two concrete zero-ideal definitions during
these comparisons. The delivery gate classifies the additional attribute commands as an
interface change and requires this record.

These attributes are explicitly local to this file. They do not change a declaration's
signature, definition body, global reducibility attribute or imported elaboration behavior.
No statement or mathematical definition changes, and no target meaning is reopened.

## Old

There are no local irreducibility commands for `Scheme.Modules.tensorPullback`,
`Scheme.Modules.tensorPullbackObj`, `linearSystemMemberIdeal` or `bertiniUniversalIdeal`
in this module. The existing definition `AlgebraicGeometry.linearSystemMemberIdeal`
and theorem signature
`AlgebraicGeometry.exists_open_geometricallyIrreducible_linearSystemMember` are the
shared repository's original ones.

## New

After entering the existing namespace:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
```

After the original definition:

```lean
attribute [local irreducible] linearSystemMemberIdeal bertiniUniversalIdeal
```

The original definition body, theorem signature, public imports and public declaration
visibility remain verbatim unchanged. The attributes expire at the end of the file's
section. Added proof imports are private. All added helpers in the item are private and
fully proved; the new public support declarations have their own modules and DAG nodes.

## Users

`python3 -B tools/downstream.py Sheaf.AlgebraicGeometry.BertiniIrreducibleMember --uses
AlgebraicGeometry.linearSystemMemberIdeal
AlgebraicGeometry.exists_open_geometricallyIrreducible_linearSystemMember` reports zero
current transitive importers. Both names are mentioned only by the item itself. This is
not a withdrawal: unfinished DAG parents still need the theorem, whose statement and
attachment remain intact. No consumer adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BertiniIrreducibleMember | C8 | proof completed from named inputs; local elaboration attributes added; public interface unchanged |

## Status

landed 20261020T211647-L-3485322 2026-10-20 (merge of deliver/C8/Sheaf.AlgebraicGeometry.BertiniIrreducibleMember)
