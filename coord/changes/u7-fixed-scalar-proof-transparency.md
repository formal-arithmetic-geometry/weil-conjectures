# AlgebraicGeometry.ProEtale.upperStar (local proof transparency)

## Reason

Avoid repeated elaborator unfolding of pro-etale inverse image while proving the
mate identities. This is a local attribute, not a change to any declaration,
exported attribute, definition body, signature, or downstream meaning. The static
preflight classifies any added attribute command as an interface change and asks
for this record.

## Old

No local irreducibility attribute in the item module.

## New

```lean
attribute [local irreducible] upperStar
```

The declaration `upperStar` itself is unchanged. The attribute expires at the end
of this module and cannot affect importers. All existing public declarations,
signatures, definition bodies and their mathematical meaning are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage | U7 | Local elaboration of private proof helpers only; Full module compile and delivery dry run passed. |

No consumer adaptation is needed: the attribute is local and no interface changes.

## Status

landed 20261019T112548-L-3955715 2026-10-19 (merge of deliver/U7/Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage)
