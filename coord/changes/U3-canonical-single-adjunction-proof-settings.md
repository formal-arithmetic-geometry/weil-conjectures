# canonicalSingleAdjunctionTranspose proof elaboration settings

## Reason

The proof introduces generic private helpers and elaborates the pinned sheaf functors
and derived adjunction choices. Its new local compiler settings are classified by the
static delivery check as non-declaration commands. No public signature, definition,
instance registration, import visibility, or notation changes. This record documents
that classification for review.

## Old

```lean
set_option autoImplicit false
```

The theorem ended in `:= by sorry` and there were no private helper declarations.

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The theorem is fully proved, with a scoped `maxHeartbeats 800000` setting and an
explanatory comment. Two proved private helpers are added. These options govern
elaboration of this file and introduce no importer-visible declarations. The old
public theorem signature and the three public imports are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose | U3 | Proof only; public interface unchanged. |

No downstream module needs adaptation: neither a signature nor a definition changes.

## Status

landed 20261012T184350-L-4022243 2026-10-12 (merge of deliver/U3/Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose)
