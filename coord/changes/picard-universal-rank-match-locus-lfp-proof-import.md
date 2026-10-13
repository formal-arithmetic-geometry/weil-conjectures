# picardUniversalRankMatchLocus_locallyOfFinitePresentation proof import

## Reason

The proof now invokes the split-off representative theorem from a private import. This
changes the module's proof environment while preserving the public target signature.

## Old

The target module did not import
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso` and its target
proof was `by sorry`.

## New

The target module privately imports
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso` and transports
local finite presentation across the resulting scheme isomorphism.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus` | unclaimed | compiles against the proved target theorem |

## Status

landed 20261013T002012-L-2359491 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation)
