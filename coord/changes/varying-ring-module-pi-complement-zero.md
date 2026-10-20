# modulePi_complement_zero

## Reason

The complementary component of `modulePi_components` is split into a named lower
statement so the image component can be proved by adjunction triangles in the item.
The item imports the new theorem as a proof-only import. The item also suppresses the style warning for the local typeclass witness used by the adjunction proof.

## Old

No declaration existed.

The item previously had no local linter option.

## New

The item now sets `linter.style.haveILetI` to `false` locally for this proof file.

`AlgebraicGeometry.ProEtale.VaryingRing.modulePi_complement_zero` states that
restriction of `modulePi` to the complementary open is zero.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | W4 | imports and applies the split theorem |

## Status

landed 20261020T230844-L-621438 2026-10-20 (merge of deliver/W4/Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting)
