# picardExternalCechCupBidegree_leibniz_coordinate

## Reason

The target Leibniz identity is proved by applying injectivity of the target Cech
coordinate equivalence. The resulting pointwise face calculation is a separate,
strictly simpler public theorem and module, with its remaining calculation recorded
as the named split node.

## Old

The baseline has no declaration
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz_coordinate`.
The target theorem `picardExternalCechCupBidegree_leibniz` has proof `by sorry`.

## New

Add the coordinate theorem with the exact pointwise statement in
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate`, and prove
the target theorem by coordinate-equivalence injectivity followed by this theorem.
The target signature is unchanged; the new module is imported privately.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz | H3 | Uses the new coordinate theorem in its proof; target signature unchanged. |

## Status

landed 20261014T010843-L-3163892 2026-10-14 (merge of deliver/H3/Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz)
