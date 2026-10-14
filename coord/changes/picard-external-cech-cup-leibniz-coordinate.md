# picardExternalCechCupBidegree_leibniz_coordinate

## Reason

Repair the returned reduction without altering either declaration's signature or
visibility. The existing inclusion-level differential compatibility theorem already
contains the needed face calculation. Reuse it, rather than leave a second copy of
that calculation as a new hole.

## Old

The withdrawn H3 delivery proved
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz` by
coordinate-equivalence injectivity and the new coordinate theorem.
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz_coordinate`
had proof `by sorry`. Both modules are absent from the current repository base.

## New

Keep both exact public signatures. The Leibniz theorem privately imports
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate` and derives
its pure-tensor identity from the existing inclusion equation. The coordinate theorem
privately imports the Leibniz theorem and proves its assertion by evaluation.
Neither module contains a textual sorry. No new instance or file-level option is added.
The choice in the theorem proof is from the already proved bidegree existence theorem;
coordinate injectivity identifies each chosen pure-tensor value with the specified map.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz | G3 | Same signature; complete proof from the existing differential inclusion theorem. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate | unclaimed | Same archived signature; coordinate evaluation is proved. |

There are no repository importers of these withdrawn modules at this delivery base.
No unheld existing module is adapted. In particular, the Paper collision is independent
of both modules; the current build probe already retries failed combined probes singly.

## Status

landed 20261014T082419-L-4009504 2026-10-14 (merge of deliver/G3/Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz)
