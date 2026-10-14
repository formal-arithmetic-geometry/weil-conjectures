# picardExternalCechCupBidegree_leibniz

## Reason

Restore the withdrawn held statement and prove it through the already proved ordinary
Cech cup Leibniz theorem. The supplied inclusion-level reduction still depended on an
open external differential calculation. The tested route exposes the missing cochain
conversion as a fully proved reusable interface.

## Old

The checkout contains neither PicardExternalCechCupLeibniz nor
PicardExternalCechCupBidegreeLeibnizCoordinate after rollback. The supplied sandbox
restores their archived signatures. Its main proof imports
Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate and applies
picardExternalCechCupDegreeMaps_comm_ι, which is still sorry.
The coordinate corollary is already proved by evaluation of the main theorem.

No public declaration named picardCechScalarIso or
picardExternalCechCupBidegree_transport exists in the checkout. The related scalar/cycle
conversion in PicardExternalCechModuleRepresentatives is private and assumes cycles.

## New

Both archived theorem signatures remain byte-identical; they are recorded verbatim in
the corresponding node lean.statement fields. The main proof privately imports the new
Sheaf.AlgebraicGeometry.PicardExternalCechCupTransport module and uses its equality in
three bidegrees, the ordinary cechCupCochain_leibniz, and the unique refinement cochain
maps. The coordinate corollary retains its evaluation proof.

The new public API consists of the real composite isomorphism picardCechScalarIso,
its coordinate, differential and equal-degree-cast lemmas, and the fully proved
picardExternalCechCupBidegree_transport. The latter has its exact signature in the new
node lean.statement. The two public imports of this module are needed by its statements;
the import in the main module is proof-only. No existing definition, instance, statement,
visibility or target interface changes, and no sorry or axiom is added.

The main node records the new proof route and no longer depends on the external
inclusion-level differential node. The coordinate node retains its existing route.
The new transport node records its proved coordinate argument.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz | T4 | Restored archived signature; axiom-free proof through ordinary cup transport. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate | unclaimed | Restored archived signature and unchanged complete evaluation proof. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupTransport | T4, new | Fully proved conversion API for arbitrary cochains; used by the main proof. |

The supplied checkout has no other importers of the two withdrawn modules or the new
transport module. Existing modules are not adapted. The differential-coordinate module
still has its own users and is not changed by this delivery. The transport module imports
only the existing bidegree and refinement modules, which do not reach either restored
Leibniz module; the imports are acyclic.

## Status

landed 20261014T103114-L-1343840 2026-10-14 (merge of deliver/T4/Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz)
