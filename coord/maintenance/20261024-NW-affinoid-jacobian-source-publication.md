# NW affinoid Jacobian source publication

Maintenance for lem-per-affinoid-jacobian-certificate-regular@a3a60566a.

The return cited RestrictedSeries.jacobianMinor in
Sheaf.RingTheory.RestrictedSeriesJacobian, but that module and its definition
node were absent from live source and history. Both were present only in Q06
head 6347acacf25db620405b19689bfc6a985a158b51. The saved independent reviews passed
both Q06 and NW; nt_parallel2.commit temporarily indexed ready Q06 definitions
before survivor validation and durable publication, then returned NW against
that provisional index. The source lookup was correct to report unavailable.
The current persistent source-index.pickle contains no such module or name.

Published only the already-reviewed shared source and definition node, unchanged
from Q06 prepared plan 3bdfd01df1ba6d310859499fbc2a2d10aaa19f572cbcae4600e2e08321973fab.
No mathematical statement or proof was written or changed. The original item's
return now records the available canonical interface and how to resume reuse.

Validation: tools/land_set.sh registered
20261024T144524-MaintNWJacobian-1986198; its single tools/lean_file.sh invocation
compiled RestrictedSeriesJacobian.lean in 9.0 seconds with the 60-second limit;
its import/collision check passed. check_new_node returned no findings, all seven
recorded declarations occur in the source, and both definition dependencies exist.
The ordinary global build remains responsible for verifying the landing.

Protected landing tools were not edited. Their required follow-up is to return
an author error only for collisions against durably published sources. A name
found only in another pending plan must trigger an internal retry/recheck after
that plan's actual outcome. Rebuild the provisional index after removing stale,
conflicting or DAG-invalid plans; never require a worker to import unpublished
source. Regression case: ready plan A introduces X; B declares X; A is removed
later; B must be rechecked against published sources rather than returned with
an unavailable source dependency.

Backups use suffix .maint-NW-jacobian-1792852603.bak. For the new source and node,
the backup is the exact reviewed Q06 content; no previous live files existed.
coord/returns/NW.md and the landing tool's coord/deliveries.log were backed up
before changes. This new maintenance record also has a .bak copy.
