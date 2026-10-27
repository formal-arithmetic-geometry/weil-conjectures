# Q08 shared cartesian-instance ownership repair

## Reason

The return of lem-sfb-unramified-pseudo-torsor at 68ac3d726477 explicitly
requires moving groupSpaceOverCartesian out of FreeFlatGroupSpaceQuotient.
The requested consumer companion repair falls outside the item's mathematical
dependency closure once the unrelated quotient theorem citation is removed.
The delivery classifier skips that node and consequently reports its module as
ownerless. Land this shared-library repair separately; the remaining Q08 packet
can use the already-landed definition without an artificial theorem dependency.
No delivery, review, launcher, or landing tool is changed.

## Old

AlgebraicGeometry.AlgebraicSpace.groupSpaceOverCartesian is a real instance in
Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient, owned by a theorem node.
Consumers need its construction but need no quotient theorem conclusion.

## New

Move the same instance name, signature, and body into
Sheaf.AlgebraicGeometry.GroupSpaceOverCartesian, owned by
def-sfb-group-space-over-cartesian (created by the Q08 repair worker).
FreeFlatGroupSpaceQuotient publicly imports that owner, removes the original
instance, and drops that name from its owned declaration list. Add the genuine
definition dependency to its stmt_deps. Its constructions and theorem remain
byte-for-byte unchanged. There is one registered instance.

## Users

FreeFlatGroupSpaceQuotient retains the same public API by a public import.
UnramifiedPseudoTorsor in the Q08 sandbox imports the new owner directly.
Other users of the quotient module continue to receive the same instance.
No theorem statement, proof, or hypothesis changes.

## Validation

The worker's full new-definition metadata passes check_new_node. All three
sandbox modules compile on the server. Before this maintenance commit, compile
the two shared modules separately with tools/lean_file.sh, default 60 seconds,
using the maintenance group mirror. Validate the introduced DAG edge and the
new definition with nt_incremental2.check. The remaining item packet must then
pass deliver2.py --no-push through the unchanged gate.

## Status

Shared ownership extraction completed as a maintenance repair. The original
item remains subject to its normal independent stage-2 delivery review.
