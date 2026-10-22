## What changed

Replaced the duplicate naturality/cancellation proof of
AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport by a specialization
of the already proved mixedGlobalHom_baseChange_counit_transport with the same
localization universe. The theorem's public signature is byte-for-byte unchanged.

The attempted source-theorem import exposed a real duplicate-definition failure:
Sheaf.GlobalHomPullbackComparison and WeilConjectures.GlobalHomPullbackComparison
both declared the same three public names. The Sheaf module now re-exports the
source module, retaining both previous public imports. Three fully proved private
helpers in the assigned module certify equality of the former tensorator, Leray
comparison, and complete pullback comparison expression with the adopted versions.
The scalar composition and square definitions are textually identical.
No statement, target meaning, or unit route changes. No source-library file changes.

The exchange consumer receives one forced simp-list addition. The complete seven
module sandbox compile passed: the changed comparison, assigned theorem and exchange,
and the four remaining unchanged downstream modules. Individual times were 2.8,
6.2, 36.7, 5.0, 4.5, 4.5 and 6.5 seconds. A long docstring line reported in that
run has been wrapped; delivery performs the final clean compilation and probes.

Updated the assigned node's proof and dependencies to the actual specialization,
reattached the definition node to the source module that owns its declarations,
and documented the consumer's normalization in its existing proof step.
Change record: coord/changes/B2-global-hom-transport-source-comparison.md.

## Proved and sorry left

AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport is completely proved
from the existing mixed-universe theorem. The private legacyTensor_eq,
legacyLeray_eq and legacyPullbackComparison_eq are also completely proved.
The exchange theorem's complete proof is preserved and adapted.

The assigned current source and preserved quarantine archive have zero holes.
This delivery has zero holes in all three changed modules. Holes closed: none
(0 of 0). Holes added: none. Split off: none. This is a compatibility and duplicate
construction repair, not a new hole closure. Existing sorries in unchanged imported
modules are not asserted to be closed; no such proof is replaced by sorry.

## No longer needed

Removed the proof-only import Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange
from the assigned module, replacing it with the proved source mixed transport.
The assigned node no longer directly needs lem-sc-global-hom-base-change-exchange,
def-pc-canonical-derived-tensor-hom-bijection, def-pc-global-derived-rhom or
def-pc-derived-base-change-map as proof dependencies: the mixed theorem carries
that argument. The statement dependencies remain unchanged, and the adopted theorem
still uses the underlying constructions. The direct proof dependencies now are
the mixed transport, pullback comparison, and global Hom adjunction nodes.

Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange and its unfinished dependency
Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate are no longer on this item's
proof route; their declarations are preserved. The exchange consumer is adapted
so that it still builds as part of the full library. No source declaration or
module is removed or withdrawn, and no quarantine archive is edited.
The old private homMap_comp, pullbackMate_naturality, directImage_naturality and
pullback_naturality duplicates are removed from the assigned module.

The Sheaf pullback-comparison module remains as a compatibility import; its three
duplicate constructions are supplied by the adopted source definitions instead.
No public import is removed there.

## Where the brief, the DAG or earlier work was wrong

The rework queue row is stale relative to the current source: E4 restored and
repaired the module at landing 20261022T002359-L-1922723. The original current module
compiled in 30.8 seconds and contains no sorry. A compiling copy alone would have
been a no-op, so this packet repairs the remaining duplicate-construction conflict
and uses the already available shorter proof route.

LeanFinder returned generic categorical evaluation/counit naturality statements;
Loogle found Functor.map_comp, and Mathlib grep returned generic naturality and
NatIso.ofComponents results. Source inspection found the exact mixed transport.
The earlier restoration report declined that route because the comparison wrappers
needed identification. The private equality proofs now supply that identification.
All changes stay below the unit level; no realized unit statement or step is bypassed.

## Forced adaptations

Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange (unclaimed when checked): its
original final simpa fails against the adopted comparison. The resulting type
mismatch has (schemeHomTensorPullbackIso g).inv.app in the proof's expanded mate
and (mixedHomTensorPullbackIso g).inv.app in the expected type, also at pullback.fst.
Add the already proved schemeHomTensorPullbackIso_eq_mixed to the final simp list
(old line 206, new lines 206-207). Every other exchange line, import, signature and
visibility is preserved. The adapted original proof compiles in 36.7 seconds.
The four other downstream modules compile unchanged; their sandbox copies were
used for validation and are not part of the delivery.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
