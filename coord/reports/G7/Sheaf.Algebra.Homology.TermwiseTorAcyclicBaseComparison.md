## What changed

Repair of the returned delivery at 8650353c78 (base e0d550965). Read the
current shared checkout, coord/rework.tsv, and the current server source directly.
On both checkouts the live lean/ path is absent and the quarantined source has
the original signature and one sorry. Reconstructed this packet's module from
that current archive, inserted the retained complete proof, and verified the
public theorem signature is verbatim identical. Retained the canonical-model
import repair required by the recorded duplicate-declaration failure.

Simplified the common-universe proof's final cancellation: rewrite the goal by
isIso_comp_left_iff and counit naturality, then use the already established
isomorphisms. This removes the redundant composite-isomorphism instance and the
explicit IsIso.of_isIso_comp_left application. The delivery therefore contains
both the restoration/proof repair of the current quarantined module and a
checked proof improvement, rather than only a rebase or an unchanged re-push.

Restored Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison from its quarantined
copy and proved
ModuleCat.BaseDerivedTensorCohomologyModel.counit_isIso_of_termwise_tor_acyclic.
Replaced the public model import by the canonical upstream model to repair the
specific duplicate-declaration failure recorded in coord/rework.tsv.

The common-universe private helper uses a functorial K-flat resolution, the
existing termwise Tor-acyclic tensor comparison, the K-flat scalar-extension
counit theorem, and the counit's naturality square. The main proof transports
the given universal pair through ULift ring equivalences, transfers the Tor
hypotheses using explicit up/down linear isomorphisms, applies that helper, and
reflects the resulting isomorphism back. Both new private helpers are proved.
The theorem's written signature and docstring are unchanged.

Added private proof imports of the K-flat resolution infrastructure, the homotopy
identity comparison, and all of DerivedExtensionRingEquivRawTransportIso. The last
import reuses its existing proved generic private helpers derived_equivalence and
kan_postcomp_equivalence; its restricted public same-universe theorem is not being
applied to incompatible universes. Updated the node's proof and proof dependencies
accordingly. This is a generic transport tool within the recorded resolution route;
no unit statement or unit proof step is bypassed.

The retained proof compiled against the current server build in 3.5 seconds.
The revised proof compiled without warnings in 3.5 seconds.
#print axioms for the public theorem returned exactly propext, Classical.choice,
and Quot.sound. The proof therefore has no transitive sorry dependency either.
The final delivery checks run the project's full declaration probe again.

Change record: coord/changes/G7-termwise-tor-acyclic-canonical-model.md.

## Proved and sorry left

Closed the original one hole:
ModuleCat.BaseDerivedTensorCohomologyModel.counit_isIso_of_termwise_tor_acyclic
(lem-pc-termwise-tor-acyclic-base-comparison).

Proved 1 of 1 original sorries. Added zero holes. Zero sorries remain in this
module or elsewhere in this delivery; nothing was split off. The proved private
helpers are counit_isIso_of_tor_acyclic and ulift_scalar_iso.

## No longer needed

Removed public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel in
favor of its upstream canonical counterpart. This removes the duplicate model
from this module's import closure. The old model module still has other users,
so this is not a claim that it can be globally withdrawn.

Both original mathematical proof dependencies are used. No mathematical node or
module on the original route is pruned. No new nodes or modules are introduced.

## Where the brief, the DAG or earlier work was wrong

The landing return for 8650353c78 identified a concurrent file change after
its base e0d550965. The present checkout and server both keep this item in quarantine/
and have no live lean/ copy. This repair uses that present quarantined statement
and retains its complete signature and docstring. No concurrent proof is removed.

The assigned file is in quarantine/, not lean/. Its actual compiler failure is
recorded in coord/rework.tsv: importing the upstream model after the old Sheaf
model duplicates BaseDerivedTensorCohomologyModel._sizeOf_inst. Starting from the
quarantined file and replacing its model import repairs that failure.

The original DAG plan is mathematically sound. It omitted the Lean implementation
of the common-universe tensor/extension comparison and the transport of the
universal Kan extension; these are now proved, rather than assumed.

There are no live downstream modules according to downstream.py --allow-missing.
The only quarantined direct consumer, TorIndependentProjectiveComplexTensor,
still contains its own obsolete Sheaf model import and has a separate rework
item. Its existing call to this theorem has the unchanged arguments; this packet
edits no consumer or source-library file.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
