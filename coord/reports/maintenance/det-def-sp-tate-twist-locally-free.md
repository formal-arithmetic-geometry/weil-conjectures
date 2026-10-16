# Maintenance: det-def-sp-tate-twist-locally-free

## Cause

The accepted CoefficientTwistsDetailed interface does not implement the rational and common-stage twist functors promised by its final K(m) formula. rationalComplexTwist and algebraicClosureComplexTwist take an object and return an object; neither has a map on morphisms. CoefficientTateTwistData records only coefficient-object families. finiteComplexTwist and integralComplexTwist are genuine functors. An isomorphism between coefficient-line objects under scalar extension does not specify the missing rational/common-stage morphism actions or their coherent scalar-extension comparisons. The incomplete stage-2 completion falsely makes det-def-sp-tate-twist-locally-free eligible; its clause 3 requires the specified tensor twist functors to be autoequivalences. The current bottom-up brief correctly prevents the consumer worker from stating this other DAG node. Repeating the consumer cannot repair its owning definition.

The owning definition was accepted in side batch d34ce2e91c8a (batch
a8aa22b54a6e4df9b99c97536fe35ca5), promoted to the authoritative shared DAG in
4c99c8a3e182, and later resynchronized to the side DAG. The Q24 report describes
object operations as implementing the final formula, and reviewed_lean passed
them without checking the rational/common-stage morphism interfaces. Fresh source
inspection and the server signature probe confirm the defect; it is not an
import, permission, timeout, search-tool or failure-threshold problem.

## Record repair

Withdraw only lean and reviewed_lean from dag/nodes/sec-smooth-purity/def-coefficient-twists-detailed.json in both server repositories:
/home/ubuntu/weil-conjectures-sheaf (sheaf-dag) and
/home/ubuntu/weil-newtargets (newtargets-dag). Archive both records verbatim in
coord/reports/maintenance/det-def-sp-tate-twist-locally-free.invalidated-lean.json, with the source hash and originating commits. The source module and
published artifacts remain available for ordinary consumers; the node's stage-1
split/review, statement and dependency edges are unchanged. Updating the shared
record as well as the side record prevents sync_newtargets.py from resurrecting
the stale completion. coord/repair-notes/def-coefficient-twists-detailed.json carries the owning worker's repair obligation and
invalidated_lean for the existing stale-alias preflight guard.

## Next workers

Repair def-coefficient-twists-detailed as its own normal stage-2 item, after its
statement prerequisites are stated. Keep its mathematical statement, dependencies,
existing public declarations and object assignments. Supply canonical functors for
rational and algebraically closed/common-stage complex twisting. The rational
morphism action must descend integral tensor to the specified raw Hom scalar
localization. The algebraically closed action must descend the finite-stage actions
to the specified common-stage Hom colimits, with the necessary coherent comparisons
under finite coefficient extension (including identity and composite extensions).
A coefficient-line object comparison alone does not provide this descent. Do not
substitute an arbitrary functor, a mere Nonempty choice, or an extra functor/linearity/
comparison hypothesis. Record all added declarations and their source/blueprint
docstrings; postponed property proofs follow the ordinary stage-2 DAG rules.

Required consumer validation: in a scratch file with the actual small pro-etale
site (object universe u+1, morphism universe u), instantiate the rational and
common-stage operations as endofunctors, access both .obj and .map, and check that
their object assignments agree with rationalComplexTwist and
algebraicClosureComplexTwist. Check compatibility with localization and with
common-stage representatives, including m=0, positive and negative twists,
identity and composite coefficient extensions, and an empty scheme. The subsequent
consumer must be able to refer to those specific functors and their negative
twists when stating autoequivalence. This validation checks the interface; proving
the consumer theorem is not part of this repair. Compile files individually using
tools/lean_file.sh (60 seconds per file), then use normal independent review.

The original consumer keeps all three clauses, including arbitrary finite rings
A killed by an ell power and its canonical Kummer scalar-extension comparison.
Resume it when the owning definition's repaired completion lands. It must use the
published canonical functors; an unspecified equivalence with the right objects
does not encode the required morphism action. Do not restore the archived binding
or merely re-alias coefficientTateTwists without fixing this defect.

## Verification and operations

The production dag_queue calculation is checked before and after withdrawing this
record, including an in-memory restoration control. Before: the definition is
stated and the consumer is stage-2-open. After: the definition is unstated and
the consumer is excluded by its missing statement dependency. The owning
definition is offered subject to its own unchanged bottom-up prerequisites.
The existing dispatcher stage2_wait.blockers guard applies to held consumer
claims after clone refresh. Preserve all historical tries, failure counts and
sandbox work; no failure threshold, suppression, abandonment or dispatcher-state
rewrite is used. Let the already running consumer worker exit naturally.

Regenerate queue.tsv, queue.md and blueprint-index.tsv through tools/queue.py.
Every changed existing server file has a sibling .maint-NR-det-twist-1792159337.bak backup; new maintenance
records also receive initial snapshots. Commit exact paths under the server
merge locks with SHEAF_LEAD=L-only and the requested Bin Wu identity. No existing
Lean source is changed and no global build is run. A fresh scratch signature probe
uses tools/lean_file.sh, which enforces one file at a time and 60 seconds per file.
