# Maintenance: thm-coef-finite-hom

The completion record names only proEtaleRingDerivedPullback and its termwise factorization. The recorded node defines pullback, derived tensor and internal Hom at finite, integral, rational and common-extension coefficient levels. Its own note explicitly limits coverage to one consumer's finite pullback clause. The referenced DerivedTensor takes chosen representatives and asserts no resolution independence; DerivedInternalHomOfUniverses supplies localized Hom and representative comparisons, but their recorded interface has no normalized tensor-Hom evaluation/adjunction on the intrinsic small pro-etale module derived category. The fixed-scalar adjunction and the exact intrinsic realization are partial alternatives without the required tensor/Hom/evaluation compatibility. Thus a pullback-only alias is not a complete stage-2 binding for this node. It falsely makes thm-coef-finite-hom ready; the worker correctly refuses to state another DAG node under the current bottom-up rule. This is a record defect, not a tool or permission failure.

The partial record was installed by Q11's lem-trf-open-ctf delivery in side batch
4edbfe7ec836ad07f39a71088ae2cfd8573e6e32, promoted to the shared DAG at
30f82511f7. Its review belongs to that consumer delivery, whose nine dependencies
do not establish coverage of this operations node's full statement. Earlier
bindings were also explicitly finite-stage-only. The Q34 delivery 6de5b34980
for thm-coef-finite-hom is its stage-1 split, not a completed Lean statement;
the sync message 'live completion superseded side split' concerns that split.

## Record repair

Withdraw only lean and reviewed_lean from dag/nodes/sec-smooth-purity/def-weil-derived-pullback-tensor-hom.json. Preserve them verbatim in
coord/reports/maintenance/thm-coef-finite-hom.invalidated-lean.json. Keep the stage-1 split/review, statement, dependencies, proof and all
published Lean modules/artifacts. Commit the repair in both the authoritative
shared DAG and the isolated side project so live sync cannot resurrect the
false completion. coord/repair-notes/def-weil-derived-pullback-tensor-hom.json gives the normal claim handoff the repair diagnostic.
The standing brief requires workers and second readers to read that note even
when the dispatcher calls the item new. No brief or dispatcher change is needed.

## Next owning-node worker

Repair the owning definition node in normal stage 2, after all of its statement prerequisites are stated. Keep its mathematical statement, dependencies and existing public declarations. Supply and record the full operations interface promised by the node, reusing the recorded finite/integral/rational/common-stage constructions. For the finite stage expose tensor and Hom together with their canonical evaluation and currying on the intrinsic constant-ring module category, with independent site object/morphism universes. Either use the intrinsic constructions directly or give a canonical transport from the fixed-scalar presentation preserving tensor, Hom and evaluation. A pullback-only alias, an arbitrary isomorphism, an extra adjunction hypothesis or an assertion only about integral-to-finite reduction is insufficient. Validate a consumer using the actual small pro-etale site (objects t+1, arrows t), A_{E,n} -> A_{E,m} for n >= m >= 1, and the existing intrinsic derived Hom. Show that reduced evaluation has a well-typed unique transpose under the canonical tensor comparison, without coefficient flatness or equality of site universes. This check is about typing the canonical map; proving thm-coef-finite-hom is not part of this repair. Preserve the etale/pro-etale comparison required by that consumer. Do not silently replace the operations or restore a partial existing:true record. Read the archived binding and maintenance report; compile any Lean files one at a time through the 60-second file wrapper and use normal independent review.

The definition currently also waits for def-weil-rationalization-karoubi and
def-weil-algebraically-closed-coefficients, whose stale interfaces were reopened
by the separate Q22 maintenance. Keep normal bottom-up scheduling through that
existing prerequisite chain. Do not mark the operations node complete merely
because its old pullback module compiles. The theorem consumer becomes eligible
again when the owning operations record is repaired; it retains its original
statement and finite-to-finite quotient cases, including n=m and nonflat n>m.

## Validation and operations

Compare production dag_queue results before/after this one-record withdrawal:
before, the definition is stated and the theorem is stage-2-open; after, the
definition is unstated and the theorem is excluded by its missing statement
dependency. Restoring the archived record in memory must restore that readiness.
The definition itself is offered once its existing coefficient prerequisites
land. Refresh generated queues with the ordinary queue tool, and release the
obsolete Q30 consumer claim only after its active worker exits naturally.
Keep historical tries, failure counts and dispatcher state. No failure threshold,
skip, backoff, abandonment, theorem proof or process signal is part of this fix.

Every modified existing file has a sibling backup ending .maint-Q30-thm-coef-finite-hom-1792137803.bak; newly created
records/reports also have initial snapshots. No Lean file changed, so no compiler
or global build is required for this metadata repair. Server commits use Bin Wu's
requested identity and SHEAF_LEAD=L-only under each repository's merge lock.
