# Maintenance: def-cbc-completed-exchange-map, 2026-10-16

The repeated BLOCKED results are caused by an unusable published statement
dependency, not by permission, search, compiler or timeout failures. The current
bottom-up brief correctly prevents the target worker from stating another DAG
node. The queue incorrectly regarded the dependency as usable solely because its
Lean binding was present.

The published completed open comparison cbcCompletedExchange uses cbcCompletedPullback, whereas its recorded statement prerequisite def-weil-pbc-completed-pullback and the proper completedExchange factor use AdicCoefficientDatum.completedPull. These functors are not definitionally equal, and the recorded modules expose no canonical natural transport preserving their ordinary-to-completed units. Thus the two prescribed factors of def-cbc-completed-exchange-map cannot compose. The prior reviewed Lean binding does not provide the dependency interface claimed by the node and must not count as stage-2-ready.

The Q03 binding was committed/promoted in stage-2 batch
99b43b65c9bb433198d3d9294464709d, side commit d386fe8052, and reviewed on
2026-10-16. Previous NR deliveries of the target did not publish a usable
replacement: NR's return on 7d1fe3550b identifies duplicate declarations in its
alternative pullback modules; the current target has no Lean binding or module.
Q23's preserved scratch rfl failure only disproves definitional equality. The
missing canonical transport was established by reading the actual constructors,
the recorded declaration lists, and successful current-server source reads.

Repair: withdraw only the defective prerequisite's lean and reviewed_lean fields
in the authoritative live DAG and isolated side DAG. Preserve the stage-1 split,
review, statement, proof plan and dependencies. Archive both withdrawn records
in the sibling invalidated-lean.json report. Leave published Lean source and
artifacts available to existing consumers. A coord/repair-notes record uses the
normal claim handoff to give any next claimant the exact stage-2 repair below.

Repair this owning prerequisite in stage 2, keeping its mathematical statement and quasi-compactness/completeness hypotheses. Publish the canonical completed open comparison on the recorded d.completedPull presentation, or publish an explicitly normalized natural transport from cbcCompletedPullback and use it to expose that comparison. Compare the actual completed coefficient maps, derived pullback counits and ordinary-to-completed units; preserve the finite quotient transitions and ordinary adjoint-mate normalization. An arbitrary endpoint isomorphism, extra comparison hypothesis or existing:true alias of the old theorem does not repair this defect. Retain the old public API for existing consumers. Read Sheaf.Paper.CompletedPullback, CompletedTowerPullback, CompletedExtensionZeroComparison and CompletedBaseChangeMap. Validate a consumer composing the actual proper and open factors for arbitrary scheme base change, with no extra hypotheses. Use a new side-only module if changing a side copy of a module also present in the live library would leave compilation resolving the published live interface. Compile one file at a time with the 60-second wrapper; never lake build. Land through the normal independent stage-2 review. The target worker resumes only once the prerequisite has a usable reviewed Lean binding.

Validation: with the prior binding the target is stage-2-open and the dependency
is stated. After withdrawing it, the dependency is stage-2-open (all its statement
prerequisites are stated) and the target is no longer stage-2-open. Restoring the
old binding in memory reopens the target. Refresh the generated side queue and
release only the now-ineligible Q23 target claim with a non-abandonment reason.
This is bottom-up readiness bookkeeping; no failure counter, failure threshold,
retry limit, dispatcher policy or mathematical statement changes.

Every changed pre-existing file has a sibling .maint-Q23-1792137457.bak; new
reports/repair-note files also have snapshots. Commits use Bin Wu's requested
identity under each server repository's merge lock. No Lean file was changed,
so no Lean compile or global build is needed. No process was signalled.
The canonical transport itself remains the prerequisite worker's authorized
stage-2 work; this maintenance fixes the false completion and repair handoff.

Handoff validation found that claim.py created the full repair entry for NV, but the dispatcher initially started that newly claimed prerequisite as new without inlining its return. The standing coord/brief-stage2.md now explicitly requires workers and second readers to read any released stage-2 repair note before accepting an existing declaration, and to validate the recorded consumer. This makes the repair diagnostic available through a document every stage-2 worker/second reader already reads. Its backups carry the .maint-Q23-1792137457-handoff.bak suffix. No dispatcher process restart, task cancellation, or message to a worker was used.

The first NV attempt actually proposed existing:true for the unchanged withdrawn theorem; dry-run 9b03796223 accepted it. tools/stage2_delivery.py now rejects an existing alias whose module and declared names are only those explicitly invalidated by an active stage-2 repair note. The check reads the note from the immutable base commit. New modules, different published interfaces, newly recorded transport declarations and resolved repairs remain subject to normal review. The note now stores the invalidated module/declaration list. This is a narrow data-validation guard against reinstating a known defect, not a failure-count restriction. Regression tests use the complete delivery reader, with no Lean build. Guard edits have sibling .maint-Q23-1792137457-guard.bak files.
