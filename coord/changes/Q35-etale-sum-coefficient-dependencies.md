# Q35 stage-2 dependency metadata repair (2026-10-21)

Return L on immutable head faee664b82df requires the three theorem nodes
lem-sp-acyclic-flat-proper-coefficient-model,
lem-coef-etale-open-comparison-data, and
lem-sf-proper-open-coefficient-refinement to remain in proof_deps while
definition-owner nodes replace them in the stage-2 statement dependencies.
The first theorem was already in proof_deps; the other two were missing.

The retained Q35 packet added those two proof dependencies, as requested.
The local delivery wrapper permits additive proof_deps changes, but server
tools/node_fields.py check_statement_change and tools/stage2_delivery.py
classify them as a statement correction and reject the unchanged statement.
Baseline deliver2.py --no-push reproduced that refusal and the consequent
demand for a Statement corrected report section. No mathematical correction
is called for: L explicitly checked the statement verbatim.

Maintenance applies L's dependency correction to the authoritative node on
sheaf-dag. The two references are also added to step 3's uses, which records
the proper coefficient map followed by the open tensor identification, so
proof_deps remains exactly the union of uses. All five proof texts, the
statement, statement dependencies, Lean records and source files are unchanged.
This is a dependency annotation correction, not new mathematics or a review
of the pending stage-2 packet. No landing, review or launcher tool was edited.

Next Q35 worker: retain the saved module and three existing:true definition
owners, refresh the base through the prescribed deliver2.py wrapper, and run
the normal dry run and delivery. Preserve these proof dependencies. No new
statement_change or Statement corrected section is needed. The wrapper uses
the corrected main proof metadata; a stale sandbox proof annotation is not
delivered. The existing return still requires the ordinary independent review.

Original node backup (untracked):
dag/nodes/sec-smooth-purity/lem-sp-etale-sum-coefficient-computation.json.maint-Q35-1792565438.bak
