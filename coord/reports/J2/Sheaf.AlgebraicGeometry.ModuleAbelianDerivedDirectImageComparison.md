## What changed

Retired Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison.
Migrated all 14 current consumers directly to its upstream twin with unchanged
import visibility and no changes to public signatures or definition bodies.
UnboundedAbelianExchangeComparison additionally reuses the canonical proved
ModuleAbelianUnderivedExchange theorem instead of rechecking its two identical
private local proofs. The public theorem proof text is unchanged; its helper
reference now resolves to the upstream declaration. This removes duplicate
proof checking and brings the full file under the 60-second limit (48.1 s). The raw
free-source consumer now imports all directly from the upstream module and uses
its identical private evaluation-acyclicity helper. Two duplicate twin imports
are consolidated. Repointed the remaining evaluation DAG attachment and refreshed
the two already-canonical attachments. No source-library or target file changes.

Change record: coord/changes/J2-retire-module-abelian-derived-direct-image-comparison.md.

## Proved and sorry left

The assigned shim has zero holes: zero closed, zero added, zero split off.
Every public consumer proof is preserved verbatim. Two private duplicate
underived comparison proofs in UnboundedAbelianExchangeComparison are replaced
by reuse of the identically stated upstream theorem. No proof is replaced
with sorry.
Two pre-existing consumer holes are unchanged:

- AlgebraicGeometry.Etale.sf_directImage_ctf_open_tor
  (det-cor-sf-direct-image-ctf-open-tor).
- AlgebraicGeometry.Etale.unboundedProperOpenInterchange
  (lem-amb-unbounded-proper-open-interchange).

The other twelve consumers have zero holes. This is a retirement, not a new proof.

## No longer needed

Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison and every active
import of it. The private forwarding wrapper and its alias are unnecessary because
RawModuleFreeSourceAcyclic can import the defining upstream helper directly.
The redundant private moduleAbelianUpperStarIso_unit and
moduleAbelianUnderivedExchange_compatibility proofs in the unbounded consumer
are no longer needed locally; the already-attached canonical upstream theorem
supplies the same step.
No mathematical node or proof dependency is pruned: the three listed nodes remain
attached to their upstream declarations, including ModuleAbelianCoefficientComparison
for the forgetful functor. Five absent consumer archives remain quarantined with
their existing dependencies and are not restored by this retirement packet.

## Where the brief, the DAG or earlier work was wrong

The old saved packet treated the zero-hole shim as an ordinary proving assignment.
The current explicit RETIRE assignment authorizes its removal and migration of all
current consumers. The listed API differences were resolved in current sources:
moduleAbelianForget and the upper-star API are publicly re-exported from upstream
ModuleAbelianCoefficientComparison. Only one of the three listed DAG nodes still
pointed at the Sheaf shim; the other two already pointed at upstream modules.
The unbounded consumer node still prescribed re-elaborating the upstream
underived proof to avoid the old copy collision. Retirement removes that reason;
its proof step and dependencies now record direct use of the existing canonical
underived lemma. This avoids duplicate proof checking without splitting anything.
The current consumer scan adds EtaleGenericDirectImageExchange and finds several
listed consumers already retired or quarantined. Their archive paths and DAG
attachments are preserved; rework restoration must use the canonical import.

## Forced adaptations

Sheaf.Paper.UnboundedProperOpenInterchange is currently held by S2.
The original has no new compiler error: it already imports the canonical twin
separately, so the withdrawn forwarding module contributes no needed API here.
This is the explicit RETIRE import-migration exception, rather than a proof
adaptation justified by a compiler failure. Keeping the original would retain a
reference to the module explicitly withdrawn in deleted.txt. The sole changed
line is removal of the obsolete private import of
Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison (original line 42).
The pre-existing private canonical import stays in its original position.
All statement, definition and proof text is unchanged. The adapted consumer
compiled successfully in the full fourteen-consumer delivery set; the repeated
delivery compiles the minimal import-only version again. No other edits to the
module held by S2 are made.

## Forced adaptations

### Sheaf.Paper.UnboundedProperOpenInterchange
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
