# NE finite smooth adjunction: source metadata repair

Item: lem-pur-finite-smooth-adjunction-general-base, stage 1.

The 2026-10-16 route return required the current blueprint diagonal/deformation
proof, but left source.document naming SGA 4 XVIII. Existing-node source is
maintainer-owned in tools/node_fields.py. deliver.py correctly preserves it;
review_split.py correctly rejects it under the no-SGA route lock. Consequently
workers could repair their proof and sandbox source but could never deliver it.
The five repeated BLOCKED results were a maintainer metadata defect.

Refreshed only the authoritative source field to the current blueprint finite
smooth-purity section, identifying its orientation and coefficient-reduction
proof places. This applies the route return, without accepting the pending
split. Statements, dependencies, status, unit bindings and review fields remain
for the normal worker/second-reader/maintainer review path. The arbitrary-field
adaptation must still be justified there; this metadata repair does not certify it.

The live DAG and isolated side snapshot both need this field: sync_newtargets.py
imports live maintainer-owned metadata and would undo a side-only repair.
Each changed existing node has an adjacent .maint-NE-source-1792171621.bak.
No Lean files or pipeline validation rules changed. No compiler or Lake ran.

Next worker: keep the retained NE sandbox, use the normal deliver.py --no-push
command after fetching the new baseline, and proceed through the independent
second reading when it prints OK. Historical SGA-source failure logs are stale
after this repair. Do not drop the route lock or relax source-field ownership.
The full maintenance validation and commit IDs are in the launcher's REPORT.md
under maint/NE-lem-pur-finite-smooth-adjunction-general-base-1792171621.
