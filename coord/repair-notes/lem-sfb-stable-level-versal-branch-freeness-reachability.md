# Stage-2 reachability metadata repair (2026-10-22)

The returned NO delivery b3e3fe16864c added def-sfb-stable-fiber-curve and
def-sfb-stable-versal-level-chart for lem-sfb-stable-level-versal-branch-freeness.
The item is outside the current and former target closure of sheaf-dag. Its new
definitions therefore require import_flags: ["unreachable"]. Stage-2 new-node
ownership forbids the worker from assigning that maintainer-owned field.

Maintenance registers the two original definition records, searches and provenance
verbatim, without their Lean records, and assigns the validated reachability flag.
No Lean module or theorem statement is landed by this repair. The worker must
deliver the modules and Lean records through the unchanged stage-2 checks and
independent review. The definitions are now existing dependency records; add a
lean.note on each and list them under ## Dependency modules in the worker report.

The new-node schema gate (before maintainer metadata is added) and incremental DAG
checks both pass. Full source-record backups are beside the new node files with
suffix .maint-NO-1792664836.bak. The destination files did not previously exist.

The general tooling gap remains: new-definition metadata must be assigned by the
maintainer before reachability validation. Landing and review tools were left
unchanged as required by this maintenance task.
