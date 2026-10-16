# Maintenance: coefficient-system comparison readiness

NV maintenance run 1792152040, 2026-10-16.

Repeated stage-2 workers correctly found that the strict varying-ring module-system
category needed to type this item has no usable recorded Lean declaration. The
existing owning node is `lem-coef-semilinear-derived-sections`; its statement
introduces strict systems of module sheaves over an inverse sequence of ring
sheaves, their compatible maps, levelwise exactness, and derived localization.
Specialize that interface to the constant quotient ring sheaves A_n used here.
Both current server repositories have this prerequisite split but with no Lean
binding and no Mathlib match. The original consumer omitted it from `stmt_deps`,
so the bottom-up scheduler admitted the consumer before that category was stated.
The 06:25 and 07:07 UTC delivery-log completions are stage-1 splits, not Lean
statements. The old NK return on the prerequisite is not this item's return;
its later NV stage-1 split is already landed. The prerequisite's own missing
enhanced foundations were separately recorded by ND maintenance.

Repair: add `lem-coef-semilinear-derived-sections` to this item's `stmt_deps`
in the authoritative shared DAG and the isolated side snapshot. Only that field
changes. The mathematical statement, all hypotheses and conclusions, proof plan,
proof dependencies, source, split review, and Lean binding are preserved. A
read-only full statement/proof dependency traversal from the prerequisite finds
no path to this item, so the added edge creates no cycle. The side project reads
`SHEAF_DAG=/home/ubuntu/weil-conjectures-sheaf/dag/nodes`; both copies must agree.
Changes are committed under each repository's `coord/.merge.lock` with
`SHEAF_LEAD=L-only` as Bin Wu <844524296@qq.com>. Original node files have sibling
`.maint-NV-1792152040.bak` backups; this report has the same backup suffix.

Production `dag_queue.Dag.stage2()` reproduced the premature eligibility before
the repair and rejected the corrected record. The prerequisite is not yet
stage-2-ready because its own statement foundations are unstated. This is normal
dependency ordering: historical failure counts remain intact and impose no
retry cutoff. No pipeline tool, brief, timeout, or failure policy changes.
No Lean source was changed, and no Lean compilation or global build is needed.

Next worker: resume through the normal queue once the prerequisite and its
statement foundations have usable declarations. Read the newly published
owning module, and use its strict varying-coefficient system category and
derived evaluation functors. Keep the general small-site/topos setting and
the possibly nonflat quotient maps; fixed-ring towers and diagrams only of
ordinary derived objects are not substitutes. Do not restate the existing
foundation node inside this delivery. The retained NV sandbox contains searches
and a diagnostic report, but no target Lean module or completed dry run.
The evaluated comparison, unit/counit and quotient coherence, bounded-below
descent, and normalization clauses still require the normal statement worker.
The earlier Q25 import repair is separate and remains in place.

Operational evidence, final commits, and queue/claim verification are recorded in
the launcher's `maint/NV-lem-pur-coefficient-system-derived-comparison-1792152040/REPORT.md`.
