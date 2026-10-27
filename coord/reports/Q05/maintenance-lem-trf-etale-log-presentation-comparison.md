# Q05 delivery dependency repair, 2026-10-24

The repair of returned head 4c52f0f50abf requires
lem-trf-prelog-pushout-log-axiom.stmt_deps to cite the shared definition node.
The launcher batch2/deliver2.py discards dependency-node stmt_deps changes
while returning a successful dry run. The server stage2_delivery.py ownership
checks also permit dependency-node changes only in lean, so changing the
launcher alone would not be sufficient. These reserved tools were not edited.

Maintenance added the existing worker definition record without its lean
binding and added its citation to the prerequisite node on server sheaf-dag.
The two DAG changes were backed up, validated with nt_incremental2.check
(no new findings), and written under coord/.merge.lock with SHEAF_LEAD=L-only.
The first commit --only attempt failed because the new file was not staged;
the following background build captured the exact DAG changes in
834c1e21a3767a82c683e32293a14c17b6278f26 before the retry. This report is the
explicit maintenance commit, also made under the merge lock.

Changed DAG paths:
- dag/nodes/sec-trace-formula/def-trf-prelog-unit-pushout-presentation.json
  (worker definition record, lean removed; no declaration falsely marked landed)
- dag/nodes/sec-trace-formula/lem-trf-prelog-pushout-log-axiom.json
  (only the requested stmt_deps addition)

Server backups are beside those paths with suffix .20261024T151927Z.bak.
The new definition backup is its initial content snapshot.

Verification: the standard delivery dry run passed server compilation of all
three unmodified sandbox modules and preflight, without the stripped-field
note, at a6a683fa2d85cf99596a97df6cad29f0b9d6ace3. Inspection of that immutable
commit confirms both theorem nodes cite the definition, all three lean records
are included, and the item no longer has the log-axiom theorem as stmt_dep.
No Lean files were changed, no global build started, no processes killed, and
no dispatcher state or concurrency settings changed by this maintenance task.

The next worker should deliver the retained sandbox via the normal pipeline.
Keep all three node copies and modules: the newly added base definition has no
lean record until this delivery supplies it as an allowed dependency binding.
Its dependency closure is accepted by server preflight. Line 141 of the launcher
need not change for this item, because its required citation is now on main.
Independent review of the Lean work remains the normal next step.
