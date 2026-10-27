# Maintenance: Q111 / sk-lem-walg-engel

The item is unfinished but pruned from stage 1. Its only caller,
`sk-lem-walg-trace-criterion`, was attached by commit
`9d93a1d8f50beac6620a8af19409305768352a1e` at 2026-10-24 01:01:29 UTC
to `LieSubalgebra.isSolvable_of_trace_mul_eq_zero`. Its slopmaster2 audit is
closed. Engel has full-DAG distance 37 and no unfinished-path
distance. It is absent from the computed stage-1 set and coord/queue.tsv.
Both the queue and landing read the same dag/nodes directory. There is no
side completion to promote; the imported Engel record is not complete.

The landing batch conflated absence from stage 1 with completion and returned
the misleading side/live message. `tools/nt_land_batch.py:296-301,559-572`
needs the launcher owner's correction: distinguish a completed item from an
unfinished pruned item, preserve the exact delivery head, and retire an obsolete
handoff for pruned work instead of returning it for an impossible repair.
The return-first dispatcher bypasses its ordinary off-queue release check.
Neither protected tool nor dispatcher was edited by this maintenance task.

The reader approved returned head `cbb25c0f3ceac5189569d6e12c180c0f39b4b781`. It is preserved at
`refs/superseded/Q111/sk-lem-walg-engel/cbb25c0f3ceac5189569d6e12c180c0f39b4b781`. Only its obsolete return section and Q111 claim were removed.
All other return sections remain byte-for-byte intact. No DAG, Lean, proof,
completion flag, queue eligibility, failure counter, or concurrency setting
was changed. No process was killed. No Lean compilation is needed for this
bookkeeping repair. The retained sandbox is
`/home/ubuntu/weil-newtargets-sandbox/Q111/sk-lem-walg-engel` on the launcher host.

Backups of changed existing files:
- `coord/returns/Q111.md.maint-20261024T085302Z.bak`
- `coord/claims/sk-lem-walg-engel.lock.maint-20261024T085302Z.bak`

Next worker: reuse the archived delivery and retained sandbox if an unfinished
target route reaches this node again. First check reachability and caller
completion; do not infer that Engel itself is proved, re-split to address a
promotion message, or add a permanent retirement/hold record.

Original obsolete return, retained as evidence:

```text
## sk-lem-walg-engel (2026-10-24 07:36 UTC, branch head cbb25c0f3ce)

L: approved by the reader, but the landing refused it: NOT MERGED sk-lem-walg-engel: sk-lem-walg-engel: completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it) Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.
```

## Late push from the already running worker

After the first repair commit `4c4e604e372`, the running repair worker noticed
the removed return and pushed `50ab010f3cb9f72b053520c6e7869aca82f9a9df` before the dispatcher observed the
released claim. The dispatcher then stopped that worker normally at
2026-10-24 08:56:11 UTC (launcher dispatch.log); maintenance killed no process.
The late push has identical item, child and unit records to the earlier
returned head. It too is preserved at `refs/superseded/Q111/sk-lem-walg-engel/50ab010f3cb9f72b053520c6e7869aca82f9a9df` and its delivery ref was
removed with a compare-and-swap under the merge lock. The item remains pruned;
no return or claim was recreated. The prior version of this report is saved at
`coord/reports/Q111/sk-lem-walg-engel-maintenance-20261024.md.maint-20261024T090002Z.bak`. Both historical packets and the sandbox remain reusable.
