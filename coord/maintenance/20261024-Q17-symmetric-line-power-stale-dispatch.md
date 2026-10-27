# Q17: completed symmetric-line power assignment

The repeated stage-1 BLOCKED answers were a stale queue publication, not a
mathematical failure. Q79's accepted split landed as a688bd59bda at
2026-10-24 01:38:56 UTC (delivery 5f599c1ab57, independent reviewer
NT-cc-Q79-5f599c1ab). The node is split/reviewed/pass and its stage-1 repair
order is resolved. Both dag_queue.stage1_completed and claim.node_finished
with stage 1 return true. There is no Q17 delivery branch or open item return.

At diagnosis, the live server's four generated queue files excluded the item,
but HEAD and the launcher's shared clone still included its stage-1 row.
The dispatcher reads the live queue for new work, but uses the shared clone's
coord/queue.tsv in _listed when restarting a held claim. Q17 retained the
claim taken at 01:38:59 UTC, three seconds after Q79's merge. This mismatch
kept restarting workers that correctly obeyed the live-wins rule.

Maintenance publishes only the item's removal in coord/queue.tsv,
coord/queue.md and the two queue-batches TSV files, adjusting the two Markdown
counts. The committed changes use HEAD 4fecb11e005ba23e936e14301bae4ef7f16c576e as their baseline. All
unrelated, uncommitted generated queue changes are preserved. Each queue file
has adjacent live and HEAD backups with suffix .maint-Q17-symmetric-line-power-20261024.bak.

The accepted node, repair order, Lean module, and worker sandbox are preserved.
No compiler or Lake build was needed. The six existing stage-1 repair queue
tests pass. No launcher, review-service, or landing-tool code was changed.

Launcher follow-up: reconcile held claims against the same live queue used
for scheduling instead of relying on an older committed clone; publish queue
removals consistently with completion records. This is a state-consistency
fix, not a failure-count gate, delay, admission limit, or pause. Protected
launcher/landing tools are outside this maintenance change.

Handoff: stage 1 is complete. Preserve Q79's split and the resolved repair
order. Do not create a duplicate split, reopen the repair order, fabricate an
ATTACH from the sorried Lean theorem, or submit an unchanged report-only
delivery. Further stage-1 work needs an explicitly released repair order.
