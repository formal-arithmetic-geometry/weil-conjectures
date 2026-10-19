# Q129 join-translation-resolution maintenance

The repeated failure was provider concurrency exhaustion, concealed by the
launcher's final-answer-only accounting. All 12 completed Q129 runs between
1792194323 and 1792196923 ended with `ERROR: exceeded retry limit, last status:
429 Too Many Requests`, without `last.txt`. Run 1792196231 includes the provider's
`gateway_concurrency_limit` error. The dispatcher replaced this with an empty
`NOANSWER: ` and immediately launched another full worker; maintenance sessions
also bypassed its worker slot accounting. The configured upper bound was 700.

This maintenance restored the complete adaptive-admission dispatcher source on
the launcher from the prepared Q33 maintenance version after finding a partial
installation (`CAPACITY` called but never initialized). Concurrent maintenance
has integrated its reader and state fixes into that source. The deployed helper
uses one reservation pool for workers, readers and maintenance, starts with 16
slots, halves admission on a 429, waits for provider cooldown and grows gradually
on successful answers. Existing sessions drain without being killed. All item
failure counts remain historical and never stop dispatch. The active dispatcher
retains its preexisting loaded code until its next normal start; this maintenance
does not kill it. The separately installed Codex retry supervisor is already
used by subsequent CLI invocations and preserves exact sessions within budget.

Own launcher backup:
`/home/ubuntu/weil-launcher-all/dispatch_all.py.bak-maint-Q129-1792196952`.
The exact restored source snapshot and admission helper are preserved in this
report's evidence directory, alongside request/session identifiers, the original
state snapshot and validation output. The source snapshot includes the concurrent
handoff and state repairs; those maintainers own their canonical server tool
updates. The Q129 evidence copy makes this maintenance change reviewable without
committing another maintainer's in-flight canonical `dispatch_all.py` edits.

Validation: five independent admission/restart regressions pass against the
deployed launcher source. They execute the real main initialization and maintenance
launch path with fake children, cover inherited-session drain, concurrent
maintenance reservations and provider burst reduction/recovery. The existing
11 fake-CLI retry regressions pass. No Lean source, mathematical statement or
proof was changed by this maintenance; no Lean compilation or lake build was
needed. The worker active at inspection was still constructing its Lean packet.

The handoff route note preserves its sandbox, identifies the incomplete JSON
layout, and distinguishes the Q52 stage-1 split and Q78 archived abandonment from
a Q129 return. The item must still complete its statement, compile each delivered
file through the authorized 60-second wrapper, pass the ordinary dry run, and
receive its independent second reading. The historical retry count is not a
mathematical verdict and is not reset.
