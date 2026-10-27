# NS syntomic conormal: cached storage failure, 2026-10-24

Item: `lem-sfb-syntomic-presentation-conormal-fibre-rank`, stage 2.

The repeated failure was a cached infrastructure error, not a Lean diagnostic.
The prescribed `scompile.py` call still returned ENOSPC during this investigation
although the server had 44 GiB free on `/`, 115 GiB on `/tmp`, and available
inodes. All previous attempts replayed the same `[10.3 s]` output.

`tools/nt_srv_compile.py` computes this saved packet's sandbox cache key as
`56e5116c0473fb6f40cf2c049c5a58b3299f045b` (confirmed with `key_of`, using the
unchanged packet source). Its cached failure was written at
2026-10-24 10:17:11 UTC:

```
{"rc": 1, "out": "resource exhausted (error code: 28, no space left on device)\n\n[10.3 s]", "t": 1792837031.8417647}
```

`INFRA_TEXT` only includes `object file`, `unknown module`, and `No such file`.
Consequently, `kcompile` reuses this rc=1 failure for one hour and sets
`FAILED_IN_DELIVERED`, suppressing fresh-server confirmation. The original
storage failure's specific filesystem cannot be established from the retained
diagnostic. Repeated attempts did not establish continuing storage exhaustion.

During this investigation, the concurrent Q11 maintenance run invalidated 32
Sandbox0 ENOSPC failures, including this exact key, at 10:57:36 UTC. Its manifest:
`/home/ubuntu/weil-launcher-all/maint/Q11-lem-sfb-tame-snc-quotient-resolution-1792839139/cache-invalidation.json`
on the launcher machine. This is Q11's repair; NS did not repeat that mutation.
The original failure remains on the server at
`/home/ubuntu/weil-nt-overlay/kcache/Sheaf.Stage2.Sandbox0/56e5116c0473fb6f40cf2c049c5a58b3299f045b.fail.maintenance-Q11-1792839139.bak`
(SHA256 `191854e92ab4b1b6334729e53e2c453f96c21f63752a6bf1b59790b177451a51`).
The same key's `result.json` now records rc=0, `[2.5 s]`, at 10:58:09 UTC.

NS independently checked an unchanged copy of the saved module using
`SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh lean/.sandbox/maintenance-NS-1792839138/SyntomicPresentationConormalFibreRank.lean`:
exit 0, `Compiled in 2.1 s`, no diagnostics. A `.lean.bak` copy is beside it.
The active worker then passed preflight and compilation and delivered
`a1027a50b50008df3a3cf1d2d75bf20509451aa3` on
`deliver/NS/lem-sfb-syntomic-presentation-conormal-fibre-rank`.
The dry-run head immediately before delivery was `0e1f0d5d084`.

The next worker should retain the existing packet and use current server
feedback. Its mathematics needed no change. Delivery has completed; independent
review and landing remain the normal downstream work.

Protected-tool follow-up for its owner: treat ENOSPC/resource exhaustion as an
infrastructure failure in both failure-cache reuse and `FAILED_IN_DELIVERED`;
do not replay it as a final Lean rejection or suppress server confirmation.
Cover a previously cached ENOSPC result followed by a successful compile and a
real Lean type error that remains cacheable. No protected launcher, review, or
landing tool was edited, and no concurrency setting was changed.
