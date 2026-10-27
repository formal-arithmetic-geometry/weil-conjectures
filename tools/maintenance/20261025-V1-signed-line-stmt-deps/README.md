# V1 SignedLineDerivedBaseChange dependency packaging repair

The return of head `606221785ab` required adding
`def-pur-signed-line-derived-action-data` to the item's `stmt_deps` while keeping
its statement unchanged. `/home/ubuntu/weil-launcher/deliver3.py` included
`stmt_deps` in its writable fields only when the statement changed. The repair
compiled and its dry run passed, but the generated commit silently omitted that
dependency, reporting `fields not yours to change were NOT delivered: ['stmt_deps']`.
Forty counted failures were the same tool mismatch, not a mathematical failure.

During this maintenance a concurrent maintainer deployed the narrow fix at
2026-10-25 16:44:46 +08: include `{"stmt_deps"}` in the packager's `allow` set
independently of `changed_stmt`. The runtime, integrity manifest and pristine
snapshot all have SHA256
`52e27ec90dc4261e11ea49aa567e359fd6ba319defc0b1f6b636564a22ac83ac`.
`deliver3.py` is that deployed snapshot; `deliver3.py.bak` is the pre-fix backup;
`deliver3.patch` is the exact difference. No launcher or server runtime code was
edited by this maintenance session after observing the concurrent deployment.

The server already validates added DAG edges in commit `c10a0ed635e`:
dependencies must name nodes and must not create a new cycle. The shared validator
still emits a misleading statement-correction advisory when a dependency edit
accompanies a stage-3 proof edit; it reuses a stage-2 correction validator. That
finding is advisory, so it does not block this repair. The landing tools were not
changed. A future authorized correction should distinguish statement text or
statement_change edits from dependency-only edits in `tools/stage3_delivery.py`
`check_nodes`, retaining the current edge validation and ordinary proof ownership.

Validation:

- `test_stmt_deps_packaging.py` runs the actual packager in disposable Git
  repositories, intercepting preflight to inspect its generated commit. It fakes
  compilation, transport and service calls; it never runs Lean or touches live
  delivery branches. The old source fails three dependency-preservation checks;
  the deployed source passes all seven tests. The statement-change guard,
  maintainer metadata and tool approval pruning are preserved. Missing dependency
  and cycle findings remain enforced by the actual server validator.
- `inspect_packet.py` reads the retained packet against current main. The statement
  is unchanged; the requested definition owner exists in the 20 new nodes; the
  duplicate node and module are absent; step 2 and proof_deps name the existing
  normalized-pullback theorem. All added edges pass validation. The packet has
  18 Lean modules. See `packet-validation.json`.
- The active worker recompiled the item without warnings in 13.8 seconds, result
  `803e88e9b67dc4a7a18cce7d`, and started its normal full delivery. This session
  started no competing delivery, did no mathematics, changed no Lean file, added
  no concurrency limit, and stopped no process.

Run on the dispatcher machine:

```sh
WEIL_DELIVER3_SOURCE=/home/ubuntu/weil-launcher/deliver3.py \
  python3 -W ignore::ResourceWarning test_stmt_deps_packaging.py -v
WEIL_DELIVER3_SOURCE="$PWD/deliver3.py.bak" \
  python3 -W ignore::ResourceWarning test_stmt_deps_packaging.py -v
python3 inspect_packet.py
```

Run archived regressions on the server:

```sh
SHEAF_TOOLS=/home/ubuntu/weil-conjectures-sheaf/tools \
  python3 -W ignore::ResourceWarning test_stmt_deps_packaging.py -v
```

The old BLOCKED note is obsolete. Keep the current repair packet and normal
review/claim flow. The active delivery or a retained pre-existing dry run may
still be running; inspect their result before starting another attempt. Do not
alter the statement to make a dependency field eligible, remove the requested
dependency, recreate the duplicate theorem, or delete the return manually.
