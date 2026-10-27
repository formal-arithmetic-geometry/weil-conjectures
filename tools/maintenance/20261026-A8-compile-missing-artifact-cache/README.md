# A8 missing-artifact cache repair, 2026-10-26

Item: `Sheaf.SixFunctors.IntegralTensorLeftShiftUnique`, stage 3.

## Cause

The five failures replayed stored environment diagnostics. The shared mirror and
server now contain all three previously missing compiled modules: `Subobject`,
`Etale`, and `FaithfullyFlatDescent`. The compile attachment key combines source
contents, the published-build stamp, and sandbox outputs. Restoring shared objects
does not change that stamp. `lcompile.cacheable` accepted the missing-object rc=1
results, and `_attached.valid` checked outputs only for successes. Consequently,
both normal compiles and delivery compiles reused those failures for six hours.

The delivery cache was `lc77cd097aa745fe9a1dc28a8`; the complete-packet cache was
`leb55757bb0e9e7d7b877b4ad`, dependency signature `a59dafcbe128b7190b1fd655`.
The latter appeared as result file `ba51f2b824f124b0bbab57d2.txt`.
`evidence.json` preserves the original failures and restored artifact fingerprints.
The retained evidence identifies the replay bug; it does not establish why the
objects were absent during the original compile.

## Deployed change

On the launcher machine, changed `/home/ubuntu/weil-launcher/lcompile.py`:

- Exclude Lean's missing-object diagnostic from reusable results, while still
  returning it to the callers attached to that request.
- Apply the current cache policy when validating existing stored entries, so old
  poisoned entries are rejected without editing caches or waiting for publication.

Backup: `/home/ubuntu/weil-launcher/lcompile.py.bak-A8-missing-artifact-20261026`.
This directory versions the exact deployed diff, regression test, and evidence
because the live launcher directory is not a Git checkout. The patch applies to
`lcompile.py` with `patch -p1` from its directory on the pre-fix version.
No landing tool, review service, dispatcher state, concurrency setting, node,
statement, proof, or shared compiled object was edited.

## Validation

`python3 test_lcompile_missing_artifact.py /path/to/lcompile.py` uses an isolated
real attachment cache and detached fixture runner, with no Lean or server calls.
Both tests fail on the backup and pass on the deployed tool. They cover replay
recovery at unchanged source/dependency state, exclusion of new artifact failures,
retention of successful results, and retention of ordinary Lean type errors.

Server import smoke test, through `tools/lean_file.sh` with acceptance limit 60 s
and run limit 300 s: all three imports passed, `Compiled in 2.5 s`.
The scratch source is at
`lean/.sandbox/maintenance-A8-1792977511/ArtifactImports.lean`.

The unchanged full packet passed `lcompile.py --all`: first
`IntegralTensorShiftProperties` in 47.2 s, then `IntegralTensorLeftShiftUnique`
in 50.3 s, exit 0. The resumed worker's delivery compile also returned `[0, 0]`.
Both formerly poisoned cache keys now have successful current results.
The packet's Lean source fingerprints remain identical to those taken before
validation. See the adjacent compile results and `packet-source-sha256.json`.

## Next worker

Keep the preserved proof packet and continue the normal delivery/review workflow.
No mathematical re-plan or statement correction is indicated by these failures.
Current complete-packet result: `ba51f2b824f124b0bbab57d2.txt`, exit 0.
The resumed worker is already continuing its delivery. This maintenance task did
not deliver or land the mathematical packet. If a compile is live, wait for its
command to return before interpreting an older result file as the current result.
