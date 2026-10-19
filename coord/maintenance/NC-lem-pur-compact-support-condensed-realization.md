# NC maintenance: compact-support condensed realization

Item: `lem-pur-compact-support-condensed-realization`, stage 2, 2026-10-18.

## Cause

The six stage-2 `NOANSWER` runs reached their 2700-second worker deadlines.
Their logs end in the Codex supervisor receiving SIGTERM (`Stopped: 15`), with
no final answer file. This is not evidence of a provider empty-response error.
Earlier runs were developing the statement and repairing type/universe errors;
the latest saved dry run has a reproducible shared-dependency timeout:

`Sheaf/Paper/CoefficientSystemDerivedComparison.lean: timeout after 60 s`.

Compiling that published side module directly with `tools/lean_file.sh`
reproduced the timeout independently of the item's packet. Its large dependent
structures generated unused `SizeOf` and constructor-injectivity helpers. The
existing local options on `CoefficientSystemDerivedImage` did not disable that
work for the earlier structures, and did not disable `SizeOf` generation itself.
Profiling reached the mathematical declarations without a reported type error;
the generated declaration work pushed the file beyond its compilation limit.

The earlier NC stage-1 stale-assignment response is separate: NG's reviewed
stage-1 split does not complete NC's stage-2 statement.

## Repair

In `lean/Sheaf/Paper/CoefficientSystemDerivedComparison.lean`, add these
module-local compiler options after `set_option autoImplicit false`:

```lean
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
```

All declaration text, structure fields, signatures, bodies, universes, theorem
statements and docstrings are byte-for-byte unchanged after removing those three
lines. The suppressed helpers have no callers in the checked side/upstream Lean
sources. The existing scoped options remain in place. The dependency node
`dag/nodes/sec-smooth-purity/lem-pur-coefficient-system-derived-comparison.json`
changes only in `lean.note`, to explain the repair.

Original source and node records have verified sibling backups ending
`.maint-NC-1792308746.bak`. This handoff is committed with them under
`SHEAF_LEAD=L-only` and `coord/.merge.lock`, as Bin Wu <844524296@qq.com>.

## Validation

All checks ran on the server using `bash tools/lean_file.sh <one-file>`,
sequentially, with the unchanged 60-second per-file limit, nice 19 and two threads.

| Check | Result |
| --- | --- |
| Original dependency at its published side path | Timeout at 60 s |
| Same source with only the three options, in a maintenance scratch module | Pass, 49.2 s |
| Repaired dependency at its published side path | Pass, 46.8 s |
| Dependency rebuilt while checking its direct consumer | Pass, 43.1 s |
| Direct consumer `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | Pass, 32.5 s |

The repaired checks have no errors or warnings. An alternative changing only
`coefficientUnderlying` from `abbrev` to `def` still timed out and was not applied.
No compiler limit, retry/admission rule, concurrency setting, launcher tool,
landing tool or live-project Lean source was changed. No global build was run.

## Next worker

Retain the saved NC stage-2 packet and resume its normal dry run and delivery.
This maintenance repair does not complete or certify the item's own statement.
Earlier packet logs also contain a timeout in the large main module; use a fresh
diagnostic for that module rather than assuming a dependency failure is its error.

During maintenance, the already-running NC worker independently removed the
unused `CompletedCoefficientPushforwardComparison` import and its two instance
attribute lines from its sandbox main module. That sandbox edit is the worker's
work, not part of this maintenance commit. Retain it if its subsequent checks
confirm the import is unnecessary. The shared dependency repair remains useful
for real consumers and prevents its timeout when it is genuinely imported.

Fetch the current dependency with `scompile.py --source` if a shared checkout
lags. Do not weaken statements, invent replacement coefficient categories, or
increase the 60-second limit to handle this timeout. Dispatch stays active and
historical failures remain counted.

Detailed worker/dispatcher evidence, compiler logs and the maintenance commit
are recorded in `REPORT.md` under
`/home/ubuntu/weil-launcher-all/maint/NC-lem-pur-compact-support-condensed-realization-1792308746`
on the Codex machine.


## Follow-up after ten deadline failures (2026-10-18)

The ten completed stage-2 attempts `1792292349` through `1792316925` all end
with supervisor SIGTERM (`Stopped: 15`) at the 2700-second worker deadline.
Their retry files still say `running`, with zero recoveries and no last error;
no final-answer file exists. They contain substantial compiler output. No
provider 429, gateway concurrency limit, or provider empty-response failure was
found. The historical first NC run `1792292289` is the separate stale stage-1
assignment described above. The dispatcher failure count is retained.

The earlier generated-helper timeout repair is commit
`9f36a87d8e7978d67a7901e719af5a69891a1c27`. The latest compiler evidence exposes a
different published-dependency failure: `CoefficientRingedSequenceSite` fails
at line 151 with `?u + 1 =?= max (t + 1) u`, followed by 100 errors. A direct
server `tools/lean_file.sh` compile reproduces it in 4.8 seconds, independently
of the worker's saved packet. Its direct consumer
`CoefDerivedSystemEvaluationCalculus` has the same failure after the first
module is repaired.

The high-priority generic instance
`CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` assumes
coefficient Hom universe `u + 1`. Here the intended coefficient universe is
`max u (t + 1)`, with independent site and coefficient universes. Instance
search selects the generic instance before the existing coefficient-universe
sheafification and leaves insoluble successor metavariables. These are
instance-selection failures, not missing mathematical constructions.

Both published side modules now contain, after their options:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

A comment explains the choice. The existing coefficient-universe instances
then discharge the same obligations. Removing only the added blank line,
comment, and attribute recovers each original source byte for byte. No
mathematical declaration, signature, field, hypothesis, body, universe or
docstring was changed. No DAG statement or record needed changing.

Validation used `bash tools/lean_file.sh <one-file>` on the server, sequentially,
with the unchanged 60-second limit, nice 19 and two threads:

| Check | Result |
| --- | --- |
| Original `CoefficientRingedSequenceSite` | Fail, 4.8 s, universe constraints |
| Scratch copy excluding only the generic instance | Pass, 6.8 s |
| Repaired published `CoefficientRingedSequenceSite` | Pass, 6.2 s |
| Repaired sequence-site rebuilt for its consumer | Pass, 7.8 s |
| Consumer before the same repair | Fail, 16.6 s, same universe constraints |
| Consumer scratch copy with the same exclusion | Pass, 44.4 s |
| Repaired published `CoefDerivedSystemEvaluationCalculus` | Pass, 46.4 s |

Successful checks contain no errors or warnings. Original server source files
and this handoff have sibling backups ending `.maint-NC-1792319639.bak`.
Diagnostic scratch copies with `.bak` originals are under
`lean/.sandbox/maint-NC-1792319639/`. An initial diagnostic excluding unrelated
integral-operation instances failed because those names are not imported;
that diagnostic was not applied to either published source.

The original sandbox `report.md` was backed up to
`report.md.maint-NC-1792319639.bak` and appended with the dependency diagnosis
and source-refresh instructions. Its existing mathematical report was retained.
Detailed logs and `REPORT.md` are on the launcher machine at
`/home/ubuntu/weil-launcher-all/maint/NC-lem-pur-compact-support-condensed-realization-1792319639/`.

Next worker: preserve the saved NC packet, obtain current server sources with
`scompile.py --source` if a shared copy lags, and run the required dry run.
Do not duplicate the repaired dependencies merely to fix this instance-selection
failure. Diagnose fresh main-module errors/timeouts separately; this maintenance
does not deliver or certify the item's stage-2 statement. The main statement
and its remaining mathematical work belong to the worker.

No launcher-owned file, compiler limit, landing/review tool, provider handling,
concurrency setting, dispatcher state, assignment or failure count was changed.
No process was signalled and no global build was run. The maintenance commit
uses `SHEAF_LEAD=L-only`, `coord/.merge.lock`, and author/committer
`Bin Wu <844524296@qq.com>`.

Source repair commit: `66a202455b2663b759f3938417d6abbafba3f41c`. While
maintenance was validating, the normal `restore_pruned_imports.py` job included
these two already-edited source files in its commit at 18:39:37 +08. Its code
uses `coord/.merge.lock`, `SHEAF_LEAD=L-only`, and the required Bin Wu identity.
The two source diffs match this repair exactly. The same commit also contains
three import restorations made by that job, outside this maintenance's edits.
The attempted maintenance source commit detected the advanced source baseline
and stopped before staging anything. This follow-up commits only the handoff.
