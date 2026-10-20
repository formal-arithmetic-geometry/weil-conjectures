# G4 projection tensor coefficient comparison maintenance

Item: `Sheaf.Paper.ProjectionTensorCoefficientComparison`, stage 3.
Dispatcher key: `Sheaf.Paper.ProjectionTensorCoefficientComparison@new`.
Date: 2026-10-20. The original missing-import failure is resolved by the normal
green publication completed during this investigation. The item is not delivered;
fresh full-file checks now reach the 60-second elaboration limit.

## Cause

The queue and workers see a new stage-2 source landing before the worker compiler
has its dependencies. This is a source/publication mismatch, before elaboration of
the retained proof, rather than a mathematical failure of the item.

The dispatcher state reported 11 tries at maintenance dispatch. All 16 completed
worker runs inspected, from `1792455760` through `1792470191`, end on the same
missing `Sheaf.Paper.ProjectionCoefficientTensorTotal.olean`. The first run spent
117 minutes on the item; subsequent unchanged retries could not supply its import.
The intervening maintenance run `1792468330` ended with an unsupported-model
provider response. That earlier provider issue is external, was not changed here,
and is not needed to reproduce the current missing-import failure.

Server commit `49bfc4e35c` added the dependency and this item in stage-2 landing
`20261020T001852-NK-1149925-144` at `2026-10-20T00:18:52Z`. Its request was pending
in `local/builds/requests/20261020T001852-NK-1149925-144.json` when inspected.

At the start of maintenance, the last published green build was
`c0b7c0c3e0196e22606d2593c864ffaf4c2697cd`, published
`2026-10-19T23:01:37Z`, before that landing. It had no dependency artifact.
`tools/remote_compile_set.py`, entered through `~/cc1/rset.py`, resolves shared
imports from `lean/.lake/build/lib/lean`. The group's server compiler uses the
same published build plus its own mirror; the new dependency was landed by NK,
not G4. Neither path imports arbitrary outputs from `local/buildtree`.

Historical builds failed in unrelated modules, including
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`,
`Sheaf.Paper.CompleteResidueCohomologyBounds`, and
`Sheaf.AlgebraicGeometry.FormalFunctionsStalk`. The last completed build record at
the start was red at `ab541687f83177cf8a38c1047f16048ca0b220d4`, with the FormalFunctionsStalk
instance error. Those historical errors do not establish a current source defect.

The already-running maintainer build of snapshot
`0d5526d52bd6abe57f6831e3c80880890a1ee2cb` compiled all 31,817 jobs successfully,
passed its checks and published normally during this investigation. Its log records:

```text
Built Sheaf.Paper.ProjectionCoefficientTensorTotal (31s)
Built Sheaf.Paper.ProjectionTensorCoefficientComparison (43s)
Build completed successfully (31817 jobs).
```

`local/builds/published.json` now records that snapshot as green, with result time
`2026-10-20T04:51:51Z`; buildloop recorded exit 0 at 12:53:53 +08. Its `verified`
list includes `20261020T001852-NK-1149925-144`. The full `.olean`, `.olean.server`,
`.olean.private`, `.ir` and `.ir.sig` families are now present in the published
directory. Both sources match the published commit, build tree and landing record:

| Module | SHA-256 of source |
| --- | --- |
| ProjectionCoefficientTensorTotal | `4e2114989e1fb7afec96c9d119b2683e4d5284734d9f0dc2ef1716f06ee0451b` |
| ProjectionTensorCoefficientComparison | `295d930c0e98339e34276d25e0a9ddbcea98f95e11a7c04b2d01f1a7f7aa046c` |

Verification used full byte comparisons. No selected build-tree artifacts were
copied into the published directory.

## Verification performed

Before publication, reproduced independently on the unchanged live server source:

```sh
SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh \
  lean/Sheaf/Paper/ProjectionTensorCoefficientComparison.lean
```

Exit 1 in 2.0 seconds, at import loading:

```text
error: object file '.../lean/.lake/build/lib/lean/Sheaf/Paper/ProjectionCoefficientTensorTotal.olean' of module Sheaf.Paper.ProjectionCoefficientTensorTotal does not exist
```

A separate one-file dependency compile used `tools/lean_file.sh`, the unchanged
dependency source, the 60-second limit, and isolated mirror
`local/build/MaintG4Projection1792470606`. It exited 124 after 60 seconds and
produced no `.olean`; only its `.src` marker remains. This does not replace the
independently confirmed missing-import cause or certify a module defect.

After publication:

- A module containing exactly the item's five public imports compiled in 8.3
  seconds, exit 0, with `tools/lean_file.sh` and the 60-second limit. The probe and
  its `.bak` are in
  `lean/.sandbox/maintenance/G4Projection1792470606/PublishedImportCheck.lean`.
- The unchanged live item compiled with the same tool and limit reached exit 124,
  with no missing-object diagnostic. This is a new elaboration-time problem,
  distinct from the original infrastructure failure.
- A maintenance copy of the retained worker packet likewise reached exit 124.
  The original worker file was not edited. The server copy and its `.bak` are at
  `lean/.sandbox/maintenance/G4Projection1792470606/ProjectionTensorCoefficientComparison.lean`.
- A bounded profiling pass on the unchanged live source, with only profiler
  options added to an isolated copy, reached the same limit. Its trace shows
  definitional equality expanding `completedIntegralCoefficientSheafUnrestricted`
  through `limit (integralCoefficientSheafSystem ...)`; this is a lead for further
  profiling, not a certified diagnosis of the whole timeout. The source and its
  pre-instrumentation `.bak` are at
  `lean/.sandbox/maintenance/G4Projection1792470606/SourceProfile.lean`.

No global build was started. No existing process was stopped, signalled, or
modified. Publication was performed by the original maintainer process.

## Changes and owner repair required

No Lean, DAG, brief, dispatcher state, claims, failure counters, retry settings,
provider settings, review service, or landing tools were changed. Server additions
are the isolated diagnostic files above and the maintenance record:

`coord/reports/maintenance/G4-ProjectionTensorCoefficientComparison-1792470606.md`

The immediate environmental repair was the coherent green publication containing
landing `20261020T001852-NK-1149925-144`. This occurred through the existing owner
workflow and was verified here. No module or tool mutation was needed to resolve
the original missing import. The new full-file timeout remains uncorrected and
must not be described as a delivered or freshly verified proof.

The pipeline also needs the worker compile environment to provide coherent,
source-matched artifacts for accepted dependencies exposed to stage 3. Record
the concrete source/artifact identity across that handoff. Dispatcher and landing
tool edits are expressly excluded by this maintenance task, so this needed change
is reported here for their owner. Do not implement a failure cutoff, concurrency
cap, throttle, admission limit, or dispatch pause.

## Next worker

Retain the existing sandbox. Its Lean file SHA-256 at inspection was
`f5106c856addcc933f7087a979a8755c9a19f72a1c734309a18acecf36d62f58`.
It contains two private helpers, two proof-only imports, and a proposed proof of
`WeilConjectures.ProjectionTensorCoefficient.good`. This is retained, unaccepted
work: fresh whole-file verification now reaches the 60-second limit.

The four remaining explicit holes are:

- `WeilConjectures.ProjectionTensorCoefficient.ordinary_existsUnique`
- `WeilConjectures.ProjectionTensorCoefficient.completion_isIso`
- `WeilConjectures.CompactSupportCoefficientTensor.integral_existsUnique`
- `WeilConjectures.CompactSupportCoefficientTensor.rational_existsUnique`

Begin with the required delivery dry run against current sources. The missing
dependency is now published and the five-import probe passes. Profile and repair
the definition the elaboration timeout unfolds, adapt its consumers if required,
and compile each file within 60 seconds. Do not raise the limit or split files to
evade it. Continue the normal proof/delivery work. Do not
duplicate the dependency, alter its statements, remove its required public import,
or count this maintenance report as a proof or delivery.
