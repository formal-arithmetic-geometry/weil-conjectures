# Finite adjunction realization: unpublished dependency

Maintenance of `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`, P4,
2026-10-20. The item remains blocked on publication; this record is not a
claim that its mathematics or its delivery is complete.

## Cause and evidence

The stage-3 queue and worker source checkout include a stage-2 landing that
the worker compile environment does not include. All completed worker runs
inspected, from `1792456572` through `1792469923`, fail while loading the
first import, before checking the retained proof. The dispatcher reported
12 counted failures when this maintenance started; that number is not a
dispatch limit.

The last published green build is
`c0b7c0c3e0196e22606d2593c864ffaf4c2697cd`, published
`2026-10-19T23:01:37Z`. Neither
`lean/Sheaf/SixFunctors/FiniteAdjunctionSystemData.lean` nor
`lean/Sheaf/SixFunctors/FiniteAdjunctionDiagramRealization.lean` exists in
that commit. The two source modules were added by server commit
`66db4d821b`, as landing request `20261020T003020-NC-1242374-159`, at
`2026-10-20T00:30:20Z`. That request is still in
`local/builds/requests/`. Its recorded source hashes match the live files
and the files in the current build copy:

- SystemData:
  `9f39970bfa69a40de9897df807a2ca629e3af6fb9cfe809422e863e9a38b9fc9`.
- DiagramRealization:
  `7f6ee45a5eb82ea315aa0b7dc49fa3303f6e0170be6d54199e2bcbe192706e8a`.

The build copy has compiled artifacts for both modules, but the shared
published directory has neither. The compile service
`tools/remote_compile_set.py`, reached through `~/cc1/rset.py`, resolves
shared imports from `lean/.lake/build/lib/lean`; it does not read
`local/buildtree` or another group's private mirror. Consequently,
unchanged delivery retries cannot supply this missing dependency.

The last completed build record is red at
`ab541687f83177cf8a38c1047f16048ca0b220d4`, reporting an instance synthesis
failure in `Sheaf.AlgebraicGeometry.FormalFunctionsStalk:256`. A later
maintainer build of snapshot `0d5526d52b` was already running when inspected;
its log has successfully built FormalFunctionsStalk and the finite
adjunction modules. It had not finished or published during this check.
The historical red diagnostic must not be treated as evidence that the
current source still has that error.

Independent reproduction on the live, unchanged item:

```sh
SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh \
  lean/Sheaf/SixFunctors/FiniteAdjunctionDiagramRealization.lean
```

Exit 1 in 4.7 seconds:

```text
error: object file '.../lean/.lake/build/lib/lean/Sheaf/SixFunctors/FiniteAdjunctionSystemData.olean' of module Sheaf.SixFunctors.FiniteAdjunctionSystemData does not exist
```

A separate single-file compile of the unchanged SystemData source into
the isolated mirror `local/build/MaintP4FiniteAdjunction1792469667`, using
`tools/lean_file.sh` and the 60-second limit, timed out with exit 124 and
no elaboration diagnostic. It produced no dependency artifact to reuse.
This secondary result does not replace the independently reproduced
missing-import failure. It also does not justify raising the time limit.

The earlier maintenance run `1792467060` ended in provider HTTP 429. That
provider failure is external and is not repaired here. The present
missing-import failure is independently reproducible without a provider
request. No provider, admission, retry or concurrency settings were changed.

## Owner repair required

The root repair belongs to the build/landing owner. Complete a coherent
green publication containing request `20261020T003020-NC-1242374-159`,
including the full compiled artifact families and their compatible import
closure. Repair any current build or batch-check diagnostics through the
normal owner workflow. Check the actual published commit and imported
artifacts, not only a new build timestamp.

The pipeline also needs a durable handoff between live stage-3 source
eligibility and worker dependency availability. Accepted new module
sources currently become stage-3 items before their imports can be loaded
by the worker compiler. The owner should make those landed dependencies
available through a coherent, source-matched compile environment. This is
an artifact-availability repair; it must not introduce a failure-count
cutoff, concurrency cap, admission limit, throttle or dispatch pause.
Changes to dispatcher or landing code are explicitly excluded from this
maintenance task and are described here instead of being applied.

Do not copy selected artifacts out of an unverified build into the shared
published directory. The existing maintainer build was not started,
stopped or otherwise modified by this maintenance session. No global
build was invoked.

## Next worker

Retain the P4 sandbox. Its only Lean change is the existing proof of
`WeilConjectures.FiniteAdjunctionDiagram.structure_isOver`; the two
remaining holes are `coefficientUnit_mem` and
`finiteAdjunctionDiagramRealization`. Historical isolated checks of the
structure-map proof do not certify the whole module.

Start with the required delivery dry run against current sources. A fresh
missing-object diagnostic is infrastructure evidence, not a failed proof
or permission to duplicate the dependency in the packet. Check the
published dependency identity and report the exact missing module if the
environment is still incomplete. Once imports load, freshly compile the
retained item, continue its proof work under the normal brief and deliver
through the normal checks. This maintenance neither proves nor delivers
the item and does not change its statement, DAG, claim or failure count.
