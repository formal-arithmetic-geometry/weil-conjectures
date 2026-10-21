# E1 IntegralBoundedKunnethExact: unpublished import compilation

2026-10-21 maintenance repair. No mathematical source or declaration changes.

The retained E1 candidate failed before elaboration because the last green build
(`cc9c0f6fc42325e9acc8f9d18d91d6659cbbd8f3`, published 2026-10-21 06:02 UTC) does
not contain the nine modules landed by F2 in `0fbd1db7095`, landing
`20261021T061041-L-1689610`. The new modules include
`Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` and its eight supporting
modules. The publisher was occupied by the upstream-sync build begun at 06:23 UTC.
Their committed sources existed, but every E1 retry read only published artifacts
and the worker's own compiled outputs. Repeating the same request could not help.

`tools/remote_compile_set.py` now prepares missing committed repository imports
with `tools/remote_compile_dependencies.py`. It compiles only the absent imports,
in dependency order, using its existing private overlay, single-file timeout and
content cache. Caller artifacts and scheduled delivery sources take precedence.
Repository sources come from one HEAD snapshot and must match the working tree;
uncommitted/untracked sources and import cycles produce explicit diagnostics.
Dependency compiler failures are returned as failures of the requested job with
the actual failing module and commit identified. No object is published, and no
buildtree object is substituted for a successful compile.

This changes the worker compile service, not the dispatcher, review/landing
services, concurrency settings, admission or publication. All files keep their
existing per-file timeout. There is no new wait or concurrency limit.

Validation: six regression checks cover dependency ordering, the published-build
boundary, caller precedence, dirty sources, cycles, cache reuse, and propagation
of dependency compiler failures. The existing admission regression also passes.
The affected Lean dependency chain is checked one file at a time with
`SHEAF_GROUP=MAINT-E1-Kunneth tools/lean_file.sh` (60 s per file). Full evidence and
the resulting commit are recorded in the maintenance run's REPORT.md.

The next E1 worker should retain its candidate and run its normal deliver3 dry
run. It no longer needs to copy dependency source files into the delivery or use
scratch interface placeholders. The compile service supplies committed missing
imports privately until the publisher catches up. Ordinary Lean diagnostics,
including errors in the candidate itself, remain the worker's task.
