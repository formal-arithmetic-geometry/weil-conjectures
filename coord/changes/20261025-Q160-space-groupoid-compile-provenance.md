# Q160 stage-2 compiler source selection repair (2026-10-25)

Item: `lem-sfb-flat-space-groupoid-kernels-cokernels`, returned head
`443ecd36ea72`, dispatcher key `lem-sfb-flat-space-groupoid-kernels-cokernels@443ecd36e`.

The repeated failure was in compiler source selection, before preflight. The
last published build commit, `54696378c79742b8b42dd2c10a62ac848ec9535c`,
does not contain `lean/Sheaf/AlgebraicGeometry/SpaceGroupoidModule.lean`.
The current committed source supplies `ModuleGroupoid` and
`SpaceGroupoidModule.forgetToQuasiCoherent`, as recorded by Q120's accepted
`def-sfb-space-groupoid-module`. However, its existing `.olean` is a symlink
to obsolete private-cache entry
`f1a1d82f9a68a51f944d9144ca2de4e79a37cac4` under
`~/weil-nt-overlay/kcache/Sheaf.AlgebraicGeometry.SpaceGroupoidModule`.
The previous selector treated that file's existence as a published build.
It therefore loaded the old multiargument `SpaceGroupoidModule` and missed
the newly landed declarations on every retry.

`tools/nt_source_overlay.py` now selects exact committed source for a module
absent from the published commit, even when an obsolete artifact exists.
Both `source_for_import` and `overlay_sources` apply the same rule. The
comparison is cached by published commit and HEAD; source hashes must still
match their committed Git blobs. Uncommitted edits and mathematical changes
to modules present in the published commit retain the existing policy.
No published artifact or cache entry was replaced or deleted.

Regressions in `tools/test_nt_source_overlay.py` cover regular leftover
artifacts, old cache symlinks, uncommitted additions and edits, first-call
selection of multiple additions, HEAD changes, retirement on publication,
and isolation from modified published modules. All 15 selector tests and
7 source-reader tests pass. The original worker packet, unchanged, now
passes `deliver2.py Q160 lem-sfb-flat-space-groupoid-kernels-cokernels
--no-push`: dry-run commit `83a7fb249e1` passes preflight and compilation.
The dependency also passed `tools/lean_file.sh` in 11.2 seconds with the
60-second limit.

Background build snapshots recorded intermediate changes while maintenance
was running: `394ca55a186631859dc6058c88165a0924571027`,
`1564b541f556be931b0f72f597f55df07305f191`, and
`a5196b1a890c269b872c1a5b60c1620489037f1f` (final functional code and tests).
The maintenance commit records this decision and the selector's provenance
contract. Existing changed files have sibling
`.maint-Q160-1792877531*.bak` backups.

Next worker: retain the repaired packet's single theorem module and existing
definition dependency. Do not re-add the Q120 definition node or its module,
and do not change the mathematics to fit the obsolete interface. Run the
normal dry run and delivery, then allow independent review to proceed. This
maintenance did not push the dry-run packet, mark the node completed, or
alter the existing return entry. No launcher-owned, review, landing, provider,
admission, concurrency, queue, claim, or dispatcher-state setting changed.
