# NR supported-product dependency maintenance, 2026-10-26

The stage-2 item `lem-per-noetherian-supported-product-calculus` repeatedly failed
inside mandatory upstream imports, before its own module was checked. Its statement
and proof plan did not cause the reported graph-square failures.

`1bdfa420dba` changed `sfGraphWordProjection` to call `sfGraphProjectionWord`.
The first, middle and second graph-square proofs still unfolded the old inline body.
Their simplification steps need to unfold the new helper and drop obsolete simp
arguments. The second-square correction was committed as `9779daa4de1` under the
merge lock; equivalent first/middle corrections landed concurrently in `850f4a0f24e`.
All three repairs were independently checked in this maintenance sandbox with
`SHEAF_GROUP=MaintNRSupportedProduct tools/lean_file.sh`, one file at a time, against
current dependency artifacts: second 33.7 s, middle 33.6 s, first 41.5 s. The middle
square's axiom print contained only propext, Classical.choice and Quot.sound.

The normal minimal import of `PurEtaleClosedConstantTensor` then passed scompile.py.
A full packet dry run exposed a second mechanical error at
`ScalarEvaluationTransposeExistence.lean:87`: the current
`sequenceModulePullbackEvaluation_isIso` no longer accepts the final `hδ` argument.
Remove that application argument; retain the private helper's hypothesis as `_hδ`
so the unused-variable linter stays clean. The complete repaired file passed
lean_file.sh cleanly in 47.3 s, with the current sequence-evaluation helper compiled
first in the same private mirror. No public statement or mathematical construction
changes, and no new sorry or axiom is involved in these repairs.

While this last check ran, the landing process took out the four broken proof
deliveries in `6e7468593d5`. Their current library files are restored statement
versions; this maintenance does not reinstate the returned deliveries. The adjacent
`.patch` preserves all four tested mechanical corrections relative to the original
proof files. Upstream proof workers should rebase these corrections onto their
returned packets and use their normal compilation/delivery path.

Original sources and scratch revisions are retained as .bak files. The canonical
second-square original is
`lean/Sheaf/AlgebraicGeometry/SfGraphSecondProjectionSquare.lean.maint-NR-supported-product-20261026.bak`;
the scratch originals and tested revisions are under
`lean/.sandbox/MaintNRSupportedProduct/`.

The local compile-attachment cache tracks only the published-build stamp, so it
retains an upstream failure after the source snapshot changes. Only this NR item's
completed failed-result cache entries were renamed to .bak to permit fresh checks.
A launcher-owner follow-up should include the server source-overlay fingerprint in
the dependency cache key, or invalidate dependency failures when that fingerprint
changes. Launcher and landing tool code was left unchanged.
