## What changed

Completed the quarantine rework assigned by `coord/rework.tsv` for
`Sheaf.TraceFormula.TwoTermPerfectDeterminant`. Restored the full archived module
at `lean/Sheaf/TraceFormula/TwoTermPerfectDeterminant.lean` without modifying the
archive. Replaced four withdrawn wrapper imports by their adopted source modules:
`DerivedPullback`, `DerivedPullbackRecordedComposition`,
`AffineDerivedPullbackTensorTilde`, and `DerivedPullbackComposition`, all under
`WeilConjectures.AlgebraicGeometry`. The first two remain public imports; the last
two remain private proof imports. The returned packet additionally removes
`set_option warn.sorry false`, which the landing hole scanner reported as an
unattributed hole at line 56. No declaration or proof body changes.
The current server also requires the two file-local
`backward.isDefEq.respectTransparency` options (including `.types`) set to `false`,
matching the adopted derived-pullback modules. Without them, compilation times out
after 60 seconds. Temporary reduced-heartbeat profiling exposed expensive instance
inference at the finite-locally-free fields and recorded composition lift. With these
options the complete module compiles in 19.0 seconds without diagnostics. All temporary
profiling and heartbeat options were removed. All 13 declaration signatures match
the archive; the source hole scanner reports no warnings.

Before this return, the module compiled alone through `lcompile.py` in 8.8 seconds.
The unchanged
archived direct consumer `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction` also
compiled against the restored module in a two-file check (9.9 and 7.7 seconds,
respectively), without errors or warnings. The temporary consumer copy is not
included in the delivery. All 34 quarantined transitive consumers were inventoried;
no consumer signature or body needs adaptation.
The final returned packet and the unchanged archived direct consumer were rechecked
together: both compiled without diagnostics (50.8 and 53.5 seconds respectively).
The temporary consumer copy was then removed; only the assigned module is delivered.

Change record: `coord/changes/D5-two-term-determinant-upstream-import-restoration.md`.
The existing DAG node, its Lean attachment, proof dependencies and unit route are
preserved. No new theorem, definition or module is introduced beyond restoration.

## Proved and sorry left

This delivery repairs the assigned compilation defect and the returned hole-attribution
diagnostic. It closes zero theorem holes and adds zero theorem holes.
The archived module had one hole, and the restored module has the same one:
`AlgebraicGeometry.exists_twoTermPerfectDeterminantData`
(blueprint: `lem-trf-two-term-perfect-determinant`). Its signature, complete proof
in words and whole `by sorry` body are unchanged. No hole is split off, relocated,
or hidden inside data. The concrete determinant models, determinant data, normalized
composition lift, rank-zero case and all comparisons are preserved verbatim.
The repaired file passes the source hole scanner with no warnings and exactly
this one holed declaration; there are no unattributed holes.

## No longer needed

The four imports of the empty withdrawn `Sheaf.AlgebraicGeometry` wrappers listed
above are replaced by imports of the actual source declarations. This is an import
migration, not mathematical pruning: all declared dependencies remain needed and
retained. No node or mathematical module is pruned, and no archive is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The return at head `2c6a1d8ab5` identifies the removed warning-suppression option,
not a second mathematical hole. The repaired source has just the named theorem's
whole-proof `sorry`, with no unattributed token. The current repair queue correctly
identifies the first compilation failure: `derivedPullback`
is unavailable through the withdrawn wrapper. Fixing it exposes the analogous
missing recorded-counit API; that wrapper also needs its source import. Two further
proof-dependency imports still pointed to withdrawn wrappers and are migrated as
well. The mathematical statement and DAG plan are unchanged. Zero live importers
was caused by quarantine; it did not justify withdrawing this module. The 34
quarantined consumers and the direct consumer check are recorded in the change
record. LeanFinder, Loogle, msearch grep and direct source searches found no duplicate
determinant functor that would justify replacing this archived mathematics.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
