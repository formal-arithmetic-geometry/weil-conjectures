# Module import repair for lem-trf-affine-lift-tower-descent

2026-10-24, Q85 maintenance.

The repeated stage-2 failures came from the legacy (non-`module`) headers of
`Sheaf.TraceFormula.SharpeningFanBijection` and its import
`Sheaf.GroupTheory.FineMonoidUnitSplitting`. The required module-mode worker
file could not import the already existing monoscheme resolution-rule and
affine-cover interfaces. The worker could not change the downstream sharpening
node through its prerequisite-only delivery scope; adding that node as a
prerequisite would cycle through its proof dependency on this item.

Maintenance converted both library files to `module`, made their original
imports public to preserve the legacy import interface, and added
`@[expose] public section`. Declaration bodies, signatures, docstrings, and DAG
edges are unchanged. Both files passed `tools/lean_file.sh` separately (60 s
limit), in 3.4 s and 3.7 s. The official `tools/land_set.sh` also passed the
import-pruning checks and registered interface landing
`20261024T031815-maint-Q85-affine-lift-1792811496-4072560`.

A further module-mode import/type probe passed through `tools/lean_file.sh`
in 8.4 s and resolved the existing `Monoscheme.ResolutionInput`, `Resolution`,
`ResolutionComparison`, `SmoothFunctorialDesingularization`, `AffineLiftCover`,
`Tower.toFan`, `FineFan.TowerIdentification`, `sharpIdeal`, `sharpSpaceMap`, and
`fine_monoid_unit_splitting`.

The next worker should import `Sheaf.TraceFormula.SharpeningFanBijection` for
these existing helper definitions. Using definitions exported by that file does
not require using its final theorem or adding its downstream owner to the DAG.
Do not recreate those definitions or add a cyclic dependency. Re-read the live
source using `scompile.py --source` if the read clone still has a legacy header.
The compilation wrapper normally uses the last green published artifacts even
when a live source header has changed. The compiler source-selector repair in
`tools/nt_source_overlay.py` now privately compiles exact committed header-only
legacy-to-module conversions whose declaration text matches the published
source. It rechecks the working source and stops selecting that conversion
after a new publication. Both persistent and fallback compilers use this
selector. Changes to declaration text retain the usual published-artifact rule.
Eight regression tests in `tools/test_nt_source_overlay.py` cover the original
failure, declaration changes, uncommitted changes, cached-source edits,
and a new publication. All eight pass on the server.

The retained Q85 sandbox is an import probe and a diagnostic report; at the time
of inspection it has no node JSON or completed statement. Its initial delivery
dry run therefore correctly reports the missing item node. After checking the
fixed import, finish the actual stage-2 statement and its ordinary node record,
compile and dry-run it, and deliver through the normal wrappers. This maintenance
repair does not state or prove the item's mathematics.

Original library sources were retained beside each file with the suffix
`.maint-Q85-affine-lift-1792811496.bak`. The usual global build still verifies
the registered interface landing; maintenance ran only single-file checks.

End-to-end verification after installing the source-selector repair: the exact
retained Q85 `AffineLiftTowerDescent.lean` probe now exits 0 through scompile.py.
It privately compiles FineMonoidUnitSplitting (2.3 s), SharpeningFanBijection
(4.3 s), the module-mode sandbox probe (1.6 s), and its library-form check
(1.6 s), one file at a time. The printed AffineLiftCover and
SmoothFunctorialDesingularization types are resolved. No published artifact
was overwritten. This confirms removal of the repeated infrastructure blocker;
the import probe remains distinct from the actual item statement to be written.
