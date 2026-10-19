# Maintenance: lem-coef-sheaf-flat-model, 2026-10-16

Cause: the recorded `def-pc-kflat-complex` interface was centralized in the side
`Sheaf.Algebra.Homology.KFlat` source (9fb70d67cc), but both compilation paths
classified every module with a live source as live-only. The server
`tools/nt_compile.py` skipped the changed side source, and the launcher's
`parallel_land.py` omitted it from source snapshots. Imports therefore resolved
the older live artifact while `scompile.py --source` returned the newer side
source. Repeating the item could not repair that selection rule.

Repair: both paths share the source selection in `tools/nt_source_overlay.py`.
`coord/stage2-source-overrides.json` explicitly selects KFlat and its side
forwarding module KFlatIndependentCoefficients. Other frozen live copies keep
their previous published-artifact policy. The updated launcher snapshot tool
is versioned in `tools/launcher/parallel_land.py` and deployed on the launcher;
the local source mirror has been refreshed. No mathematical source, node,
statement, claim, failure count, or live project was changed.

Validation: four source-selection regression tests and three server compiler
integration tests pass. The server tests compile files sequentially through
`tools/lean_file.sh`, with 60 seconds per invocation, and verify the independent
and general KFlat predicates, the forwarding import, and the coefficient
sheafification declarations. The original import-only worker probe now passes
locally without server fallback. The imports of the retained worker draft also
pass on the server. No global build was requested.

Next worker: resume the item's own statement work. Use the recorded
`CochainComplex.IsKFlatIndependentCoefficients` from KFlat; do not ship a private
copy of that dependency or substitute the older predicate. The retained draft
is preliminary and still needs completion and the normal second reading and
delivery dry run. Earlier BLOCKED reports describe the repaired compiler state,
not a current failure. Maintenance evidence and the final commit are recorded
in `/home/ubuntu/weil-launcher-all/maint/NP-lem-coef-sheaf-flat-model-1792138713/REPORT.md`
on the launcher.
