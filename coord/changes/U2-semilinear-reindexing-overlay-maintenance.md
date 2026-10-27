# U2 SemilinearExchangeReindexing compile-overlay maintenance

The five repeated stage-3 failures were a private compiler-overlay defect, not a
false statement or an invalid mathematical plan. The completed W2 interface
landing `20261025T203551-L-2828711` moved the reindexing predicates from
`Sheaf.Paper.PurCompletedReductionReindexing` into
`Sheaf.Paper.PurCompletedReindexingData`, after the last green publication.
`missing_dependencies` stopped at any existing published object. Thus it supplied
the new data module while retaining the old compiled owner, and Lean rejected
`AlgebraicGeometry.Scheme.PurCompletedReindexingSquare` as declared twice.

`tools/remote_compile_dependencies.py` now examines the reachable repository
import graph after supplying genuinely missing dependencies. It rebuilds existing
direct importers of those new modules in the request's private overlay, using the
existing committed-source/completed-landing validation. The final overlay is
ordered by its imports. It keeps unrelated newer proof plans behind the published
boundary and never writes to the published build.

The exact retained U2 packet now selects six dependency modules: the five newly
split dependencies and `PurCompletedReductionReindexing`. A broad invalidation
would have selected 887 modules and was rejected before installation.

Validation: all 20 tests in `tools/tests/test_remote_compile_dependencies.py`
pass, including definition relocation through a published importer, unchanged
published bytes, source validation, multiple new imports, private overlay order,
cache reuse, nested relocations on newly discovered import branches, and exclusion of unrelated unfinished proof plans. The service test
pins its mocked run limit to 60 seconds; production limits are unchanged.

Backups of both changed tools are alongside them with suffix
`.bak-maint-U2-SemilinearExchangeReindexing-1792971924`.
No Lean source, DAG statement, proof plan, dispatcher state, landing tool,
admission setting, or concurrency setting was changed by this maintenance.

The full maintenance handoff, including actual Lean verification results, is in
the maintenance workspace's `REPORT.md`.

The unchanged delivery failure was also served from a six-hour local compiler
result cache on the repeated retries. The one cached duplicate-declaration
failure (key `l1ebe51b0b0b840a5672b5c0e-72858d1c4838923ae74299cc`)
was archived with a `.bak-maint-U2-SemilinearExchangeReindexing-1792971924`
suffix. It can no longer mask the repaired server tool on the next delivery.
No compiler frontend or landing tool was modified to invalidate that result.
