# ModuleInverseImageAdjunction maintenance, 2026-10-17

Item: `Sheaf.CategoryTheory.ModuleInverseImageAdjunction`, stage 3, group B2.

The ten failures counted under `Sheaf.CategoryTheory.ModuleInverseImageAdjunction@`
were fatal Codex HTTP 429 exits without `last.txt`, not ten failed Lean proofs.
The ten run IDs were 1792195557, 1792196280, 1792196319, 1792196368,
1792196672, 1792196711, 1792196800, 1792196864, 1792196923, and 1792197005.
Two of those logs already contain successful `deliver3.py --no-push` output.
An empty NOANSWER concealed the transport diagnosis and caused fresh attempts
to repeat investigation of a repair already present in the retained sandbox.
The earlier five-failure maintenance session also ended with HTTP 429.

The actual upstream compatibility error was:
`Unknown identifier AlgebraicGeometry.adjunctionOfLinearLifts`.
The private helper moved into
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`.
`import all Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction` imports
the retired re-export wrapper and cannot expose the original private helper.
The retained repair correctly uses a proof-only `import all` of the source
module. Its statements, definitions, and mathematical route are preserved.

During this investigation the normal landing pipeline accepted that repair as
`1f828626cfa78fefe8ed7e779a679addc2b18875`, landing
`20261017T003413-L-3312317`, reviewed by COMPILER. The item has no remaining
textual sorry; its B2 return and claim were removed and it left the queue.
This maintenance session did not write or deliver a new mathematical proof.

Validation: the landed file compiled on the server with
`SHEAF_GROUP=maint-B2-1792197030 SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh
lean/Sheaf/CategoryTheory/ModuleInverseImageAdjunction.lean` in 10.5 seconds.
The retained worker logs also contain successful axiom probes (only propext,
Classical.choice, Quot.sound) and direct-consumer checks. No lake build was run
by this maintenance session. A global batch build remains the normal final
landing verification; single-file compilation alone does not certify that build.

Concurrent maintenance work on the shared launcher integrated provider-failure
classification and adaptive provider admission in `dispatch_all.py` and
`codex_capacity.py`. This session's earlier diagnostic-only prototype was
superseded by that shared integration. The retained regression test exercises
the actual reaper with a mocked capacity tracker and no processes or SSH:
missing/empty final answer with a fatal 429, preservation of failure counts even
at 10000, preservation of valid DELIVERED output, and missing-log handling.
Together with `test_dispatch_failure_classification`, 12 tests pass. Launch
eligibility is not limited by an item's failure count. Provider rejection does
not establish a mathematical failure. Source edits to an already running
dispatcher require its owner's normal activation/reload procedure; this session
did not stop or restart any process.

The integration test is archived beside this note's supporting files under
`tools/maintenance/20261017-B2-module-inverse-image-adjunction/` and runs on the
dispatcher host with its active launcher directory in PYTHONPATH. The local
working report records the original logs, backups, and exact maintenance commit.

If the item is assigned again, inspect its current return and main-branch source
first. Start with the retained validated sandbox; keep the direct source import.
If it is still proved and has no current return, repair the stale assignment
instead of inventing a new proof. If a new substantive return exists, repair that
specific diagnostic and use the ordinary author/independent-reader delivery flow.
