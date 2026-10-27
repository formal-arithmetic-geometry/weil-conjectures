# Recovery provenance

The dispatcher released the NR item at 2026-10-26 15:45:01 +08 and deleted its
sandbox during maintenance. This archive is outside dispatcher sandbox cleanup.

The Lean file was recovered unchanged from the server compiler's temporary input
/dev/shm/nt-tmp/nt-supplied-na1qszj6/lean/Sheaf/AlgebraicGeometry/NoetherianSupportedProductCalculus.lean.
Its compile-attachment digest is exactly se0e938023f383fdf4d9372c8, matching the
original saved packet submitted by deliver2.py. It contains 55,444 bytes / 855 lines.

The DAG node was reconstructed from the unchanged live base node and the exact
lean-record / four stmt_deps additions logged in the original worker run
lem-per-noetherian-supported-product-calculus.1792996438/log.txt:14633-14640.
The JSON .bak is the live base before adding those recorded delivery fields.
The statement signature was read from the recovered Lean file, as the worker did.

report.md is the earlier complete report printed by worker run 1792998704; it is
historical and does not include later retry-only appendices. Read the maintenance
REPORT.md for current server/queue state. This is a recovered, unvalidated packet;
no item statement or proof mathematics was changed or completed by maintenance.

Once an authorized worker holds this item again, copy this archive into that
worker's normal item sandbox, compare its node with current main, and run the
normal no-push delivery check. Do not infer completion from the old release message:
the live node had no lean record when this recovery was made.
