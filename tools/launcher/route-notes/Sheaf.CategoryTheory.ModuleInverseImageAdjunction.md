# Retained repair and transport diagnosis

Maintenance 2026-10-17: the original error was
`Unknown identifier AlgebraicGeometry.adjunctionOfLinearLifts` after upstream
sync e47efb5a5. The generic helper is private in
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`.
Use `import all` of that source module for proof use; the retired Sheaf wrapper
does not expose its original private name. Preserve the statement and unit route.

The complete repair was retained in this item's sandbox, passed dry runs, and
landed as `1f828626cfa78fefe8ed7e779a679addc2b18875`; a server single-file compile
passed in 10.5 seconds. Ten NOANSWER attempts were fatal Codex HTTP 429 exits,
including two after successful dry runs, rather than failed mathematical work.

First inspect the CURRENT return and main source. If this is a new return, repair
its concrete diagnostic starting from the retained work; do not restart the old
mathematics. If the item is already proved with no current return, the assignment
is stale. Keep the ordinary author dry run and independent second-reader flow.
