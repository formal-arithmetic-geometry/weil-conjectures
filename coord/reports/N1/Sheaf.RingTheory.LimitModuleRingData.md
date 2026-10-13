## What changed

Added `LimitModuleRingDataCore` and reduced `RingHom.exists_limit_module_ring_data` to its core finite-coefficient descent assertion. The target theorem is proved by choosing the cocone component as `κ` and discharging its pointwise equality by reflexivity.

## Proved and sorry left

`RingHom.exists_limit_module_ring_data` is proved. The new declaration `RingHom.exists_limit_module_ring_data_core` remains `sorry` as the strictly smaller finite-coefficient descent assertion (node `lem-weil-pbc-limit-module-ring-data-core`).

## No longer needed

None; the original proof dependencies were already absent from the module imports.

## Where the brief, the DAG or earlier work was wrong

The DAG's single-step proof plan is too large to execute directly in this worker window; it was split into the core descent assertion, which is strictly weaker and supplies all nontrivial construction content.

## New nodes

`lem-weil-pbc-limit-module-ring-data-core` in `dag/nodes/sec-proper-base-change/lem-weil-pbc-limit-module-ring-data-core.json`.

## Earlier second reading (a previous round; superseded)

A second worker should compile the two sandbox modules and check that the core statement is strictly weaker than the target and that the target proof only instantiates the omitted cocone representatives.

## Second reading by N1

1. Compared the delivered module with the repository version. The existing theorem signature is byte-for-byte unchanged; only a proof-only import and proof body were added. The new core theorem is a separate declaration with a weaker conclusion.

2. Compiled both modules with `lcompile.py --all`; they compile cleanly. The target has no direct `sorry`; the only remaining hole is the named core theorem, documented and represented by node `lem-weil-pbc-limit-module-ring-data-core`.

3. Checked the core statement against the target: it omits only the explicit κ representatives and their pointwise equality, which are supplied by setting κ to the underlying β maps. It is therefore strictly weaker and exactly sufficient. No duplicate library theorem was found.

4. Checked the proof route and imports. The target proof applies the core node and uses reflexivity for κ; the unit route is retained. The target node now records the core node as its proof dependency. No imports can be removed without changing the statement or proof environment.

5. Checked DAG agreement: the target node proof and `proof_deps` match the Lean proof, and the new core node carries its source, statement, proof plan, Lean declaration, chapter, and unit metadata.

Changed the report and target node metadata only; no Lean statement or definition was changed.
