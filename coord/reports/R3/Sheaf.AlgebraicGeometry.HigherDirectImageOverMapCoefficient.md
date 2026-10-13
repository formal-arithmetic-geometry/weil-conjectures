## What changed
The target theorem is reduced by a genuine two-step functorial decomposition. Two named intermediate
coherence declarations are included in the target module and used by the target proof.

## Proved and sorry left
`higherDirectImageOverMap_coefficient` is proved from the factorization and endpoint declarations.
Sorries remain in `higherDirectImageOverMap_coefficient_factorization` (mapped-composite functoriality)
and `higherDirectImageOverMap_coefficient_endpoint` (endpoint coherence), both corresponding to strict
parts of the planned argument.

## No longer needed
No imports were removed; no additional modules are needed.

## Where the brief, the DAG or earlier work was wrong
The endpoint comparison is not definitional after unfolding the canonical over-map; it must be stated
as a separate coherence result. The earlier attempt's undeclared endpoint theorem was made explicit.

## Earlier second reading (a previous round; superseded)
Pending independent review of the two split intermediate statements and the target reduction.

## New nodes
Added `sbc-lem-higher-image-over-map-coefficient-factorization` and `sbc-lem-higher-image-over-map-coefficient-endpoint` for the two intermediate steps.

## Second reading by R3
1. Compared the delivered module with the repository version. Existing declaration signatures are unchanged; only the target proof and the two newly declared intermediate theorems differ.
2. Compiled the module with `lcompile.py`; it compiles cleanly. The factorization hole is closed by `Functor.map_comp`. The endpoint theorem remains the named split hole listed above; no unnamed `sorry` was added.
3. Checked the split statements against the definitions and the target. The factorization is exactly functoriality of the homology functor and is strictly simpler. The endpoint is the remaining coherence identification and is required to connect the factorized morphism to the canonical over-map.
4. Checked the proof route and imports. The target now uses the factorization theorem followed by endpoint coherence; the unit route is retained. No import can be removed based on this repair.
5. Checked node metadata against the declarations. The two split nodes and the target node name the same statements and dependencies; the factorization proof now uses `Functor.map_comp` directly.

Changed the factorization proof from `sorry` to `rw [Functor.map_comp]`; no statement or definition was changed.
