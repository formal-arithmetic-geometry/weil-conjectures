## What changed
Added a proof-only helper module stating the objectwise comparison and restriction compatibility, then assembled it with `NatIso.ofComponents` to prove the target theorem.

## Proved and sorry left
The target `CategoryTheory.Sheaf.injectiveResolution_cohomologyPresheaf` is reduced to the strictly simpler intermediate theorem. The intermediate theorem `CategoryTheory.Sheaf.injectiveResolution_cohomologyPresheaf_data` remains `sorry` and has node `lem-sc-injective-resolution-cohomology-presheaf-data`.

## No longer needed
No imports or stated dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong
The DAG gave no explicit node for the objectwise comparison and naturality glue, so it was split into the new intermediate theorem.

## New nodes
`lem-sc-injective-resolution-cohomology-presheaf-data` in `dag/nodes/sec-picard-framework/lem-sc-injective-resolution-cohomology-presheaf-data.json`.

## Second reading by J1

1. The delivered target theorem has the same signature as the repository version; only its proof changed, and the helper theorem is a separate strictly stronger objectwise formulation.
2. The target proof compiles and introduces no axioms or definitions; the helper is the sole explicitly named remaining `sorry`, with a matching node and proof source.
3. The helper statement is true and exactly the objectwise comparison plus restriction compatibility required by `NatIso.ofComponents`; its three Mathlib searches found no existing theorem.
4. The proof uses the unit route's injective-resolution comparison and does not bypass the unit; no imports or dependencies were pruned.
5. The DAG node, Lean signatures, proof dependency record, and report agree after adding the exact helper signature and search records.

Changed during second reading: corrected the helper node metadata (`stmt_deps`, exact Lean signature, and three search records) and documented this review.
