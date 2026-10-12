## What changed

Proved `TopCat.locallyConstantMapsPresheaf_isSheaf` using the unique-gluing characterization of sheaves. Added `Sheaf.Topology.LocallyConstantMapsGluing` with the strictly smaller gluing-existence theorem, which remains a documented `sorry` for the pointwise gluing and local-constancy argument. Added its DAG node.

## Proved and sorry left

`TopCat.locallyConstantMapsPresheaf_isSheaf` is proved. `TopCat.locallyConstantMaps_gluing_exists` remains sorry (node `lem-weil-pbc-locally-constant-maps-gluing-exists`).

## No longer needed

The old proof dependency node `def-weil-pbc-sites-and-cohomology` is no longer used by the Lean proof. The proof uses `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing` and the new gluing module.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof omitted the substantial construction of the glued locally constant map; this was split into a strictly smaller existence theorem.

## New nodes

`lem-weil-pbc-locally-constant-maps-gluing-exists` records the remaining pointwise gluing construction.

## Second reading by Q2

1. I compared both delivered modules with the repository versions. Existing declaration signatures are unchanged; the only source change is proof and proof-only imports, while the new gluing theorem is a separately documented split statement.
2. Both modules compile with `lcompile.py --all`; no forbidden declarations occur. The sheaf theorem has `sorryAx` only because it imports the explicitly split gluing theorem, and the split theorem is the sole remaining sorry.
3. The split theorem is a strictly smaller existence claim than the item, is mathematically true by pointwise gluing and local constancy, has a complete docstring proof sketch, and has node `lem-weil-pbc-locally-constant-maps-gluing-exists`.
4. The proof follows the shortest available route through Mathlib's unique-gluing characterization and the split gluing theorem. Imports remain necessary, and no old proof dependency was removed.
5. The item's node now records the actual proof route and includes the gluing node in `proof_deps`; the unit route and realized item are unchanged.

Changed the item's DAG proof metadata to match the Lean proof and added the second-reading record; no Lean proof repair was needed.
