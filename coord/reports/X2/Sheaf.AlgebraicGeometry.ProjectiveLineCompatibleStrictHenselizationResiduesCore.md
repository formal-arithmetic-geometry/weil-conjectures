## What changed
Added `CompatibleStrictHenselizationCoreData`, a strictly simpler intermediate construction theorem. The target core theorem now obtains all existential data from it and proves the trailing `True` conjunct. The residue-square theorem remains unchanged.

## Proved and sorry left
The target core theorem is reduced to `Etale.exists_compatibleStrictHenselizationCoreData` and closes its final `True` conjunct. `Etale.compatibleStrictHenselization_residue_square` remains sorry. The new intermediate theorem `Etale.exists_compatibleStrictHenselizationCoreData` is sorry, with node `compatible-strict-henselization-core-data`.

## No longer needed
None; all original imports remain needed by the declarations.

## Where the brief, the DAG or earlier work was wrong
The DAG treated the full construction as one theorem; it was decomposed into the construction data and the trivial final conjunct.

## New nodes
`compatible-strict-henselization-core-data`: see `dag/nodes/sec-proper-base-change/compatible-strict-henselization-core-data.json`.

## Second reading by X2

1. Compared both delivered modules with the repository versions. Existing theorem signatures are unchanged; the only item-module change is its proof and a proof-only import, and the added module is the declared split theorem.
2. Compiled both modules with `lcompile.py --all`; they compile without errors. The only remaining `sorry` is the named construction theorem and the pre-existing residue-square theorem; no definitions contain `sorry`.
3. Checked the split theorem against the construction data required by the target. Its statement is strictly weaker than the target (it omits only the final `True` conjunct), and its node now contains the exact Lean signature and three search records.
4. Checked the proof route and DAG metadata. The target node now records the split theorem as its proof dependency, and the unit route remains through the target construction.
5. Checked imports and pruning. The new theorem's public imports are required by its signature; the item uses the new theorem through a plain proof-only import. No unused imports were found.

Changed the new theorem docstring and line formatting, completed its DAG signature and search metadata, and synchronized the target node's proof and dependencies.
