## What changed
Split the target proof into Noetherianity and geometric-regularity component theorems, then combined them in `formalFiber_isGeometricallyRegular`.

## Proved and sorry left
The target theorem `Polynomial.formalFiber_isGeometricallyRegular` is proved by conjunction. The component theorems `Polynomial.formalFiber_isNoetherian` and `Polynomial.formalFiber_isGeometricallyRegular_component` remain `sorry` and are new nodes.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The seven-step proof is too large for this worker window; decomposition into its two logically independent conclusions gives strictly smaller follow-up items.

## New nodes
`lem-weil-pbc-another-helper-g-ring-noetherian-component` and `lem-weil-pbc-another-helper-g-ring-geometric-component`.

## Second reading by P3
1. Compared the delivered target module with the repository version: its theorem statement is unchanged; only proof imports and the conjunction proof were added.
2. Compiled all three modules with lcompile.py; compilation succeeds and the only remaining sorries are the two explicitly split component theorems.
3. Checked the component statements against the target conjunction: both are strict projections retaining every hypothesis and conclusion.
4. Checked imports and DAG metadata; new component modules are proof-only imports, and node filenames, signatures, proof steps, and dependencies agree.
5. The unit route is retained: the target combines the Noetherian and geometric components corresponding to the planned proof.

Changed the component docstrings to include blueprint identifiers and proof sketches, corrected node filenames and metadata, and added this second-reading record. No target statement or existing declaration was changed.
