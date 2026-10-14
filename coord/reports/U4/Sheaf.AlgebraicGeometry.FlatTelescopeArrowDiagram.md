## What changed
Closed `exists_flat_telescope_arrow_diagram` by a real proof that obtains structural tower data from `exists_flat_telescope_arrow_core` and applies the conditional realization theorem. Added the core module and explicit conditional realization theorem.

## Proved and sorry left
Proved: `exists_flat_telescope_arrow_diagram`.
Sorry left: `exists_flat_telescope_arrow_diagram_construction` (realization from structural tower data), `exists_flat_telescope_arrow_core` (compatible flat tower construction).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original plan bundles structural compatible flat resolutions and homotopy-category realization into one theorem. The delivery separates these into strictly staged obligations so the target proof is compositional.

## New nodes
`lem-sc-flat-telescope-arrow-diagram-core`.
`lem-sc-flat-telescope-arrow-diagram-construction`.

## Second reading by U4

1. Compared the delivered module with the repository version. The existing target signature is unchanged; the proof now uses the core structural theorem. Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`. There are no errors, forbidden declarations, or sorry terms inside definitions. The two named realization theorems remain documented split-off holes. Verdict: pass.
3. Reviewed the split statements. The construction theorem now requires the full boundedness and flatness data from the core theorem, so it is a genuine conditional realization step rather than the target under a vacuous `True` hypothesis. The new construction node records this obligation. Verdict: repaired and pass.
4. The proof follows the unit route through the core structural construction and the conditional realization theorem; the proof dependencies and imports are retained as needed. Verdict: pass.
5. Updated the DAG proof fields and added the construction node so Lean declarations and node metadata agree. Verdict: pass.

Changed the construction theorem's `hcore` argument from a vacuous existential to the full structural tower data, updated the target proof and DAG metadata, and added the construction node.
