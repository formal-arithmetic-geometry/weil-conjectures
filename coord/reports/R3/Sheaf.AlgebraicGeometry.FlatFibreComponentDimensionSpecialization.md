## What changed
Added the intermediate theorem exists_fibre_dimension_open_of_flat_restrict and proved the target theorem from it using openness of specialization. The target module compiles.

## Proved and sorry left
The target fibre_dimension_eq_of_specializes_component_restrict is proved. One strictly simpler intermediate theorem remains sorry: exists_fibre_dimension_open_of_flat_restrict (node lem-sbc-flat-fibre-component-dimension-specialization-open).

## No longer needed
No imports were removed; the original imports are all retained for the statement and planned proof.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan omits the explicit local-constancy neighbourhood statement needed to make the final specialization step concrete; this delivery adds that intermediate node.

## New nodes
lem-sbc-flat-fibre-component-dimension-specialization-open: local constancy neighbourhood at a generic fibre component point, stated in the existing target module.

## Second reading by R3
1. Compared the delivered module with the repository version. The existing target
   declaration is byte-for-byte unchanged; only its proof was replaced, and the
   split-off theorem was added as declared in the report.
2. Compiled the module with `lcompile.py` and ran the delivery preflight. There
   are no errors, forbidden declarations, or unlisted `sorry`s. The remaining
   `sorry` is exactly `exists_fibre_dimension_open_of_flat_restrict`, whose
   source and node are recorded above; the target proof itself is complete.
3. Checked the target proof against the stated hypotheses: the open-neighbourhood
   theorem supplies `V` and its constant-dimension equality, while
   `hsp.mem_open V.isOpen hxV` places the generalization in `V`. Thus the target
   statement is proved without changing its strength. The intermediate statement
   is the strictly simpler local-constancy reduction required by the proof.
4. Searched the imported library and Mathlib APIs during review. No existing
   declaration gives this fibre-dimension neighbourhood theorem, so the split
   is necessary; no shorter available theorem closes it. The imports are retained
   because they support the public statement and its proof.
5. The DAG node, Lean declaration, and proof route agree. The unit route is kept:
   the target still proceeds through the component-point local constancy step.

Changed in this second reading: no code or statements; only this review record
was added. The target hole was closed, and one strictly simpler hole remains.
