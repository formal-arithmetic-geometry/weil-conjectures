## What changed
Copied the existing implementation of `AlgebraicGeometry.dualityEquationBaseChangeMap` into the delivery sandbox. The declaration already contains a complete mate-based construction and no `sorry` holes; no proof edits or imports were needed.

## Proved and sorry left
`AlgebraicGeometry.dualityEquationBaseChangeMap` is complete. No `sorry` remains and no new holes were added.

## No longer needed
None. The existing imports are used by the definition and its naturality proof.

## Where the brief, the DAG or earlier work was wrong
The module is already fully proved in the current library (the DAG node is marked as having passed compiler review), so there were no remaining stage-3 holes to close.

## Second reading by E1

1. Compared the delivered module with the repository version. The declaration signature and body are unchanged; only the module and declaration documentation now state explicitly that the map is constructed directly as the mate of the inverse canonical base-change transformation, with no auxiliary adjunction data. No target statement or definition data changed.

2. Compiled the module with `lcompile.py`; it succeeds with no errors and no `sorry` in the delivered file. The declaration's transitive axioms include `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` only from still-open imported declarations.

3. The repair concern about undetermined auxiliary data is resolved: the definition takes only `adjf`, `adjf'`, `hβ`, and the canonical base-change map, and constructs the result with `mateEquiv`. No new theorem or split-off statement was added, and the existing declaration agrees with the DAG statement.

4. The imports are unchanged and are all needed by the public signature or the mate-based proof. No proof dependency or module can be pruned. The unit route remains the direct mate route recorded by `def-sc-duality-equation-base-change-map`.

5. The DAG node's Lean declaration and proof fields remain consistent with the source. No new nodes or change records are needed.

Changed in this second reading: clarified the module and declaration docstrings to describe the direct mate construction and its independence from auxiliary pullback adjunction choices.
