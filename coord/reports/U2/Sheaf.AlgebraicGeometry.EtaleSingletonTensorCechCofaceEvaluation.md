## What changed
Proved `singletonTensorCech_coface_evaluation` by composing two strictly lower structural statements: the raw categorical coface projection and its downstairs restriction evaluation.

## Proved and sorry left
Closed: `singletonTensorCech_coface_evaluation`. Left: `singletonTensorCech_coface_raw_projection`, `singletonTensorCech_coface_map_down`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The direct formal coproduct reduction is large; it was split into two intermediate structural statements whose composition is checked in Lean.

## New nodes
`new-etale-singleton-tensor-cech-coface-raw-projection` and `new-etale-singleton-tensor-cech-coface-map-down` are new intermediate statements in the module, each strictly below the target.

## Earlier second reading (a previous round; superseded)
Pending independent reading.

## Second reading by U2

1. **Statements unchanged.** Compared the delivered module with the repository version: the existing target theorem signature is byte-for-byte unchanged. The two added declarations are intermediate statements only; no target or existing interface was weakened.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly. The target proof uses only the two named intermediate lemmas and `congrArg`/transitivity. The two intermediate lemmas remain explicit `sorry`s with source docstrings and DAG nodes; no `sorry` occurs in a definition, and no forbidden declaration was added.
3. **New statements.** Checked both split statements for the edge case `n = 0`: they reduce to the expected projection and restriction equations. They are strictly simpler than the target and are not duplicates of declarations found by repository search.
4. **Pruning and route.** The target's declared proof dependency import remains in place, and the proof follows the unit route through the raw projection and downstairs restriction steps. No imports or proof dependencies became unnecessary.
5. **DAG agreement.** Added DAG nodes `new-etale-singleton-tensor-cech-coface-raw-projection` and `new-etale-singleton-tensor-cech-coface-map-down`, matching the two split declarations and their proof dependencies. The unit and chapter fields remain `sk-prop-h2` and `sec-curve-estimates`.

Changed the report and added the two required DAG node records; no Lean proof text or target statement needed repair.

