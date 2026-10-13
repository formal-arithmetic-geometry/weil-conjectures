## What changed

Added a real decomposition proof of `AlgebraicGeometry.exists_geometric_generic_cover_model`.
The proof obtains the model and closed-cover data from
`exists_geometric_generic_cover_model_data`, obtains the fibre and generic-intersection
properties from `refine_geometric_generic_cover_model_data`, and combines them.
The two intermediate declarations remain explicit named theorems with documented
construction sources.

## Proved and sorry left

The target theorem `exists_geometric_generic_cover_model` is proved by combining the
 two strict intermediate assertions. Sorry remains in
`exists_geometric_generic_cover_model_data` and
`refine_geometric_generic_cover_model_data`; these are nodes
`new-lem-sbc-geometric-generic-cover-model-data` and
`new-lem-sbc-geometric-generic-cover-model-refinement`.

## No longer needed

No imports were removed. The original module had no proof imports and the proof uses
only declarations in this module.

## Where the brief, the DAG or earlier work was wrong

The DAG supplied a two-step geometric construction but no formal intermediate
interfaces. The proof decomposes those two steps into strict theorem statements;
no target statement or unit route was changed.

## New nodes

`new-lem-sbc-geometric-generic-cover-model-data` and
`new-lem-sbc-geometric-generic-cover-model-refinement` are new named intermediate
statements corresponding respectively to the model/closed-cover and refinement
steps. Their node files are in `dag/nodes/sec-smooth-base-change/`.

## Second reading by V4

1. **Visible declarations and signatures.** Compared the delivered module with the
repository version. The existing theorem has the same hypotheses and conclusion byte
for byte; the only change to it is its proof. The two added declarations are the
explicit model-data and refinement interfaces described in this report.

2. **Compilation and proof status.** Compiled the module with
`python3 /home/ubuntu/weil-launcher/lcompile.py`. It compiles without errors or
warnings. There are no axioms, `unsafe`, `opaque`, or hollow definitions. The target
has no `sorry`; the two named construction interfaces intentionally retain their
documented `sorry`s and corresponding nodes. A scratch compilation with `#print
axioms` reports only the permitted axioms plus `sorryAx` inherited from those open
interfaces.

3. **Truth and strength of split statements.** The model-data assertion supplies
exactly the first five conjuncts of the target. The refinement assertion takes those
data as hypotheses and supplies exactly the geometric-fibre and generic-intersection
conjuncts. Both are strict parts of the target and preserve every original
hypothesis; neither weakens the target or adds an assumption.

4. **Shortest route and pruning.** The target proof uses only the two local
intermediate declarations and structural conjunction elimination/introduction. The
module's three public Mathlib imports are required by the signatures, and no proof
only imports are present to remove. No old proof dependency is bypassed: the unit's
model and refinement route remains represented by the two new nodes.

5. **DAG and unit route.** The target node's proof and `proof_deps` name both
intermediate nodes, and each new node records its declaration, source, and unit.
The `sk-prop-normal-form` route is unchanged. The node statements and Lean
declarations agree, and both open statements have complete construction docstrings.

**Changes made during second reading.** Added this review section only; no Lean
declarations, imports, signatures, or DAG records required repair.


## Earlier second reading (a previous round; superseded)

The decomposition is checked by compiling the module: the target's conclusion is
assembled field-for-field from the two strict intermediate conclusions, with all
hypotheses passed unchanged. The intermediate theorem statements are proper parts
of the target (model data and refinement respectively), and retain the unit route.
