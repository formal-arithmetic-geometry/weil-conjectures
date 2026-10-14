## What changed

The module now decomposes the construction into two named intermediate theorems: existence of the exact graded data and the homogeneous multiplication identity. The target theorem assembles these data into `TensorGradedPresentation`. The two intermediate theorem proofs remain explicit, documented `sorry`s; the target theorem is fully proved from them.

## Proved and sorry left

Proved `tensorGradedPresentation_exists` by constructing the record from `tensorGradedPresentation_core_exists` and `tensorGradedPresentation_core_multiply`. Sorry remains in `tensorGradedPresentation_core_exists` (node `lem-sc-square-zero-tensor-graded-presentation-core`) and `tensorGradedPresentation_core_multiply` (node `lem-sc-square-zero-tensor-graded-presentation-core-multiplication`).

## No longer needed

No imports or existing proof-dependency nodes were removed; all original imports remain available to the intermediate construction.

## Where the brief, the DAG or earlier work was wrong

The original node bundled local gluing/exactness and homogeneous multiplication into one theorem. These are separated into strictly smaller intermediate statements so the record assembly is a real Lean proof.

## New nodes

`lem-sc-square-zero-tensor-graded-presentation-core` records existence of all presentation fields except multiplication. `lem-sc-square-zero-tensor-graded-presentation-core-multiplication` records the homogeneous multiplication law for the core data. `def-sc-square-zero-tensor-graded-presentation-core` records the core structure declaration.

## Earlier second reading (a previous round; superseded)

The record assembly was compiled independently in the sandbox; the two named intermediate statements are strictly weaker than the target and preserve the unit route.

`def-sc-square-zero-tensor-graded-presentation-core` records the new core structure used by both intermediate theorems.

## Second reading by A4

1. **Diff and interfaces.** Compared the delivered module with the repository version. The
   original declarations retain byte-for-byte identical signatures; the only existing target
   change is its proof. The added core structure and two intermediate theorem interfaces are
   represented by the three accompanying DAG nodes.
2. **Compilation and axioms.** Compiled the delivered module with `lcompile.py`; it succeeds
   without errors. The two remaining `sorry`s are exactly the named split-off theorems, and no
   definition contains `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
3. **Truth and strength of split statements.** The core existence theorem supplies precisely
   the fields needed by the target except multiplication. The multiplication theorem adds only
   the homogeneous multiplication field. Both are strictly weaker than the target and their
   docstrings describe the local polynomial construction and gluing argument from Tags 09MS and
   0B8S. Searches found no existing declaration with either statement.
4. **Pruning and route.** The target proof uses both split theorems and assembles their fields
   directly; no old proof dependency or import is unused, and the unit's realized route through
   the graded presentation remains intact.
5. **DAG consistency.** The Lean declarations, node statements, proof dependencies, source
   citations, and `split` status agree. The new structure node records the definition, while the
   two theorem nodes record the remaining holes.

The second reading changed only this report section; no Lean declarations, statements, imports,
or DAG node contents were altered during review.
