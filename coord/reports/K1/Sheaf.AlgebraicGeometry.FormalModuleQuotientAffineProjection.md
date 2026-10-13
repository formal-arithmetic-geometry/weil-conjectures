## What changed
The target module combines separate surjectivity and kernel component theorems. During second
reading, the surjectivity component was proved from the existing positive-power quasi-coherence,
affine tensor-product and cokernel-image theorems, then transported through the bijective tilde
unit. Its proof imports are plain imports. The kernel component remains a named theorem with a
complete natural-language proof and matching node. All existing signatures and definitions stay
unchanged. The target's DAG proof now records the actual conjunction reduction.

## Proved and sorry left
Original module holes closed: `AlgebraicGeometry.formalModuleQuotient_affine_projection` (one of
one), by combining the two components. This theorem still depends on `sorryAx` through the
kernel component, so it is not an axiom-closed proof of the original mathematical result.

The first worker added two component holes. Second reading closed
`AlgebraicGeometry.formalModuleQuotient_affine_projection_surjective`; `#print axioms` shows only
`propext`, `Classical.choice` and `Quot.sound` for this theorem.

The delivery adds one remaining hole:
`AlgebraicGeometry.formalModuleQuotient_affine_projection_kernel`, node
`lem-weil-pbc-formal-module-quotient-affine-projection-ker`. The target module contains no `sorry`.
Thus the original one hole becomes one strictly simpler kernel hole: a decomposition with net
zero holes closed in the import closure, not a net proof gain. There is no holed definition.

## No longer needed
Removed the target's direct proof import
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`. This module remains
needed by the component proofs; no module is globally pruned.

The target's old direct `proof_deps` are replaced by its two component nodes:
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`,
`def-weil-pbc-coherent-formal-module`, and
`lem-weil-pbc-quasi-coherent-module-cokernel-image`.
The theorem ingredients remain recorded in the component nodes; the coherent formal module
continues to define the objects in all three statements. None is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong
The first version described the decomposition as a proof without making its negative hole count
explicit, and left the component docstrings without a source or full proof. It also left the
original target node's proof route unchanged. Second reading repaired these issues. Surjectivity
needs no ideal range computation and could be closed directly with existing library results.
The kernel's remaining work is multiplication range computation and scalar transport, not a
mere repetition of the whole conjunction.

## New nodes
`lem-weil-pbc-formal-module-quotient-affine-projection-surj`: the surjectivity conjunct, now proved.
The node records the actual quasi-coherence, affine cokernel and tilde-unit proof route.

`lem-weil-pbc-formal-module-quotient-affine-projection-ker`: the strictly smaller kernel conjunct,
with the same original hypotheses and explicit map, source, proof and fresh search records.
No statement or definition change records are needed.

## Second reading by K1
1. Compared the delivered target module with its repository version. The existing signature is
   byte-for-byte unchanged. Only its proof and private proof imports change; no definition or
   target statement changes. The two new modules contain exactly the original two conjuncts.
2. Compiled all three modules locally. The sole remaining `sorry` is the named kernel theorem.
   No prohibited declaration or holed definition occurs. A scratch axiom audit reports precisely
   the three permitted axioms for surjectivity; the kernel and conjunction additionally use
   `sorryAx`, as declared above.
3. Read the split statements, original theorem and definitions, affine cokernel-image theorem,
   and ideal-times affine-sections theorem. Both components are true and strictly simpler than
   the conjunction. At I=0 the projection is an isomorphism and kernel zero; at I=top its target
   is zero and kernel all of M; M=0 and the zero ring cause no exceptions. Positive m excludes
   the zero-power case in the power-range theorem. Fresh LeanFinder, Loogle and Mathlib grep
   searches, plus `rg` on both library roots with range, cokernel and ideal-power terms, found
   ingredients but no exact duplicate of either component. LeanSearch was also attempted
   and recorded as unavailable (Internal Server Error). The existing private product
   quasi-coherence proof cannot be invoked across modules, so the proved private helper uses
   the same public tensor, kernel and cokernel ingredients.
4. Replaced the surjectivity sorry with the short affine-cokernel route, kept imports private
   where only proofs use them, and removed the target's redundant direct ingredient import.
   Read `dag/units/sk-thm-p1.json` and its `realized` fields: this item is below the unit level,
   is not one of its realized statement/step nodes, and changes no unit route. No global pruning
   is asserted. All old target dependencies are accounted for above.
5. Updated the target node to its actual two-component conjunction proof. Updated both new
   nodes with self-contained statements, correct ingredient dependencies and fresh searches.
   The kernel docstring now gives the full range and scalar-transport argument and its source.

Second reading changed: closed the surjectivity component hole; repaired component docstrings
and line lengths; pruned one redundant direct import; corrected the target and component DAG
proof records and the report's decomposition accounting. The kernel remains open.
