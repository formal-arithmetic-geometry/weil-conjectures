## What changed

Added two auxiliary theorem modules splitting the construction into stabilized kernel-image data and the quotient coherent formal-module system. The target theorem now combines these two auxiliary results by destructuring their existential data. The auxiliary proofs remain named `sorry` theorems with their own DAG nodes.

## Proved and sorry left

`AlgebraicGeometry.coherentFormalModule_kernel_construction` is proved by a real composition of the two auxiliary statements. Sorries remain in `AlgebraicGeometry.coherentFormalModule_kernel_stabilized_aux` (node `lem-weil-pbc-formal-kernel-stabilized-aux`) and `AlgebraicGeometry.coherentFormalModule_kernel_quotient_aux` (node `lem-weil-pbc-formal-kernel-quotient-aux`).

## No longer needed

None. The original proof imports are retained because they are the stated dependencies of the two auxiliary arguments.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the affine stabilization and quotient-system construction into one unproved theorem. This delivery decomposes those strictly separate steps so each can be proved independently.

## Earlier second reading (a previous round; superseded)

Pending independent second reading.

## Second reading by J3

1. **Statements and interfaces.** Compared the construction module byte for byte with the
repository version; the target theorem signature is unchanged. The two auxiliary statements
are new and strictly decompose the construction. Verdict: pass.
2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`.
The target is a real composition of the two auxiliaries; the only remaining `sorry`s are the
two named auxiliary theorems, with no definitions containing `sorry`, and no forbidden
declarations. Verdict: pass.
3. **Split statements.** Checked both auxiliary nodes against their declarations and source.
The quotient auxiliary now explicitly assumes the stabilized-image equality; this is required
for the quotient construction and eventual kernel assertion and avoids an overstrong standalone
claim. Verdict: pass after repair.
4. **Pruning and route.** The affine, Artin--Rees, coherence, and quasi-coherence imports are
still used by the stated auxiliary proof routes; no unused public import was introduced. The
unit `sk-thm-p1` route remains represented by the original target node and both split nodes.
Verdict: pass.
5. **DAG agreement.** Updated the quotient node's statement and proof text to include the
stabilization hypothesis and checked the stabilized node unchanged. Proof dependencies and
origins match the delivered declarations. Verdict: pass.

Changed the quotient auxiliary hypothesis and target application accordingly, updated its
docstring and DAG node, and added this second-reading record.

## New nodes

`lem-weil-pbc-formal-kernel-stabilized-aux`: auxiliary theorem for the stabilized kernel-image data.

`lem-weil-pbc-formal-kernel-quotient-aux`: auxiliary theorem for the quotient coherent formal-module system and eventual kernel vanishing.
