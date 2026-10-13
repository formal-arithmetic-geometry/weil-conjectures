## What changed

Proved `AlgebraicGeometry.affineBasisDualMatrix_component` in
`Sheaf.AlgebraicGeometry.AffineBasisDualMatrix`, preserving all existing statements,
definitions and imports. Private proved helpers establish the inclusion identities
for `tildeFinsupp` and `restrictFreeIso`, derive the projection identity by free-sheaf
extensionality, and express each sheaf component as the functor image of its scalar
algebraic component. The final scalar identity is the dual-basis evaluation calculation.
The local dual-coordinate constructions use the fixed classical equality instances
inside the original dual-coordinate definition.
The existing DAG plan and its dependency remain unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.affineBasisDualMatrix_component`
(node `lem-sc-affine-basis-dual-matrix`), the module's sole original hole.
No holes added or split off. No sorry remains in the delivered module.
All private helpers are proved, and both private coordinate isomorphisms are real
constructions from existing isomorphisms.

## No longer needed

None. No imports removed, and no nodes or modules pruned. The proof uses the existing
Mathlib sheafification construction recorded by
`lem-weil-pbc-spec-module-tilde-sections`, as planned. The three existing public
imports remain necessary for the unchanged public definitions and statement.

## Where the brief, the DAG or earlier work was wrong

None. The two steps of the existing plan suffice. Restriction additivity is supplied
locally from its natural isomorphism with pullback; no interface adaptation is needed.
The proof uses no division or nonzero hypotheses. Empty index types give no component
pairs, and the same calculation applies over the zero ring.

## Second reading by P1

1. **Visibility and unchanged statements.** Compared the delivered module with the repository version using `diff`. The existing declaration and all definitions have byte-for-byte identical signatures; only the proof body and private helpers were added. No change record is needed.

2. **Proof and axioms.** Compiled the module with `lcompile.py` successfully. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the only remaining theorem hole in this item is none. The proof uses ordinary category and module constructions and the permitted classical instances.

3. **Statements and split-offs.** No statements were split off and no new nodes were added. The proved declaration is exactly the existing node statement, and the private helper lemmas are strictly internal reductions rather than duplicate public statements. The finite and empty-index cases are covered by the same extensional calculation.

4. **Route and pruning.** The proof follows the node's two-step route: establish generator/projection identities for the sheafification and restriction comparisons, then reduce to the algebraic dual-basis coefficient identity. All stated proof dependencies remain used; no shorter available library theorem was found, and no imports or nodes can be pruned.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` agree with the delivered proof and its use of `tildeFinsupp` and `restrictFreeIso`. The unit route and `realized` records are unchanged.

Changed only this report by adding the second-reading record required by the stage-3 delivery contract.
