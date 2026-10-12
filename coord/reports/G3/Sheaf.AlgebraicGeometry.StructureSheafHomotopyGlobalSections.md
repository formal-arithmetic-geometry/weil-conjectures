## What changed

Proved `AlgebraicGeometry.structureSheaf_homotopy_globalSections` in
`Sheaf.AlgebraicGeometry.StructureSheafHomotopyGlobalSections` without changing its signature.
Three fully proved private helpers establish the underived unit/global-sections Hom bijection,
transport this bijection across a source isomorphism, and lift chain maps and homotopies
componentwise before passing to the homotopy quotient. The final additive equivalence is the
map of the global-sections functor followed by the inverse of the single-complex comparison
isomorphism. Naturality follows from preservation of composition and associativity.

Updated the existing node's proof and proof origin to describe the actual Lean argument.
Its proof dependencies stay the same. No new modules, public interfaces, or imports were added.
The unit record has no realized statement or steps here; the existing unit route is preserved.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.structureSheaf_homotopy_globalSections`
(node `lem-pc-structure-sheaf-homotopy-global-sections`).

All three private helpers are proved. No `sorry` remains in the item's module, and no holes
were added elsewhere. This is a proof, not a decomposition. No unproved theorem is used to
choose data. Inverses of the Hom bijections are determined uniquely by their bijectivity.

Local single-file compilation passed without warnings in approximately four seconds.
The delivery dry run performs the required axiom probe and static validation.

## No longer needed

None. All three existing imports remain needed for the statement and the proof:
`Sheaf.Topology.RingedSpaceModuleCohomology`,
`Mathlib.Algebra.Homology.HomotopyCategory`, and `Mathlib.Algebra.Homology.Single`.
Both existing dependency nodes remain used:
`def-sc-ringed-space-module-cohomology` and `def-pc-cochain-complex-modules`.
No additional modules or nodes of the planned proof are required.

The proof uses neither a derived-category localization nor injective resolutions, cohomology
comparisons, boundedness, or quasi-coherence. These were not dependencies of this item's node.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The two elementary steps of the node expand to
componentwise Hom bijectivity and homotopy lifting; Mathlib supplies quotient representatives,
quotient equality versus homotopy, and the single-complex comparison isomorphism.

The recorded searches found `SheafOfModules.unitHomEquiv` and the Hom-complex cohomology
comparison as ingredients, but no theorem directly giving this sheaf/module homotopy comparison.
A direct componentwise argument avoids building a separate Hom-complex cohomology comparison.

The edge cases require no exclusions: nonzero degrees of the source are zero, the underived
bijection only uses restriction and linearity, and the argument works over the zero ring and
on empty spaces, with no boundedness condition on the target complex.

## Second reading by G3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the theorem proof and private helpers differ. Verdict: pass.
2. Compiled the module with `lcompile.py` and inspected the declarations and imports. There are no errors, warnings, `sorry`, axioms, unsafe declarations, or hollow definitions. The proof uses only the permitted foundational axioms. Verdict: pass.
3. Checked the proof route and the existing node. The underived unit Hom bijection, componentwise chain-map and homotopy lifting, quotient descent, and naturality establish exactly the node statement. No split-off statements or new nodes were introduced, and no duplicate library result was used. Verdict: pass.
4. Checked pruning and dependencies. All three imports and both recorded proof dependencies are used; no import or node can be removed. The proof takes the recorded unit route through the single-complex comparison. Verdict: pass.
5. Checked the DAG and unit metadata. The node proof and proof_origin describe the implemented route, and the unit route remains intact; no statement or definition was changed. Verdict: pass.

Changed only the proof of `AlgebraicGeometry.structureSheaf_homotopy_globalSections` and its private helper proofs, and added this second-reading record.
