## What changed

Proved `AlgebraicGeometry.Scheme.exists_finiteType_ideal_module_diagram` without changing
its signature or docstring. The diagram sends each finite-type subideal to its ideal
module, and each order arrow to the source library's proved `toModulesOfLE`. Monicity
of the structure-sheaf inclusions proves the functor and cocone laws. The stage
isomorphisms are identities.

Added two fully proved modules:
`Sheaf.AlgebraicGeometry.DirectedIdealModuleColimit` constructs the colimit descent by
lifting affine sections to stages, comparing lifts at common upper stages, proving
linearity and restriction compatibility, and extending on the affine basis.
`Sheaf.AlgebraicGeometry.FiniteTypeIdealModule` lifts finite affine ideal generators,
constructs finite free epimorphisms on the over sites, and supplies local generator data.

Added proof-only imports of these two modules and
`WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf`. Updated the original node's
proof route and added nodes for the two proved generic bridges. The unit route is kept.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_finiteType_ideal_module_diagram`
(node `lem-pqf-finite-type-ideal-module-diagram`): 1 of 1 original holes closed.

Also proved, with no holes introduced:
- `AlgebraicGeometry.Scheme.IdealSheafData.nonempty_isColimit_of_directed_ideal_modules`
  (node `lem-pqf-directed-ideal-module-colimit`).
- `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_toModules`
  (node `lem-pqf-finite-type-ideal-module`).

No `sorry` remains in any delivered module. Holes added: zero. This is a proof, not a
reduction to unproved intermediate statements. All choices of generators and affine
stage lifts come from theorems proved in the delivery or in Mathlib/the source library.
The arguments include zero ideals and the empty scheme. The generic colimit bridge
requires a nonempty index family and does not assume compactness. The finite-type
bridge does not assume compactness or quasi-separatedness.

## No longer needed

None. No original import, node or planned proof dependency is removed. The existing
lattice directed-union theorem is used. Its second, cofinal-family clause is not used
here, just as in the original plan. The new imports are each used by the completed proof.
No extra cohomology or quasi-coherent presentation theory is imported for the proofs.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically sound. The source already provides the canonical ideal
module inclusions in `Curve.DivisorIdealSheaf`, so their affine gluing need not be redone.
The earlier search record missed that existing construction. Mathlib's affine basis
homomorphism extension supplies the gluing used in the colimit proof. No statements,
definitions, visibility, target declarations or unit routes were changed.

## New nodes

`lem-pqf-directed-ideal-module-colimit`: a fully proved generic directed-union colimit
criterion, in `lean/Sheaf/AlgebraicGeometry/DirectedIdealModuleColimit.lean`. Its explicit
stage identifications and inclusion equations force the transition maps; its proof
constructs the universal descent and verifies uniqueness on the affine basis.

`lem-pqf-finite-type-ideal-module`: a fully proved finite-type conversion for any scheme,
in `lean/Sheaf/AlgebraicGeometry/FiniteTypeIdealModule.lean`. Its proof constructs actual
local finite generating families. Neither new node leaves work to another worker.
No change record is needed: the existing module's exported interface is identical.

## Second reading by S2

1. **Diff and interfaces.** Compared the delivered item module with the repository version. The
existing theorem signature and docstring are unchanged; the two additional modules are new
proof bridges and no existing declaration was weakened.

2. **Compilation and axioms.** Compiled all three delivered modules with `lcompile.py --all`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or
`debug.skipKernelTC` occurrences. The proofs use only ordinary library constructions; no
hollow definition or arbitrary witness is introduced.

3. **Statements and nodes.** Checked both split-off statements against their Lean declarations,
edge cases (zero ideals and the empty scheme), source references, and DAG records. Both are
true, strictly narrower bridges needed by the item, and carry complete proof descriptions.
The original target statement is unchanged and its proof applies exactly the two bridges.

4. **Route and pruning.** The proof retains the unit route through the finite-type directed
union and colimit steps. Every added import is used, and no prior import or proof dependency
can be removed. The DAG proof and `proof_deps` fields match the declarations used.

5. **Final verdict.** The delivered code is accepted after this reading. I changed only this
report by adding the present review section; no Lean statements, definitions, or proofs were
changed.
