## What changed

Proved `coherentFormalModules_coimageImage_isIso_restrict_affine` by combining separately stated monomorphism and epimorphism lemmas and applying balancedness of sheaves of modules. Added the two decomposition modules and their DAG nodes.

## Proved and sorry left

The item's original theorem is proved. The added declarations
`coherentFormalModules_coimageImage_isMono_restrict_affine` and
`coherentFormalModules_coimageImage_isEpi_restrict_affine` remain `sorry`, with nodes
`lem-weil-pbc-coherent-formal-coimage-image-affine-mono` and
`lem-weil-pbc-coherent-formal-coimage-image-affine-epi`.

## No longer needed

Removed from the item the seven original proof-dependency imports: kernel, affine equivalence, cokernel closure, ideal-times affine sections, quasi-coherent cokernel/image, completion Noetherianity, and quasi-coherent kernels. They remain below the new component nodes, so no module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan contains a long affine first-isomorphism argument but no Lean-level
component statements. It was decomposed into the strictly simpler mono and epi assertions.

The final dry run accepts the first-worker delivery and defers the second reading to
the independent reader. All three modules compile without warnings.

This is a decomposition (one hole closed, two added), not a net proof gain. The zero
arrow, empty affine open, and ideals zero and one satisfy both component assertions.

## New nodes

`lem-weil-pbc-coherent-formal-coimage-image-affine-mono` and
`lem-weil-pbc-coherent-formal-coimage-image-affine-epi` are the monomorphism and epimorphism
components of the affine comparison, respectively.

## Second reading by C3

1. **Statements and interfaces.** Compared the affine theorem declaration byte for byte with the
repository version; its hypotheses, level index, restriction functor, and conclusion are
unchanged. The two added component declarations are strictly weaker (monomorphism and
epimorphism) and have matching DAG statements and declarations.

2. **Proof and axioms.** All three delivered modules compile with `lcompile.py --all`. The affine
proof is a direct application of the two component results followed by
`isIso_of_mono_of_epi`; the only remaining `sorry`s are the two named component theorems. No
forbidden declarations or hollow definitions occur. The completed theorem consequently has
`sorryAx` only through those explicitly split statements, alongside the permitted axioms.

3. **Split statements.** Searched the library and recorded Mathlib searches in both new nodes;
there is no existing specialized affine coimage-image result. The component statements are true
first-isomorphism consequences and are each needed by the completed comparison proof. They are
not restatements of the original isomorphism target.

4. **Pruning and route.** The original affine calculation imports were removed from the top-level
module and retained below the two component modules, so the affine first-isomorphism route and
the unit route remain represented. The removed imports are listed under `No longer needed`.

5. **DAG consistency.** The top-level node now uses exactly the mono and epi nodes in its proof
and `proof_deps`; each new node records its source, statement, Lean declaration, and split
status. No unit record or target statement was changed.

I changed only the top-level proof/imports, added the mono and epi component modules and DAG
nodes, and documented this independent reading. No further repair was necessary.
