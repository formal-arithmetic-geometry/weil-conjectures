## What changed

The original theorem `AlgebraicGeometry.Scheme.exists_section_everywhere_nonzero_germ`
is now proved from a fully proved geometric-germ witness and one remaining local
refinement theorem. Added proof-only imports of `NonzeroGermWitness` and
`RefineNonzeroGerm`. The combination restricts the source section along the
refinement map and uses naturality of the original morphism to identify its image.
The original theorem signature and docstring are unchanged.

`exists_section_nonzero_at_some_germ` is fully proved: assuming all image-section
germs vanish, the stalk colimit universal property and naturality force every
stalk map to vanish. The library's proved
`sheafHom_ext_of_sheafFiber_map_algClosurePoint` then forces the morphism to be zero.
The marked lift supplies nonemptiness, using the closed point of Spec of the field.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.exists_section_everywhere_nonzero_germ` (the one
original sorry), and `AlgebraicGeometry.Scheme.exists_section_nonzero_at_some_germ`
(node `lem-weil-pbc-nonzero-germ-witness`).

Remaining sorry: `AlgebraicGeometry.Scheme.refine_section_nonzero_germs`, node
`lem-weil-pbc-refine-nonzero-germ`. This statement concerns restriction of one section
of the target sheaf along an actual etale morphism. It has no source sheaf or sheaf
morphism and does not repackage the nonzero-morphism hypothesis. Its complete
natural-language proof is in its docstring, following original proof steps 2--4.
All three delivered modules compile together with lcompile.py.

Edge cases: a zero section cannot satisfy the nonzero marked-germ hypothesis;
the empty scheme cannot carry the marked lift. No connectedness or finiteness of
X is assumed. The set-sheaf trivialisation need not preserve addition, because
both the section and the zero section are transported and refined separately.

## No longer needed

No original import was removed. The direct stalk-exactness dependency
`prop-weil-pbc-geometric-stalks-exact` is unnecessary for the witness proof:
existing joint faithfulness suffices. That node has no `lean` record in this checkout and no module for it is newly imported.
The constant-sheaf and sheafification dependencies remain needed by the refinement
node; they have not been pruned from that argument. No unit statement or step is bypassed. The old direct dependencies
`def-weil-pbc-constant-sheaf`, `def-weil-pbc-etale-sheaves`,
`def-weil-pbc-geometric-stalks`, `lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-sets-sheafification-geometric-stalk` are now carried by the new refinement node
rather than direct proof edges; they are not pruned transitively. Both
`prop-weil-pbc-geometric-stalks-exact` and
`lemma-weil-pbc-geometric-stalk-conservative` are eliminated as proof nodes: the
witness directly calls the upstream joint-faithfulness declaration.

## Where the brief, the DAG or earlier work was wrong

The original node used exactness and conservativity to derive joint faithfulness,
but the source library already proves joint faithfulness directly for algebraic
closure points in the coefficient universe. This eliminates that detour.
The original node's constant-colimit and set-sheafification nodes have no `lean`
record in this checkout, despite the brief's assertion that each dependency has
one. The source library has the constant-sheaf stalk formula, but there is no
existing declaration for the pointed refinement of an arbitrary locally constant
set-sheaf section; that precise residual step is split off.

Searches: msearch leanfinder returned RingedSpace local-germ lemmas and
TopCat.Presheaf.germ_exist, which concern other sites. Loogle returned an unknown-identifier result, and grep was also
run through msearch. Leansearch was unavailable (Internal Server Error). Direct rg searches of both library roots found the proved
joint-faithfulness theorem used above, but no existing etale nonzero-section
refinement theorem.

## New nodes

`lem-weil-pbc-nonzero-germ-witness`: fully proved witness theorem in
`Sheaf.AlgebraicGeometry.NonzeroGermWitness`, implementing original step 1.

`lem-weil-pbc-refine-nonzero-germ`: residual refinement theorem in
`Sheaf.AlgebraicGeometry.RefineNonzeroGerm`, implementing original steps 2--4
for a single target section and an explicit restriction map.

Updated the original node's proof, proof_deps and proof_origin to match the Lean
proof. No changes to statements, definitions, unit records or target signatures.

## Second reading by B3

1. Compared the delivered item module with the repository version. The theorem
   signatures and existing declarations are unchanged; only proof imports and
   proof bodies changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The two
   proved theorems contain no `sorry`, and the sole remaining `sorry` is the
   named `refine_section_nonzero_germs` split-off theorem. No forbidden
   declarations were added. Explicit `#print axioms` checks show only
   propext, Classical.choice and Quot.sound for the witness; the refinement
   and original theorem additionally use sorryAx, as expected from the open
   refinement theorem. Verdict: pass.
3. Read both split-off statements and their docstrings and checked their edge
   cases. The witness theorem is the genuine stalkwise reduction, while the
   refinement theorem isolates the missing locally constant sheaf argument and
   has exactly the hypotheses used by the target. Searches found no existing
   declaration with either statement. The second reader independently searched
   with "locally constant sheaf distinct sections stalk neighborhood restriction"
   through leanfinder and searched the library for nonzero-germ and section
   declarations. Results concern topological functions or other sites; none
   closes this etale refinement. Verdict: pass.
4. The proof follows the shortest available route through the proved witness
   theorem and the residual refinement theorem. The original exactness node is
   pruned from the witness proof; the unit route remains represented by the
   refinement node. Verdict: pass.
5. Checked the updated DAG proof, dependencies, origin, and the two new node
   records against the Lean declarations. They agree, and the report records
   the removed dependencies and retained unit route. Repaired the witness node:
   its proof called joint faithfulness directly, not the conservativity node
   whose recorded declaration is an isomorphism criterion. Verdict: pass.

Changed during second reading: added this review record and clarified the
axiom status and pruning inventory, and removed the spurious conservativity
proof dependency from the witness node. No Lean changes were necessary.
