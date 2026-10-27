# Q27 stage-1 delivery: lem-sfb-hopf-relative-kernel-shear

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-hopf-relative-kernel-shear.json`: statement unchanged; status split, seven explicit proof steps, no new nodes and no Mathlib leaves created. Existing Mathlib tensor-product and quotient-algebra nodes are reused.
- `citations.json`: an exact statement quotation for every citation in every step.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact blueprint tag, shear, Hopf/kernel, and the Hopf-algebra source directory found generic categorical shears, affine-space shears, and specialized Hopf-ideal constructions, but no project declaration supplying all clauses of this item. No compiler or build tool was run.

## WANTED

None. The cited Milne PDF is present and was read. No SGA source is used.

## Problems found

The imported item had no proof. It did not carry a Lean audit or attachment record. The statement is correct and needs no change. Milne Exercise 2-2 states a surjectivity hypothesis for its abstract-group diagram, and the book works with algebraic groups. Neither restriction is needed here: if the pair satisfies f(h)=f(phi(g)), then h phi(g)^(-1) is in the kernel regardless of surjectivity. The coordinate proof below uses only the displayed Hopf axioms, so also treats Hopf algebras not finitely generated. This is an extension justified in the proof, not an unverified appeal to the geometric exercise.

The existing blueprint ancestry has null `from.node`; the required ancestor command confirms None. Its long `from.place` and `via` identify the supporting route. I preserved that metadata and read the newest blueprint through `literature/blueprint/latest` (main-20261023-1620), including the current unit and direct-image proof (3). No chapter or unit file is changed.

## Unfinished work

None at this level. No new unsplit node is required: the only construction input beyond the stated Hopf data is the existing tensor universal-property leaf. The ideal and quotient operations are already defined by the existing quotient-algebra leaf.

## Not duplicates

No new nodes. Searching the whole DAG for Hopf, antipode, Hopf quotient, Hopf ideal, and shear, and the whole imported blueprint via `blueprint_refs.py search`, found no duplicate full statement. The existing spectrum functor node and Hopf-subalgebra faithful-flatness node have different conclusions; the latter is the parent that uses this item, so is never cited as an input. The two blueprint hits for Hopf are geometric dictionary statements, not these algebra isomorphisms.

## Review by Q27

I read Milne Exercises 2-1 and 2-2 (printed pp.61–62), Definition 3.3 (pp.65–66), Proposition 3.12 (p.67), and the two diagrams and their explanation in Theorem 3.31 (p.74). The exercises explain multiplication and division in a kernel fibre, Proposition 3.12 describes quotient Hopf structures, and the diagrams require precisely the naturality square in the item. The proof is marked agent-written because I supply the unrestricted coordinate calculations, including the details the book calls routine. I read both cited existing nodes in full: the tensor node states algebra maps out of a tensor product and their uniqueness, and the quotient node states quotient algebra structure, surjectivity and its kernel. Neither is cited for a Hopf theorem it does not state.

Step 1 uses the quotient node for the ideal-generated quotient and the tensor node for the tensor algebra maps. It proves directly, on the ideal generators, the vanishing needed to descend all three Hopf structure maps. In particular qv(c)=epsilon(c) is proved for every c, not only c in the augmentation ideal. The auxiliary epsilon S=epsilon identity follows by applying epsilon to the given antipode equation and then using the counit equation; it is not assumed from an uncited theorem.

Step 2 again uses just those two statements. It defines the three maps on representatives and checks the coassociativity, both counit identities, and both antipode identities after the surjective quotient map. There is no invocation of a general Hopf-ideal theorem hidden in this step. Step 3 uses the same inputs for the induced quotient map alpha and explicitly checks all three Hopf compatibility equations. The ideal inclusion follows on each generator from the given map i; no injectivity is used.

Step 4 invokes the tensor universal property exactly for its algebra map construction. Its required hypothesis is agreement of the two maps on C. The displayed calculation proves this agreement using the counit of C, so the map really descends over C rather than merely existing on X tensor over k B. The codomain receives the common C-algebra structure through B. Step 5 uses the quotient definition for independence of lifts and the tensor node for the two tensor-map constructions. It explicitly moves v(c_(1)) to the second factor by C-balancing and then applies the stated antipode identity. Because S is an algebra map in the item's commutative Hopf convention, T is an algebra map and killing generators suffices to kill their whole ideal. The step is not an appeal to unproved Hopf kernel theory.

Step 6 uses the tensor algebra description and ordinary additivity to check the two inverse identities on pure tensors. Coassociativity puts the factors in the displayed order, and the two different antipode identities cancel S(x_(2))x_(3) and x_(2)S(x_(3)) respectively. Thus no cocommutativity or reversal of Sweedler indices is silently used. Step 7 uses the tensor node to form a_i and b_i and proves the commuting square on a tensor a tensor b using Delta_B i=(i tensor i)Delta_A. Equality alpha(q_Aa)=q_Bi(a) was already established in step 3; it is not a new black box. All seven steps are under 900 characters each; there is no long proof step concealing a lemma. Steps 4 and 5 are marked non-elementary because they invoke the tensor universal property; the other steps are explicit substitutions, quotient descent or cancellation from the displayed axioms, not new supporting lemmas.

I checked the B–E return cases with both node files and the source open. There are no new-node schema, missing-definition, unsearched-node, duplicate, or clause-relabelling issues. No step cites the proof of another node, a tag in place of a node, or an off-route non-leaf theorem. The proof dependency list is exactly the union of uses, and every citation has a verbatim quotation. The statement and all excluded-extra-hypothesis clauses are retained. The two cited nodes are already Mathlib leaves, so no off-unit route declaration is needed.

For small cases, with C=k the quotient is X itself and the formulas are the usual shear and its antipode inverse. With v the identity on X, Q=k and the formulas reduce to the standard X tensor_X B=B identification. With v factoring through the counit, the quotient ideal is zero and the balancing check reduces to tensoring over k. The formulas also work for u:k[t] to k[s], t mapping to s^p, for the primitive Hopf structures in characteristic p, even though this is inseparable. Taking u:k[t] to k to be the counit checks a noninjective map; taking i:A to k to be its counit checks a noninjective i. No argument uses smoothness, reducedness, finite generation, a basis, or flatness. The tensor-order check in step 6 treats noncocommutative Hopf algebras without reordering comultiplication factors.

I read the inherited Mathlib search results and retained them. I then ran Q27 leanfinder with two distinct phrasings, leansearch, loogle, and two recorded Mathlib greps through msearch.py. All services answered. The hits were tensor Hopf structures, antipode equations, the generic Hopf-ideal quotient, abstract-group fibre equivalences, and scheme pullback identifications. I opened Mathlib's HopfAlgebra/Quotient.lean: it gives a Hopf structure conditional on a Hopf ideal, not the relative shear statement. The group-fibre hits do not supply algebra maps or their square. Therefore the item is not a Mathlib leaf. No search was fabricated and no unavailable service is recorded as absence.
