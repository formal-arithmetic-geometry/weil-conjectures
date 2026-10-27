## Worker report

Q126 split `lem-trf-split-tensor-quotient-decomposition` for stage 1. The statement is unchanged. The six steps prove the scalar-extended basis, identify the generated ideal with its B-linear span, separate the projected generators using the two product idempotents, construct inverse tensor/quotient maps, construct inverse product/quotient maps, and exhibit finite generating lists. No Lean was written or compiled.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-split-tensor-quotient-decomposition.json`: item, status split, complete proof and recorded searches.
- `citations.json`: eight step/dependency entries, with verbatim statement quotations.
- `report.md`: this report. The search command also maintains `searches.jsonl`.

## New nodes

None. The algebra arguments are short calculations from the existing statements and definitions; promoting the product-ideal equality or the quotient isomorphism into new nodes would merely repeat clauses of this item. There are zero new Mathlib leaves. The existing base-change basis leaf is reused.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for split tensor algebras and tensor quotients. No declaration states all the item's clauses. The applications in `AlgebraicGeometry/AffineEtaleClosedImmersionLift.lean` and `AlgebraicGeometry/ClosedImmersionAlgebraSectionsExact.lean` use tensor/quotient infrastructure, rather than proving this item. Sorry-containing declarations would not qualify in any event.

## Sources and searches

I read `literature/stacks-project/flat.tex`, Tag 0812, label `lemma-trick-fitting-ideal`, statement and proof (lines 8848 onward). The proof passes from the product splitting of the algebra to the quotient-module splitting; this item makes precisely that passage explicit. The finite-free hypothesis here is already the local free setting used by the parent; no hypothesis is added. I also read `algebra.tex`, Tag 00CX, label `lemma-tensor-product`, including its proof by generators and relations, and Tag 05G3, label `definition-base-change`. The cited existing basis node explicitly covers the right-factor form needed here. Its recorded Mathlib declarations are `Module.Basis.baseChange` and `baseChange_apply`.

The latest blueprint was read at `literature/blueprint/latest/blueprint/sec-trace-formula/`: the chapter, `sk-i-curve-zero/_section.md`, and the locality statement and proof. This auxiliary algebra step remains below the existing Stacks 0813/0812 branch recorded by the item's `blueprint.from`; it does not replace a unit-level step. `tools/blueprint_refs.py ancestor` identifies `lem-trf-local-term-locality`. Whole-blueprint searches for `tensor quotient` and `quotient decomposition` found no equivalent blueprint node. Whole-DAG searches included Tag 0812, free-module base change, tensor product universal properties, tensor quotients, product ideals and quotient products. I opened the selected dependencies and the sibling `lem-trf-split-tensor-quotient-finite-fitting`; the latter concerns finite relations and Fitting generators and is neither needed nor a source of a cycle.

I ran the prescribed msearch command with LeanFinder, Loogle, grep and LeanSearch, including a second semantic phrasing. All new requests succeeded and their actual results are recorded from `searches.jsonl`; historical searches were retained unchanged. `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` (read in `Mathlib/RingTheory/TensorProduct/Quotient.lean`, lines 35–68) concerns tensoring over the ring being quotiented, not the complete product splitting of this item. `Ideal.quotientEquivDirectSum` (read in `Mathlib/LinearAlgebra/FreeModule/IdealQuotient.lean`, lines 28–58) assumes domains and a PID and concerns Smith coefficients. Neither is an attachment or a one-line specialization proving this entire item. Other hits concern quotient algebra structures or finite type as an algebra, rather than finite generation as a module. The proof instead uses the existing universal properties and elementary formulas.

## Not duplicates

No new nodes were created. The existing `lem-weil-pbc-free-module-base-change-free` supplies the needed basis theorem exactly. The existing tensor-product, quotient-algebra and finite-module nodes supply their own notions and universal properties.

## WANTED

None.

## Problems and corrections

No statement dispute or source error affects this item. The imported node had no proof; the missing arguments are now written. I preserved the statement and all historical metadata and searches. In particular I did not infer that the B-linear span of arbitrary algebra generators is an ideal: Step 2 proves this specifically using that K is an ideal of C. No unsupported use of flatness, finite generation of K, or finite presentation occurs.

## Unfinished work

None for this stage-1 split. New statement-only nodes are unnecessary. Independent maintainer review and the later Lean stages remain the project's separate work.

## Review by Q126

I checked the six steps against the source and reopened every cited node's statement, rather than relying on its title or proof. Step 1 cites `lem-weil-pbc-free-module-base-change-free`: its statement explicitly gives `(e_i tensor 1)` as the basis in the right-factor tensor convention, over arbitrary commutative rings. It therefore applies with R=A, scalar algebra B and F=C, without flatness or a nonzero rank assumption.

Step 2 cites `def-weil-pbc-module-tensor-product` for pure tensors generating and `lem-weil-pbc-algebra-tensor-pushout-universal-property` for the multiplication formula. Both clauses are literally in those statements. Multiplication of a generator by a pure tensor is `b (ck tensor 1)`; `ck` belongs to K by the actual ideal hypothesis. Distributing finite sums proves ideal closure, so the two span inclusions follow from the definitions. This is an elementary calculation, not an uncited exactness theorem.

Step 3 uses no external lemma. I checked its two ideal inclusions directly: arbitrary finite ideal sums map through a surjective isomorphism, the product ideal contains the images of the generators, and multiplication by `(1,0)` and `(0,1)` separates them. Multiplication by `(b,0)` and `(0,d)` then yields exactly the finite sums defining KB and H. It uses the given first-projection identity with b=1. It never assumes that the B-module span in D alone is an ideal.

Step 4 cites the algebra tensor universal property, the quotient algebra definition, and the module tensor definition. The first explicitly supplies homomorphisms with the required values on pure tensors; the second supplies the quotient structures; the third explicitly supplies generation by pure tensors. I verified that both maps out of the factors respect A and that changing a C/K representative changes its image by an element of J. Conversely beta kills every displayed ideal generator and hence J. Thus both quotient maps are well-defined on representatives. The composites fix pure tensors and their quotient images; this is the written argument for inverse maps, with B-linearity checked in the second tensor factor. No left exactness of tensoring is used.

Step 5 cites only the quotient algebra definition. The inverse formula is on arbitrary representatives in B and D. Its independence is exactly Step 3, because the difference pair belongs to theta(J), and applying theta inverse makes its difference lie in J. Computing the two composites verifies the isomorphism. B-linearity uses the specified B-algebra structure on theta, not merely its being a ring isomorphism. Substitution of a pure tensor gives precisely both coordinates of the statement. The two-term direct sum is represented by pairs.

Step 6 cites `def-weil-finitely-generated-module`, whose first sentence is exactly the finite-generating-list criterion being used. For D, every element has a lift of the form theta inverse(0,d); projecting its basis expansion gives the claimed list. Residue classes of that list generate D/H. B/KB is cyclic. The classes of the basis vectors generate T/J, and the already constructed inverse alpha transfers this explicit list to the tensor quotient. These checks avoid invoking an additional finite-module-image theorem without a node.

I tested K=0 (the maps reduce to the original product splitting), K=C (J=T, KB=B and H=D, so both quotient factors vanish), D=0 (only the first quotient remains), and rank d=0 (C is the zero ring and the unital map C to B forces B=0; the splitting forces D=0). Empty lists therefore cause no exception. As a nonflat test, take A=C=Z, B=Z/2, D=0 and K=(2): J=KB=0 and the tensor quotient is Z/2 as required. Zero-ring quotients are allowed throughout. Every proof step is shorter than 2000 characters, and none hides a separate standard comparison. I checked B1–B10, C1–C8, D1–D5 and E1–E7 in this concrete form: no new nodes to violate the statement-only rule, all references are to actual statements with verbatim quotes, no cycle through the parent or sibling, and all maps use the correct scalar factor and hypotheses. The correction made during this reading was to spell out quotient inverses and the generating lists rather than asserting that they transport automatically.
