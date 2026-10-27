# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-comodule-coefficient-coalgebra.json`: item split into seven explicit steps; no exact Mathlib match.
- `citations.json`: one literal statement quotation per dependency per proof step.
- No new nodes; 0 new Mathlib leaves. The proof reuses the existing Mathlib leaf `lem-trf-vector-subspace-complement` and the existing tensor-product and finite-dimensionality definitions.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag and for comodule, subcoalgebra and coefficient-coalgebra terminology found only a general-linear-group simplicity docstring, not a declaration of this item. The project tensor zero-detection theorem is not the coefficient-coalgebra statement.

## Sources and searches

Read Milne, *Algebraic Groups* (2017), §9(d), printed pp.174–175, from `literature/milne-algebraic-groups_iAG2017.pdf`. These pages define coalgebras and comodules, display the two coefficient identities, assert that their span is a subcoalgebra, and record finite-dimensionality. The source applies to arbitrary coalgebras, with neither multiplication nor cocommutativity required.

Read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/_section.md` and `sk-thm-sf-ctf-stability/_section.md`. This is a supporting linear-algebra input deep in the inherited direct-image alteration/moduli chain; the split retains that route and changes no chapter or unit record. The current unit wording differs from the older unit JSON, but this supporting coefficient calculation changes neither formulation.

Whole-DAG searches used coalgebra, matrix coefficients, finite span, tensor injectivity, tensor bases, and subspace complements. `tools/blueprint_refs.py search` returned no imported blueprint node for coalgebra or subspace complement. The matrix-coefficients search returned sk-d-real-weil, whose statement concerns Weil sheaves and fundamental-group representations rather than the coalgebra coefficient identities; it does not state this item. `ancestor` reports the inherited `blueprint.from.node = None`; the precise inherited place and full via chain are preserved rather than inventing an ancestor id. No repair note for the item was present.

The sandbox search log records fresh LeanFinder, Loogle, LeanSearch and Mathlib grep searches, plus a second semantic phrasing and a search for Comodule. All returned successfully. Read `Coalgebra.Repr` and `Coalgebra.Repr.arbitrary` in Mathlib/RingTheory/Coalgebra/Basic.lean:48–66: they present the comultiplication of a single element as a finite tensor sum, not a comodule representation or a stability theorem. CoalgCat/Comon equivalences similarly package structures already supplied. Read FiniteDimensional.span_of_finite and span_finset in LinearAlgebra/FiniteDimensional/Defs.lean:200–209; this clause is immediate here from the cited definition, so no leaf node is needed. All inherited search records were preserved and only searches actually run were appended.

## WANTED

None.

## Corrections and limitations

The item originally had no proof. Its statement is correct and is unchanged. The tensor-subspace identification needs justification: field linear algebra supplies a projection, which yields left inverses on the tensor square and cube. The proof now states this argument and checks all coalgebra laws explicitly. No hidden finite-dimensionality assumption on C, nonempty basis assumption, algebra structure, or cocommutativity is used.

## Not duplicates

No new nodes. In particular, the finite-subcoalgebra theorem is the parent and cannot be used to prove this item without a cycle; the finite-subcomodule sibling is unnecessary. The existing generic subspace-complement node is reused.

## Review by Q39

I read Milne pp.174–175 against every clause of the item: its index order is Δ(c_ij)=Σ_a c_ia⊗c_aj for the right-coaction convention ρ(e_j)=Σ_i e_i⊗c_ij, and its counit is δ_ij. The restrictions refer to tensors over k. The statement introduces both coalgebra and comodule laws inline; its three definition dependencies supply exactly field, tensor product and finite-dimensionality.

Step 1 uses the statement of `def-weil-pbc-module-tensor-product`: its universal bilinear map and generation by pure tensors justify coordinate extraction and reconstruction. A basis supplies the linear coordinate functionals. This is an explicit calculation, not an uncited tensor-basis theorem. Step 2 uses that same universal property twice to extract the first coordinate of the two coassociativity sums; the displayed sums have the order required by the right coaction. Step 3 applies a coordinate functional to the counit equation and needs only that tensor universal property. These three steps do not use any assertion from a node's proof.

Step 4 uses the statement of `def-weil-finite-dimensional-subspace`, which defines finite dimension by a finite spanning family. I checked that I×I is finite and the coefficients span D by its definition, including the empty family; no finite-dimensional-span theorem is being invoked as a black box.

Step 5 uses the complete statement of `lem-trf-vector-subspace-complement`, which supplies a unique decomposition of every element for every subspace of an arbitrary field-vector space. I read its Mathlib match `Submodule.exists_isCompl` at LinearAlgebra/Basis/VectorSpace.lean:280–282. All hypotheses hold with P=D, V=C and the given field k. Unique decomposition proves linearity of p; tensor functoriality and generation in `def-weil-pbc-module-tensor-product` prove the two explicit left-inverse equations. Thus square and cube inclusions are injective. This is the only step using a non-elementary black box, and it cites an existing Mathlib leaf, so no new node or off-unit tool declaration is required.

Step 6 uses the tensor statement to construct (p⊗p)Δι and the coefficient calculation of step 2 to identify its composition with the tensor inclusion on each generator. Linearity then proves the restriction equation on D; injectivity from step 5 proves independence of the complement. Step 7 uses those restriction equations, the square/cube inclusions proved earlier, tensor functoriality, and the three coalgebra identities assumed on C. It explicitly identifies both coassociativity images and both counit images before cancelling injective maps. No additional stability or transport lemma is implicit. Every node cited in these steps was opened, and every quotation in citations.json is a verbatim substring of its statement.

I checked B–E: no new statement-only node is needed, no duplicate or disguised clause was introduced, every non-elementary input has a node, and no parent/sibling citation creates a cycle. All proof steps are shorter than 2000 characters. Small cases: I empty gives M=D=0 and zero structure maps; dimension one gives Δ(c)=c⊗c and ε(c)=1; zero C forces M=0 by the comodule counit. Repeated or zero coefficients cause no problem, since independence is used only for the given basis of M and never for the coefficients. The proof works in all characteristics and for an infinite-dimensional C. I corrected the draft's temporary tensor-subscript notation so every tensor is over k. Nothing mathematical remains unfinished.
