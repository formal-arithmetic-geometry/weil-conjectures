# Stage-1 worker report: Q77

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-free-algebra-map-coordinates.json`: statement, split; Mathlib searches find no declaration for the full coefficient-quotient representing bijection. Six proof steps reuse four existing Mathlib leaves. No new nodes or new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 14 step/node pairs.
- `searches.jsonl`: five actual searches, recorded by the required search command.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag and for Weil restriction, coefficient algebras and finite-free coefficient constructions found no declaration stating this item. The Mathlib presentation-model equivalence is not this statement.

## WANTED

None for this split. Its proof uses the locally available Stacks source, not an unavailable BLR text.

## Findings and changes

The item statement is unchanged. I read Stacks `more-morphisms.tex`, Tag 05Y6, `lemma-hom-from-finite-free-into-affine`, lines 20100–20172. Its proof constructs the polynomial coefficient algebra and leaves details of the inverse omitted. Here the coefficient ring of the presented algebra is B, and the maps preserve B: evaluating B-coefficients by b ↦ b tensor 1 is the relative version of the same construction. The proof below writes out the omitted relations test, quotient well-definedness, inverse and naturality. No finite generation, finite presentation, flatness of A, or nonzero-ring hypothesis is used.

The original blueprint ancestor was null despite its specific place and long via chain. The inherited chain ends at `lem-sfb-admissible-direct-image`, whose recorded blueprint ancestor is `det-thm-sf-ctf-stability-direct-images`. I restored that ancestor, preserved the via chain and place, and read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), together with the current unit section. This is the inherited algebra input below the open-direct-image refinement, not a replacement of a unit route. No unit or chapter record is changed. The older dag unit has a historical chapter association; the latest blueprint places this unit in sec-six-functors-basics.

I added `lem-weil-pbc-free-module-base-change-free` to statement dependencies because the unique coefficients occurring in the statement require its basis theorem. DAG searches by basis/base change/tensor concepts found this exact existing Mathlib leaf; the product-basis leaves concern two based R-modules and are unnecessary. I searched the whole blueprint with `blueprint_refs.py search` for coefficient algebra, tensor basis, base change basis and quotient algebra. There is no blueprint node stating this representing bijection. The six existing nodes carrying 05Y6 include the item, relative Hom representability and affine Weil restriction charts: none states the explicit B-algebra coefficient bijection. In particular, `lem-sfb-affine-finite-free-hom` has a related calculation in its proof only; citing that calculation as its statement would violate C3.

The required five fresh Mathlib searches are appended to the inherited search records, without changing those historical records. The first semantic search found `Algebra.Presentation.tensorModelOfHasCoeffsEquiv`; I read `Mathlib/RingTheory/Extension/Presentation/Core.lean`, lines 140–214. It identifies a scalar-extension model with an algebra already given by relations, rather than constructing a representing algebra for maps into B tensor A. The second phrasing found affine-space and submersive-presentation declarations, which do not state the item. Loogle returns the polynomial evaluation/extensionality API already present in our definition leaf. LeanSearch returns scalar restriction and tensor-algebra lifts. The two grep hits concern Witt-vector and IsAdjoinRoot coefficients. None is a full match, and no unavailable service is called a no-match.

## Not duplicates

No new nodes. Reused the existing basis base-change theorem rather than creating a finite-coordinate lemma or a clause of the item. The new proof carries the actual relations calculation.

## Review by Q77

I checked B–E with the node statements and Stacks 05Y6 open. All four cited nodes are existing Mathlib leaves. The source argument uses an arbitrary set of variables and relations and an arbitrary commutative R-algebra on the test side. The relative version keeps the B-structure fixed in every polynomial and quotient map; this is essential, since an R-algebra map alone need not respect B.

Step 1 cites `lem-weil-pbc-free-module-base-change-free`: its statement explicitly covers B tensor A, with basis e_j tensor 1, not merely freeness with an unspecified basis. I also read `Module.Basis.baseChange`, `baseChange_repr_tmul` and `baseChange_apply` in `Mathlib/LinearAlgebra/TensorProduct/Basis.lean`, lines 64–74. The polynomial definition node explicitly supplies evaluation and uniqueness over any commutative coefficient ring, so it applies over B. The tensor pushout node explicitly supplies the commutative algebra structure and inclusions. These statements give both the construction and uniqueness of c_kj.

Step 2 uses the tensor pushout node for the map b tensor z ↦ b tensor u(z). Its two input R-algebra maps have the same R-structure; its formula shows preservation of B. The polynomial node gives equality of this composite with theta_u by equality on variables. The quotient definition node identifies the quotient maps and their kernels. No unquoted basis-free compatibility theorem is being assumed.

Step 3 uses exactly the specified basis statement to turn zero tensors into zero coefficients. The generated-ideal test is proved in the text by finite sums of multiples; it is an elementary step, not a new lemma. Infinite I or K do not turn this finite sum into an infinite sum.

Step 4 cites the quotient definition for cosets and kernel H. The proof defines h_v on representatives and checks independence, operations and the B-structure directly; it does not take a quotient factorization theorem from a definition that fails to state it.

Step 5 cites the basis theorem for the unique alpha_ij, the polynomial node for the unique u and equality hq = theta_u, and the quotient node for well-defined cosets and surjectivity. It writes the two inverse checks explicitly: uniqueness of coefficients and polynomial evaluation, followed by surjectivity of p or q. This is the elementary assembly of the previous steps, not an extra representing-bijection node.

Step 6 uses the tensor pushout formula again and computes the image of each basis coefficient under s. Both constructions therefore have the same variable values. The rank-zero assertion is checked without assuming R nonzero: B = 0 forces every unital B-algebra C to be 0, while D = R; both Hom sets are singletons. Empty variables, empty relations and the zero test algebra are all allowed. For d = 1, B = R with its standard basis, the construction becomes the ordinary presentation quotient. For B = R[epsilon]/(epsilon^2), the basis (1,epsilon) makes x^2 = 0 into the two relations a_1^2 = 0 and 2a_1a_2 = 0; this confirms that the calculation uses the algebra multiplication and needs neither reducedness nor characteristic restrictions. For C = 0 and nonzero B the quotient may have no points in a particular nonzero A, which is consistent with the Hom set; no existence of maps is asserted.

All citation quotes are actual substrings of the cited node statements (whole statements were used to make the audit unambiguous). No proof step exceeds 2000 characters; the longest is 869. There are no unsplit new nodes, no hidden comparison of derived objects, and no SGA reference. The corrections made during self-review were to reuse the exact basis node, add that statement dependency, restore the broken blueprint ancestor and make the quotient constructions explicit.

## Unfinished work

None in the mathematical split. Delivery is subject to the required server dry run and push.
