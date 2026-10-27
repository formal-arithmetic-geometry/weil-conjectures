# Stage-1 worker report: lem-sfb-affine-group-tensor-reconstruction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-group-tensor-reconstruction.json`: statement, split; no exact Mathlib match. The original statement and statement dependencies are unchanged. The proof now has ten steps using existing nodes.
- `citations.json`: one verbatim statement quotation for every node used by every proof step, numbered from 1.
- `searches.jsonl`: the search command's original output records; the new searches are appended to the item's pre-existing search history.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script, not a delivered project file.

New nodes: 0. New Mathlib leaves: 0. No existing node other than the item was modified. No unit realization is needed: this auxiliary lemma is not the unit's key statement.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for Tannaka, comodule, regular-representation and tensor-reconstruction terminology, and also inspected the analogous hits in `lean/Sheaf/`. No project declaration states this theorem. In particular Mathlib's Tannaka theorem is not an attachment.

## WANTED

None. The required book and the latest blueprint are available locally.

## Audit findings and route

The imported statement agrees with Milne, *Algebraic Groups* (iAG2017), Theorem 9.2, printed pp.164--165, including all three compatibility conditions, arbitrary commutative coefficient algebras and the absence of an invertibility hypothesis. I read that theorem and its proof, Lemma 9.1, Corollary 4.8, the regular representation on p.87, and Proposition 4.12 on p.88. No statement dispute was found.

The proof follows finite-dimensional exhaustion, the regular representation and multiplication, extraction of the point at the identity, and comparison with each representation. The comparison through the coaction embedding is written on its linear-functional components, and uniqueness is checked by the counit on the regular representation. This writes out the same mechanism without requiring a new node for a faithful representation or for an algebra endomorphism commuting with translation. It also avoids invoking Yoneda or a small-indexed colimit: maps are defined vector by vector, and their scalar extensions use the existing tensor universal property.

I read the chapter and unit records and the latest blueprint at `literature/blueprint/latest/`, including the six-functor unit in `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the direct-images proof (3). The inherited long auxiliary chain reaches this statement through Milne 14.31, which invokes Theorem 9.2 after checking (a)--(c). No chapter or unit route is changed. `blueprint.from.node` is already null and `tools/blueprint_refs.py ancestor` returns None; that inherited value and the detailed `from.place` and `via` are retained, rather than inventing an ancestor. Whole-blueprint searches found no version of this reconstruction theorem. Searches for general words such as reconstruction produced unrelated derived/adic statements; tensor-compatible produced exceptional-adjoint material, not a representation reconstruction statement.

## Mathlib searches

Five searches were run with the required `msearch.py` command: LeanFinder with two phrasings, Loogle for `"Tannaka"`, a grep in `RepresentationTheory`, and LeanSearch with a comodule formulation. All services answered. Their actual records are in `searches.jsonl` and the item's appended `mathlib_searches`. I retained the searches already on the imported item and did not claim them as fresh N6 executions.

I read `Mathlib/RepresentationTheory/Tannaka.lean` lines 11--23 and 225--232. `TannakaDuality.FiniteGroup.equiv` concerns finite abstract groups and monoidal natural automorphisms over an integral domain. It does not allow arbitrary affine finite-type group schemes, arbitrary coefficient algebras, or a family initially consisting of endomorphisms. The returned abstract-group representation maps, general algebra endomorphism results and bialgebra endomorphism structures do not give a one-line specialization to this theorem. Hence the item remains a split, not a Mathlib leaf.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. The finite-subrepresentation node is used in its existing affine-group form; the more general coalgebra-comodule finite-subspace theorem is not duplicated. The representation/comodule dictionary and coordinate Hopf node are reused unchanged.

## Review by N6

I checked the node files against Milne with the cited statements open, not just their titles or their proofs. There are no new-node sources to audit. The substantive inputs are the existing representation/comodule dictionary and finite-subrepresentation theorem; the coordinate Hopf identities, tensor and basis tools supply the remaining calculations. Here is the dependency check step by step.

1. The dictionary uses right scalar extensions, whereas the item uses left ones. The explicitly given tensor flip resolves that convention. The module tensor node supplies pure tensors and their universal property. The basis-extension node actually states extension of an arbitrary independent subset, so it supports the projection obtained by killing extra basis vectors. Finite-dimensionality means a finite spanning list, from which deleting dependencies constructs a basis. The coordinate Hopf node gives the actual maps and identities for the affine group. The algebra-tensor node gives exactly the multiplication used on R tensor A. The projection identity proves scalar-extension injectivity directly, including coefficient algebras with zero divisors; no flatness theorem is tacitly invoked.

2. The Hopf node supplies both coassociativity and the counit, so Delta is indeed the regular right coaction. The dictionary applies in arbitrary dimension, not just finite dimension. The finite-subrepresentation node states containment of every finite subset for an affine group over a field; it therefore applies to a finite spanning list and to the union of two such lists. The chosen subspaces and inclusions are rational and finite-dimensional as required for condition (c). This is the one step marked non-elementary, since it explicitly invokes the substantial finite-subrepresentation theorem.

3. Two choices for l(f) are compared in a single finite subrepresentation, using only inclusions and condition (c). Addition and scalar multiplication are compared in the same way with all involved vectors in one subrepresentation. The scalar-extension universal-property node states the bijection between k-linear maps A to A_R and R-linear maps R tensor A to A_R, including the pure-tensor formula. Thus L is a real construction, and its restriction identity follows on the tensor generators. There is no choice of an unspecified object from an existence theorem.

4. The finite-subrepresentation theorem supplies a finite target containing every basis product. The finite tensor spanning list shows that the source U tensor W is finite-dimensional. I checked the tensor coaction formula against the dictionary's exact statement and product preservation against the Hopf node's exact statement. They give the displayed equality of maps, after which the explicitly split tensor inclusion justifies cancellation. The criterion in the dictionary is an equivalence between equivariance and the coaction equation, not just one direction.

5. Naturality is used only for the finite representations U, W, U tensor W and Z. The tensor identification is the one actually assumed in the item. Multiplicativity on pure tensors extends by bilinearity and finite-sum generation to all of A_R. The unit map is equivariant because Delta preserves 1. Naturality for that map and the unit condition give L(1)=1, so no missing unitality assumption remains. The algebra-tensor node supplies the product on which the calculation takes place.

6. The Hopf node states that epsilon is an algebra homomorphism. The tensor-algebra universal property therefore supplies epsilon_R as an algebra map, not merely a linear map. Composing with L and A to A_R gives a k-algebra map A to R. Both the affine-spectrum node and the dictionary state the correspondence with an R-point. This is the extraction part of Milne 9.1, checked directly instead of making a new node for its two-line counit calculation.

7. Applying a linear functional to the first factor of the coassociativity equation gives Delta f_phi = (f_phi tensor 1)c_V, with the right-comodule order unchanged. The dictionary's stated intertwining criterion then gives equivariance into the regular representation. The counit equation gives epsilon f_phi = phi. These are explicit substitutions in the cited identities, so no uncited representation-embedding theorem is needed.

8. The finite-subrepresentation theorem applies to the finite list of coefficient values on a spanning set. The factorization to U is equivariant because its coaction equality can be tested after the split inclusion from Step 1. Condition (c) now applies to a map between finite representations, even though the regular representation is infinite. Scalar extension and composition are the maps from the tensor node. This justifies the actual naturality identity for L used next; it is not assumed as a general natural transformation on infinite representations.

9. The dictionary states the point-action formula used in the displayed equality. The coordinate-functional maps are inverse to the finite-basis expansion by their values on pure tensors, so equality is detected over any coefficient ring R. This is elementary finite linear algebra from the cited tensor and finite-spanning definitions. No density of rational points, no algebraic closure and no field assumption on R appear.

10. The dictionary states the action formula and equivariance for arbitrary-dimensional comodules. Agreement on every finite subrepresentation therefore determines the regular-representation operator on all tensor generators. Applying the Hopf counit gives h* = epsilon_R L = g*. The affine-spectrum statement gives equality of the points. The final invertibility assertion uses the group-homomorphism clause of the dictionary. It is a consequence, not an extra hypothesis.

Small cases checked: V=0 (empty basis and the unique zero-space operator), the trivial group (naturality from k into any finite trivial representation forces every lambda to be the identity), R=0 (all scalar-extended modules and maps are unique, and there is one algebra map A to R), and algebras with nilpotents or zero divisors. The proof uses no smoothness, reducedness, characteristic restriction, algebraic closure or commutativity of the group law. In particular nonreduced examples such as mu_p in characteristic p are handled by coaction identities and algebra-valued points rather than pointwise density.

I checked delivery-errors B--E point by point. There are no new unsplit statements, proof-containing new nodes, duplicated clauses, missing source tags for Stacks results, or new declarations to attach. Every substantive use has an existing node; `citations.json` quotes the actual statements. Every step is under 2000 characters. The finite-local gluing, multiplication and coefficient arguments are written out as elementary applications of the cited statements, not hidden new general lemmas. `proof_deps` is the union of all step uses. The only off-unit statement tools are already Mathlib leaves (basis and scalar-extension/tensor/spectrum facts), so no new off-unit tool approval is required. No SGA source is used.

## Unfinished work

None in this stage-1 split. The project theorem is not claimed to have a Lean proof; existing prerequisite nodes keep their own proof/formalization status. Remote dry-run and delivery results are recorded after they finish.

## Validation

The first remote dry run returned one self-containedness wording diagnostic in Step 5. I replaced the phrase referring to the item with an explicit reference to the canonical scalar tensor identification assumed in the statement. No mathematical statement or dependency changed.
