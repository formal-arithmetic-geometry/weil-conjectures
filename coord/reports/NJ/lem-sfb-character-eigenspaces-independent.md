# Stage-1 delivery: lem-sfb-character-eigenspaces-independent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-character-eigenspaces-independent.json: statement, split, no exact Mathlib match; six proof steps using existing nodes. No new nodes and no new Mathlib leaves.
- citations.json: verbatim statements for every proof-step citation.
- report.md: this report. searches.jsonl records this worker's actual msearch calls; the item's inherited searches are retained. write_split.py is a sandbox-only preparation script, not a delivery file.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag/id, character eigenspaces, weight spaces and group-like independence found no project declaration stating the item. The Lie-module declarations found have different hypotheses and conclusions. There was no prior sandbox item or report to continue, and no stage-1 repair note.

## WANTED

None: the mathematical source is present as literature/milne-algebraic-groups_iAG2017.pdf. The reused dimension and extension facts are existing Mathlib leaves whose source declarations were read.

## Statement and import audit

STATEMENT-DISPUTED (notation at dimension zero, repaired): the imported statement allows V=0, but def-sc-general-linear-group defines GL_c only for c>=1. V=0 has no basis indexed by such a c, so that citation alone did not define GL(V) in this case. The statement now explicitly sets GL(0) to the trivial group scheme, with Aut_A(0)={1}. This fills the notation gap faithfully to Milne's arbitrary-vector-space formulation; it adds no hypothesis and changes no conclusion. Tensor products and finite-dimensionality now cite their existing definitions. Algebraic closedness and finite type are retained even though this argument needs neither.

The item was a statement-only node with no proof. Its source reference was appropriate, and the universal all-algebras definition is essential: replacing it by eigenvectors for G(k) would be wrong for nonreduced groups. For example over an algebraically closed field of characteristic p, mu_p has just the identity k-point but distinct characters 1 and t in k[t]/(t^p-1). On the direct sum of its trivial and tautological one-dimensional representations, the all-algebras eigenspaces are the two coordinate lines; k-point tests alone would make both the entire space.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor returns None for the item and its parent. I retained that value and its existing via chain, and made split_report identify the latest blueprint file and its paragraph (3). Whole-blueprint searches for character eigenspaces, eigenspace, group-like and coaction found no equivalent blueprint assertion; the broader character search and direct reading of the current direct-image proof do not reveal this statement. same_as remains []. No chapter or unit record is changed: this item is a supporting lemma, not the unit's key theorem.

## Not duplicates

No new nodes. In particular the group-like independence fact is already lem-sfb-coalgebra-group-like-independent, the extension of linear maps is lem-sfb-linear-map-extension-prescribed-value, and the dimension bound is lem-weil-independent-family-card-le-dimension. I read those statements and reused them rather than creating specialized nodes. The existing monoid-character independence theorem concerns field-valued functions on an abstract monoid; it does not cover the mu_p example above by taking k-points. The existing G_m weight-basis theorem is only a special case and does not replace this item.

## Review by NJ

I read Milne Chapter 4(g), printed pp.92-94 (PDF pp.104-106), including the character/group-like correspondence, Proposition 4.22, Proposition 4.23, Corollary 4.24 and the full proof of Theorem 4.25. Its proof applies the coaction and then all linear forms to a finite relation. The present proof evaluates the given representation at the universal C-point instead: this produces exactly the tensor relation needed without importing a representation/comodule equivalence. No external source or SGA route is used.

Step 1 uses the statement of lem-sfb-affine-group-coordinate-hopf for the actual coalgebra on C=k[G]. It assumes only a field and an affine group scheme, both supplied by the item; it requires no reducedness. The statement of def-weil-affine-spectrum explicitly says every affine scheme morphism is induced by exactly one ring homomorphism. The GL_1 formulas in def-sc-general-linear-group give Delta(t)=t tensor t and epsilon(t)=1. Consequently pulling t back through a group homomorphism produces a group-like element, and two equal such pullbacks determine the same character because t and t^{-1} generate its coordinate algebra. These are explicit coordinate computations, not uses of an unstated character-comodule lemma.

Step 2 uses the same affine-spectrum correspondence to get the universal point from id_C. The GL definition identifies r_C(u) as an invertible C-linear operator. The tensor definition supplies v -> 1 tensor v, so the resulting rho is k-linear. The item's eigenspace definition, with precisely A=C and g=u, supplies the displayed eigenvector identity. I removed an unnecessary choice of a basis from an earlier draft; no basis-existence lemma is hidden here. This is an elementary evaluation step, and all its cited statements say what is needed.

Step 3 uses the tensor-product universal property in def-weil-pbc-module-tensor-product on the bilinear map (c,v) -> f(v)c. The statement of lem-sfb-coalgebra-group-like-independent gives exactly vanishing of every scalar coefficient in a finite relation of distinct group-like elements. C has the coassociative counital coalgebra of step 1; the distinctness was established there. No domain assumption on C is needed: the base k is a field. I read Mathlib/RingTheory/Coalgebra/GroupLike.lean:98-103 and confirmed that the domain condition is on the scalar ring and that torsion-freeness holds for every k-vector space.

Step 4 uses the full extension conclusion of lem-sfb-linear-map-extension-prescribed-value, not merely a statement about a proper subspace. Set P=0, U=k, the initial map zero and prescribed value 1. The hypothesis v not in P is exactly the assumed nonzero vector. The node's statement gives f(v)=1, contradicting step 3. I also read LinearMap.exists_extend_of_notMem at Mathlib/LinearAlgebra/Basis/VectorSpace.lean:294-301.

Step 5 uses lem-weil-independent-family-card-le-dimension for a finite choice of nonzero vectors. The required linear independence is proved in the step itself from step 4; the vectors belong to V, which is finite-dimensional as assumed. The dimension notion is explicitly cited. Mathlib/LinearAlgebra/Dimension/Finite.lean:161 states the corresponding cardinal bound. The passage from finite-set cardinal bound to finiteness is written out by selecting d+1 distinct members if infinitely many existed; no infinite choice of vectors is needed.

Step 6 writes the sum map, its image and its kernel explicitly. The subspace property follows from the linear equations in the item's definition. Injectivity is exactly step 4. Thus the internal direct sum is a consequence of the proved finite-relation property, with no additional theorem hidden in the word "direct".

I checked delivery-errors B-E against each field and step: every object is introduced, every non-elementary input is an existing cited statement, the source places are actual pages read, and all uses have verbatim citation quotes. No new statement is a relabelled clause or a duplicate because there are no new nodes. The elementary steps are evaluation and the explicit sum-map argument; the other four steps are marked non-elementary and cite their inputs. All step texts are shorter than 2000 characters. Every proof_deps entry occurs in uses and conversely. No proof uses its parent, so no return edge is introduced. The cross-unit inputs are existing Mathlib leaves or definitions, which are generic tools under the contract.

Small-case checks included V=0, t=0, the trivial group, repeated eigenvalues within a single eigenspace, and nonreduced mu_p in characteristic p. For the trivial group there is only the trivial character and its eigenspace is V; the claim asserts an internal sum of one space, not a decomposition of an arbitrary representation into characters. For a general noncommutative group the sum may be proper in V, as allowed by the statement. Neither commutativity, smoothness nor connectedness is used. No further statement dispute was found.

The logged Mathlib searches were run using the prescribed command, with a second natural-language phrasing. Results for Lie-module weights, one operator, abstract finite groups and isotypic components do not state this group-scheme theorem. The Loogle finite-support result assumes independence and is not an exact match for the item. No new Mathlib-search record claims that an unavailable service ran; all five current calls succeeded.

## Unfinished work

None in the mathematical split. Delivery is subject to the required server dry run and push recorded below.
