# Stage-1 report: lem-sfb-condensed-internal-bar-resolution

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-internal-bar-resolution.json`: existing statement, unchanged; split into ten steps. Mathlib verdict: no match for the full internal condensed statement. No new nodes and no new Mathlib leaves.
- `citations.json`: eleven entries, covering every node cited in each proof step, with verbatim statement excerpts.
- `searches.jsonl`: the actual msearch results for this item. The item's inherited searches and results were retained, and the six additional searches actually executed by NG were appended to `mathlib_searches`.
- `report.md`: this report. The two Python helpers in the sandbox only construct and refine these JSON files; they neither modify the repository nor run Lean.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the blueprint tag and internal/homogeneous/bar-resolution concepts found no completed declaration stating this item. Ordinary bar-resolution uses in `RepresentationTheory/GroupCohomology/CupNonvanishing.lean` and the continuous-cochain coordinate equivalences concern different coefficient categories, not internal modules over a variable condensed ring.

## WANTED

WANTED: an ordinary condensed-module reference for this internal augmented homogeneous bar resolution. This is the inherited source request, not a claim that the ordinary abstract-group bar theorem proves the item. The proof delivered here is explicitly agent-written and supplies the calculation. Its non-elementary sheafification, tensor and categorical inputs are existing cited nodes with sources already in the repository. No additional external document is needed as an unproved input to these ten steps.

## What changed and what was wrong

The original item had a complete statement but no proof. Its statement and four statement dependencies are unchanged; all original metadata, citations and logged searches are retained. The imported source only places this formal input underneath paragraph (3) of the direct-image argument. It does not itself prove an internal condensed bar theorem. The proof therefore remains marked `proof_origin.by = agent`, rather than attributed to a nonexistent literature theorem.

The nearest-blueprint-ancestor command reports `None` for this inherited created-node chain. The existing `blueprint.from.node = null` and its inherited `via` list were preserved. Its place was already explicit. Whole-blueprint searches for `homogeneous bar`, `free internal`, `bar resolution`, and `free module`, together with whole-DAG statement/title searches, found no blueprint node stating this full result. The broad matches are not attachments or substitutes for the item. `same_as` remains empty. The item is not the key statement of its unit, so the unit's realization record is not edited.

No dependency was dropped. Generic tool uses are declared individually in `split_report.tool_uses`. These implement the formal resolution input; they do not change the chapter or unit's geometric route. In particular no SGA source is used.

Mathlib searches were made only through the required msearch command. I read `Mathlib/RepresentationTheory/Homological/Resolution.lean` at the extra-degeneracy construction, the forgotten standard-complex contraction, and the bar-complex/resolution declarations (160–162, 249–255, 408–443), and `Mathlib/Condensed/Solid.lean` at its free-module definitions (40–46). The former is ordinary abstract-group representation theory over a fixed ordinary ring; the latter only constructs free condensed modules over an ordinary ring. The flat-tensor exactness search hits require flatness and do not supply the arbitrary-T conclusion. General short-complex splitting results do not construct this internal complex or its coordinate identification. A second natural-language phrasing and a second grep scope were run and read before the no-match verdict.

## What remains unfinished

No step of this one-level split is left as an unspecified argument. Existing cited nodes retain their own existing proof status; NG has not tried to split or alter them. There is no statement dispute, new node, Lean file or compilation in this delivery. The maintainer's independent mathematical review remains part of the normal delivery process.

## Not duplicates

No new nodes were created. In particular the sectionwise free-product/tensor calculation, double-deletion cancellation, insertion-of-identity identity, kernel factorization and inverse-coordinate formulas are written as steps, not turned into redundant lemmas. Existing module-sheafification, tensor and module-object nodes are reused. No same-Stacks-tag new/existing pair arises.

## Review by NG

I read the item, its parent derived-invariants use, its chapter and unit records, and the current `main-20261015` direct-images proof, especially paragraph (3). I also read the stated three-level restrictions and both copies of delivery-errors B–E. For the algebraic inputs I read `literature/stacks-project/sites-modules.tex`: Tag 03CY (`lemma-sheafification-presheaf-modules`), the free-module construction in the proof of `lemma-universal-module`, Tag 0GMW (`lemma-sheafification-tensor`), Section 03EK's tensor/bilinear universal property, and the internal-Hom adjunction used by Tag 03EO. For module-object kernels, cokernels and abelianness I read the three corresponding current blueprint node files. I read the sheaf-module abelian instance in Mathlib as well as its existing node's statement. There are no new-node sources to certify.

Step 1 uses the full statement of `lem-pc-sites-module-sheafification-interface`, in particular its factorization property for a module presheaf and a sheaf target. Here the ring is the sheaf A, hence A-sharp is A; all module restrictions are semilinear as required. The elementary linear-extension formula then identifies its sheafified free presheaf with the left adjoint actually specified by the item. It does not assume sections of that sheaf stay free.

Step 2 uses exactly the canonical tensor/sheafification isomorphism stated in `lem-pc-sites-module-sheafification-tensor`, for the two free module presheaves and the ring presheaf A. The displayed sectionwise maps are inverse by their tensor relations. This is where the comparison theorem is needed; neither closedness alone nor the definition of module objects would prove that comparison.

Step 3 uses `lem-pc-sites-module-sheafification-bilinear-extension` for extending sectionwise bilinear action formulas, with the second factor and target already sheaves. Its statement really gives existence and uniqueness of the required extension in both module variables. The action laws and equivariance are generator computations, and coordinate deletion is a continuous group-equivariant map. Step 4 has no non-elementary input: it pairs every ordered double deletion with the other order, including the explicitly treated augmentation case. I checked the signs with original indices rather than renumbering both deletions incorrectly.

Step 5 writes the contraction and its identities explicitly, separately treating degree zero and the augmentation. It does not mistake the insertion map for an equivariant map. In step 6, `lem-pur-ringed-site-module-category-abelian` applies because the coefficient ring is commutative and the site is small in the statement's convention. Its statement supplies the abelian category in which the kernel/image argument is made. The factorization k = d h k, not a general assertion that tensor is exact, proves the claimed image/kernel equality.

Step 7 uses the actual unit/associativity definition in `sk-def-sfb-module-objects`, plus `lem-pc-sites-module-sheafification-bilinear-extension` for the formula (sum a_g[g],m) maps to sum a_g(gm). Thus the conversion between actions and A[G]-module structures works for all local group parameters and arbitrary sheaf modules. The inverse group element gives the inverse action, and A[G] need not be commutative. This is an explicit linear extension, not a citation of the definition node for an unproved categorical exactness theorem.

Step 8 is the categorical exactness input. I checked that `lem-pc-sheaf-modules-tensor-closed` says both additive and closed. The finite-colimit preservation required for the cokernel theorem is verified by the displayed chain of adjunction/colimit universal properties. The base module category is abelian by step 6. Under precisely these hypotheses, the statements of `lem-sfb-modobj-kernels` and `lem-sfb-modobj-cokernels` give the underlying kernel and cokernel with their unique action structures, and `lem-sfb-modobj-abelian` supplies abelianness for modules over the monoid B. The step therefore proves the needed reflection of exactness; it does not borrow that fact from the proof of an inflation node or assume a nonequivariant contraction was equivariant.

Step 9 takes additivity and the tensor unit directly from `lem-pc-sheaf-modules-tensor-closed`. It applies them to the already constructed contracting identities. T is arbitrary; no flatness or projectivity is used. Since T has trivial action, the stated tensor action makes the augmentation to T equivariant, and step 8 applies. Step 10 needs no new categorical theorem: I wrote both continuous coordinate maps, checked their composites and computed the transformed action. The last identification uses the already proved free-product/tensor calculation of step 2, not an uncited projectivity theorem.

I corrected two potential omissions during this self-review before delivery: I added the explicit bilinear-extension citation for the group-algebra action, and the module-object abelianness citation when using images in that category. Every `(step,node)` pair now has a verbatim excerpt in `citations.json`; every cited node's full statement was read and its hypotheses checked as described above. Proof dependency lists equal the union of those citations. All ten steps are shorter than 2000 characters; none packages an omitted standard comparison.

For small cases I checked G trivial, where each P_n is A and the differentials alternate between zero and identity, with epsilon the identity. I checked degree n=0 in the coordinate and contracting identities, the zero ring and zero module, noncommutative G, characteristic two (paired signs still cancel), and nonflat T such as Z/2 over the constant Z ring. The tensor assertion is valid even in that last case because the contraction survives tensoring. No categorical projectivity, uniform finite cover, discreteness of coefficients, constant-ring hypothesis or pointwise exactness of arbitrary sheaf evaluation is assumed.

The first server-only `review_split` check passed with zero new nodes. Its informational message about the unit having no realization recorded is inherited: this auxiliary node is not the unit's key statement. The required deliver.py dry run and final push follow this report.
