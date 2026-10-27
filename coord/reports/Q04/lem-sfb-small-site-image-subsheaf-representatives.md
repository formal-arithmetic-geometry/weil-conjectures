# Stage-1 report: lem-sfb-small-site-image-subsheaf-representatives

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-small-site-image-subsheaf-representatives.json — statement, split; all clauses unchanged, seven explicit elementary steps; no exact Mathlib match.
- citations.json — one entry for each step/node pair, with a verbatim substring of the cited statement.
- report.md — this report. searches.jsonl is the unmodified log written by msearch.py.

New nodes: 0. New Mathlib leaves: 0. No Lean, compiler or build commands, repository writes, launcher edits, or direct git commands.

## Attachments

None. Searched all lean/WeilConjectures for the exact blueprint tag and for imageSubsheaf, image subsheaf, sectionwise image, actual subsheaf representatives, imageSheaf, imageInclusion and ImageIndex. No project declaration states all clauses of this general small-ringed-site item. The parent node records specialized integral-model helpers and a larger parent theorem, which do not supply the present general statement. Individual source hits about images or injectivity cover only pieces and are not attachments.

## WANTED

None. The blueprint and all Stacks passages needed were available locally.

## Corrections and scope

The imported node had a statement and no proof. I supplied the actual inherited operations, monomorphism cancellation argument, range presheaf, matching-family gluing, explicit natural linear inverse, equivalence over a fixed target, and universe bound. No statement dispute or hypothesis change was necessary. The proof remains on the fixed unit route: it expands the last sentence of det-lem-int-integral-heart-triangulated paragraph (2), the smallness of the data. The item's contribution is the image-subsheaf portion of its parent's original steps 8–9; it is not the unit's key statement, so no unit record is edited.

Every proof dependency is already a statement dependency and an existing definition. In particular def-weil-sheaf-of-modules-category explicitly asserts that kernels are computed sectionwise. This is not an unsupported inference from the term “module sheaf”. With that sentence available, cancelling a monomorphism against its kernel inclusion proves sectionwise injectivity directly. No separate categorical-mono lemma is needed. No off-unit statement tool is invoked.

The creator's six recorded searches were retained, including its explicitly unavailable invalid file scope, rather than rewritten as successful searches. Q04 ran six additional searches with msearch.py and read their results. The two semantic phrasings locate presheaf well-poweredness and type-valued image sheaves; Loogle has zero hits for SheafOfModules, CategoryTheory.Subobject; LeanSearch finds generic image factorization and monoOver smallness. Read Mathlib/Algebra/Category/ModuleCat/Presheaf/Generator.lean:97–99: its wellPowered instance is an abstract result for presheaves. Read Mathlib/CategoryTheory/Sites/Subsheaf.lean:198–241: Sheaf.image uses the sheafification of a type-valued range, and does not itself give actual sectionwise module images, the explicit code sets, or the equivalence criterion. PresheafOfModules.injective_of_mono is a partial hit for presheaves only. The full item is therefore not a one-line specialization of these hits.

## Not duplicates

No new node is proposed, so there are no new/existing pairs to justify. Searched the whole DAG for Tag 03DA and monomorphism/sectionwise-kernel/injectivity terms and searched the blueprint with blueprint_refs.py for subsheaf and monomorphism. Read lem-sfb-image-subobject-of-monomorphism: it identifies an abstract categorical image subobject, whereas the present item constructs actual sectionwise module subsheaves and size bounds. Read lem-weil-pbc-module-sheaves-limits-sectionwise: it concerns arbitrary small limits and would be a stronger reusable tool for kernels, but the module-sheaf definition already explicitly provides precisely the kernel fact required. Neither warrants a new node. blueprint_refs.py ancestor gives det-lem-int-integral-heart-triangulated; the existing from.place and via list were retained, and same_as remains [] after the whole-blueprint searches.

## Review by Q04

I read the item, its current parent split, the chapter and integral-heart unit records, and the current main-20261015 blueprint proof of det-lem-int-integral-heart-triangulated. The unit and proof say that the small-site and gluing data form a set; they do not give this range construction, so proof_origin.by is agent. I read Stacks sites-modules.tex, definition-sheaf-modules (Tag 03CV), and the kernel formula immediately preceding lemma-abelian (Tag 03DA), together with that lemma and its proof. I also read sites.tex definition-sheaf-sets (Tag 00VM) and its explicit matching-family formulation and empty-cover remark. The input is an arbitrary small ringed site and a sheaf of rings, with no commutativity, points, subcanonical topology, or exactness of arbitrary sectionwise images assumed. No SGA route is used. There are no new nodes requiring an additional source review.

For step 1 I opened def-weil-sheaf-of-modules-category and checked its sectionwise operations, semilinearity and linear morphisms clauses. Restriction stability and the sheaf axiom are hypotheses on E_j, not conclusions assumed from an arbitrary subpresheaf. Restricting the existing operations gives every presheaf identity and cancellation through the actual subset inclusion proves that inclusion monic. Its uniqueness is the uniqueness of the inherited operations/maps on the specified subsets.

For step 2 I checked the exact sentence “kernels are computed sectionwise” in that same node; citations.json quotes it verbatim. Site smallness relative to the module universe is supplied by the item, as that node requires for its categorical assertions. Write k for the actual kernel-subset inclusion. The equality mk=m0 and monicity give k=0; evaluating says each kernel element is zero, and applying this to x-y proves injectivity. This is a few-line cancellation calculation using the cited kernel statement, not an appeal to an uncited exactness theorem.

For step 3 the same definition supplies linear morphisms and semilinear restriction maps. The displayed zero, sum, negative and scalar identities prove range-submodule closure, and the displayed naturality equation proves restriction stability. These are direct calculations, not a node restating one clause of the item.

For step 4 I opened def-weil-pbc-sites-and-cohomology and verified that it explicitly gives the covering equalizer/sheaf axiom. Covering fibre products used in the argument exist by its site axioms; arbitrary fibre products in the whole category are not assumed. Each n_a has a unique preimage by step 2, and injectivity on the overlap object makes these preimages compatible. M's sheaf axiom supplies the gluing, and P_j's separatedness supplies uniqueness in N. Thus we prove membership in E_j rather than presume that all range presheaves are sheaves. The empty covering has a unique family and M(V) has one element, so the argument remains valid there.

For step 5 the module-sheaf definition's morphism clause is exactly the required interface: linear components and naturality. I wrote the identities proving inverse linearity and naturality, each checked by applying the bijection e_V or e_W. This produces an actual isomorphism and its equation with the original m, not merely bijective underlying section functions.

Step 6 uses only steps 1 and 5 and elementary componentwise composition of isomorphisms, so its uses list is empty. An isomorphism over the target has surjective components and preserves the actual ranges; equal ranges put e and e' into the very same subsheaf, giving (e')^{-1}e. The own-inclusion clause follows since the underlying map is the literal subset inclusion. No abstract image theorem or well-poweredness theorem is hidden here.

For step 7 I opened def-weil-size-convention and checked it is the metatheoretic universe convention. The present statement explicitly requires a Grothendieck universe (not merely an arbitrary Stacks partial universe); powersets, pairs, transitivity and unions indexed by an element of that universe are its defining closure axioms. The proof explicitly encodes products as graphs in a powerset and then uses subset closure; the disjoint union is J-indexed. The hypothesis K in V controls all object-indexed codes, and each P_j(V) in V controls their powersets; no uncontrolled large category of all sheaves is used. Since no arrow-map choice is made after a code is fixed, no extra universe bound for choices of restrictions is needed.

I checked small cases on a one-object trivial-topology site: the statement becomes the usual range-submodule classification of subobjects of an R-module, including the zero ring and zero module. For empty J the total set is empty; for empty K there is one empty code per j, and sheaves on the empty category are uniquely specified; for zero targets there is only the zero image. Empty coverings were checked separately in step 4. All seven steps are below 1000 characters and contain the actual calculations rather than hidden long lemmas.

Against delivery-errors B–E: there are no new statement-only nodes, duplicates, undeclared notions, or Mathlib leaf claims to audit; all existing metadata and statement clauses are preserved. Each citation was checked against the node's statement rather than its proof and is quoted verbatim in citations.json. Non-elementary input facts are already explicit sentences in the cited nodes; what remains is a sequence of elementary calculations. The split does not move any clause into a new lemma. I found no missing hypotheses, change of coefficient notion, circular dependency, or false generalization to nonmonic images.

## Unfinished work

None in the stage-1 split. The mandatory remote dry run and direct delivery are performed after this report is written; their output is the final delivery record.
