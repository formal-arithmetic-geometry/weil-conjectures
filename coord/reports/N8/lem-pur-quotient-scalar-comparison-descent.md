## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-quotient-scalar-comparison-descent.json`: statement, now split into eleven proof steps; not a Mathlib leaf.
- `citations.json`: 24 verbatim statement extracts, one for every step/node citation.
- This report. Search answers and the research log are retained in the sandbox.

## New nodes

None. No new Mathlib leaves. The existing DAG supplies all the non-elementary ingredients, including the generic pointwise descent machinery. The item's statement is retained verbatim; flat-module and strict-Roos definition dependencies have been added to specify its existing terminology and coordinate convention.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, the item id, and scalar/comparison/resolution terminology. No project declaration states this whole assertion. The existing `Complete/Defs.lean` supplies completion constructions but not the arbitrary ring-sheaf augmentation and its normalized descent. `LeftDerivedFromResolvingClass.lean` is a generic theorem already represented by a different DAG node; it is not an attachment for this item. Statements under `lean/Sheaf/` were also searched for context and were not treated as upstream finished proofs.

## Literature requested

None. No WANTED document is necessary: the source PDF and the required Stacks source files are present.

## Findings and changes

The imported node had an empty proof, not a proof of its chain-level or derived assertions. Its source already explicitly warned that this is an expansion rather than a verbatim assertion of Bhatt–Scholze. I read Definition 3.4.10 and Proposition 3.5.1 on PDF pages 22 and 24. Those give completed tensor and the natural derived-reduction map in their more specialized noetherian/replete setting. They are background here, not a black box proving the arbitrary-site statement. Accordingly `proof_origin.by` is `agent`; the proof gives the balanced scalar maps and uses existing Stacks-based descent nodes. It makes no assertion that the product cone computes an ordinary inverse limit on arbitrary towers, or that the coefficients are flat, or that an arbitrary sheaf category has exact products.

The universal derived comparison maps point FROM the derived functors TO the ordinary homotopy-category functors. The descent is constructed using the right Kan universal property in this orientation. It is not an attempt to apply localization directly to ordinary tensor on all complexes, which need not preserve quasi-isomorphisms.

The chapter and unit were read before the item. This item is not a unit key node, so no unit realization file changes. The blueprint ancestor is `lem-weil-scalar-extension-composition`; I read its current main-20261015 proof. This argument supplies the augmentation on integral representatives needed by its finite-free scalar-comparison child and does not replace any six-functor or purity route.

## Mathlib research

I retained the item's four inherited searches without claiming to have run them myself. I then ran five fresh searches using the prescribed `msearch.py` and read the complete stored answers (`search-1.txt` through `search-5.txt`), including two different natural-language phrasings. All five services/commands answered successfully. The queries and verbatim returned results are appended to the item's search records and independently logged in `searches.jsonl`.

The first LeanFinder query found exact-functor comparisons, Tor, tensor infrastructure and ordinary flat scalar extension. Loogle found the general left-derived/right-Kan definitions. LeanSearch found `Functor.leftDerivedNatTrans`, `leftDerivedLift`, and uniqueness, together with classical projective-resolution transformations. The second LeanFinder query found localization extension of natural transformations and pointwise Kan infrastructure. The grep found four unrelated scalar-tower lines and no Roos augmentation. I read the generic Mathlib left-derived and pointwise-left-derived source around the relevant definitions. These are infrastructure for parts of the argument; none constructs the specified ring-sheaf tower, proves its tensor/product/cone invariance, and gives the entire item's assertion in a one-line specialization. Thus the item remains a split statement, not a Mathlib leaf.

## Not duplicates

No new-node/existing-node pairs arise, because no node is created. The whole-DAG statement search located the existing K-flat resolution, change-of-rings, Roos homotopy, Roos-coordinate quasi-isomorphism, essential-constancy, pointwise-Kan bridge and total-localization nodes, and the proof reuses them. Blueprint searches for `scalar augmentation` and `coefficient-tower`, in addition to the ancestor lookup, found no blueprint node stating this entire item. `lem-pe-kflat-roos-representative-invariance` is related but concerns the augmentation from P with R acting as the scalar ring, not the general two-ring scalar augmentation or its universal left-derived transformation; I do not duplicate it or apply it with changed hypotheses.

## Review by N8

I reread delivery-errors B–E against the actual node and the source passages. There are no new statements to check under B1–B9: the delivery does not introduce a proof hidden in a new unsplit node, an elementary new node, or a relabelled clause. The item itself keeps its statement. It has a self-contained proof, explicit scalar actions and cone signs, and recorded sources. The complete inherited fields and searches are preserved. Each proof step is under 2000 characters, so no long step masks an omitted auxiliary lemma.

For step 1 I read `def-pur-sheaf-tensor-product`, `def-pc-sheaf-restrict-scalars` and `def-weil-inverse-system`. The tensor definition is sheafification of the sectionwise presheaf tensor; the scalar definition retains the underlying abelian sheaf; and the inverse-system definition supplies strict transitions. The balanced-map calculation is carried out, including restriction compatibility. A tower of S-algebras has structure-compatible transitions, so t_n c_(n+1)=c_n, with no epimorphism hypothesis. This is the equality the step actually uses.

For step 2 I read `def-weil-strict-roos-model`, which explicitly defines the differential and compatible-family augmentation with first coordinate zero. Substitution gives d(0,alpha)=(0,alpha d), because (1-s)alpha=0. The product and pure-tensor arguments establish uniqueness of chain maps, not uniqueness of arbitrary maps into an unspecified derived-limit object. Local generation after sheafification is sufficient, and global generation of sections is not assumed.

For step 3 I read the entire statement of `lem-pur-strict-roos-homotopy-functor`. It applies to strict tower homotopies commuting with transitions, exactly the compatibility verified for h tensor 1. It gives the required signed homotopy, rather than just existence of the object Cone(1-s)[-1]. The abstract-derived-category definition supplies localization after passing to the homotopy category. No functoriality of arbitrary choices of cones is used.

For step 4 I checked Stacks 06YS (`sites-cohomology-lemma-K-flat-resolution`) in sites-cohomology.tex against `lem-pc-kflat-resolution`. Its conclusion explicitly includes flat terms, K-flatness, termwise surjectivity and no boundedness condition. The module-category definition gives abelianness on the small site. `lem-pur-quasi-isos-saturated-triangulated` explicitly includes the right fraction axioms and two-out-of-three, so these are cited theorems, not an assumption silently imported from localization notation.

For step 5 I checked Stacks 06YT (`sites-cohomology-lemma-derived-tor-quasi-isomorphism-other-side`) and the statement of `lem-pur-change-of-rings-kflat-quasi-iso`. This last node states exactly invariance of scalar extension for quasi-isomorphisms between K-flat complexes, with arbitrary ring-sheaf maps. It is applied separately to R to S and R to B_n. The restriction-of-scalars definition and the kernels/cokernels clause in the module-category definition justify the short explicit cohomology argument. In particular I did not cite the completed-integral special-case exact-restriction lemma for arbitrary S and B_n.

Step 6 uses the exact-product hypothesis in the question itself, plus the definition of cohomology. I checked the short calculation on kernels, images and their quotient, rather than assuming products are exact because these are sheaves. This proves the product map is a quasi-isomorphism. Step 7 then cites the precise statement of `lem-pe-roos-coordinates-quasi-iso`. I checked its coordinates and matched its endomorphism to NEGATIVE (1-s), since reordering the strict model introduces that sign. Both coordinate maps really are V(f), as the lemma requires. This corrects the potential sign mismatch between the two existing Roos conventions.

For step 8 I opened each of `lem-pur-resolving-class-essential-constancy`, `lem-pur-left-derived-defined-pointwise-kan-bridge`, and `lem-pur-total-left-derived-localization`. The first states essential constancy under right fractions, resolutions and inversion on resolving objects, and invertibility of the identity leg on those objects. The second identifies the identity leg with the pointwise-Kan comparison. The third assembles the pointwise extensions into a universal right Kan extension. The earlier steps verify the resolution and inversion assumptions for BOTH functors. This uses their published statements, not hidden constructions in their proofs. It avoids imposing exactness of a functor on the homotopy category as an additional unverified premise of an exact-triangulated version of the derivability theorem.

For steps 9–10 the cited universal property gives the unique lift of beta composed with epsilon_F, in the correct direction. I explicitly inverted epsilon_G only on resolving objects. The displayed resolution formula then forces a normalized natural transformation on every derived object. Hence independence of representatives is a consequence of an already constructed natural transformation, not a claim that an arbitrary derived isomorphism lifts to one chain map. All complexes have the necessary resolution by the cited theorem; localization inverts its quasi-isomorphism by the cited definition.

For step 11 I checked the unit against `def-weil-strict-roos-model` and the explicit tensor definition. Multiplication and p mapping to p tensor 1 are inverse on local pure tensors and hence on the sheafified tensor. Every quotient projection is p mapping to p tensor 1-bar, and the first component stays zero. This is an equality of the specified chain maps before descent.

The small cases checked were P=0; all B_n=0; a constant tower B_n=S; the identity map R=S; a=0; and a invertible. The augmentation is respectively zero, zero, the constant compatible-family map, the usual scalar unit, the identity-tower unit, and the zero quotient-tower unit. A non-surjective structure map S to S[x] with constant tower also satisfies the formula: no step solves for a lift of an element of B_n. Nonflat quotient coefficients are allowed by the exact K-flat change-of-rings hypothesis. The arbitrary unbounded case is covered by 06YS, not by a bounded-projective resolution argument. These checks do not change the statement or assume the augmentation is an isomorphism.

The two off-unit statement citations are declared in `split_report.tool_uses`: K-flat resolution existence is a generic ringed-site tool, and the Roos-coordinate lemma is a generic cone-comparison tool. Both are strictly auxiliary to this coefficient-comparison argument. No nonpermitted SGA source is used. Every step/node citation has a verbatim extract in `citations.json`; those extracts were checked by direct substring comparison with the open node statement. I also checked that these auxiliary dependencies do not reach the item, avoiding a circular citation.

## Unfinished work

None at the level of this split. The cited existing open nodes retain their own work; no claim is made that their Lean proofs are closed. The first dry run rejected two restriction-of-scalars extracts as shorter than 40 characters. Both were expanded to the full defining sentence; the mathematical argument and node citations were unchanged. Server dry run and direct delivery follow this repair.
