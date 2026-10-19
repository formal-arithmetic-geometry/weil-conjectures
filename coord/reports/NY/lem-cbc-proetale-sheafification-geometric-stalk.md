# Worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-proetale-sheafification-geometric-stalk.json: existing statement split in six steps; not a Mathlib leaf.
- citations.json: verbatim statement quotations for every citation of every step.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of WeilConjectures for the blueprint tag, sheafification/stalk combinations, and points/stalks in the ProEtale sources found no project declaration stating this comparison. Proetale/Sheafification.lean only supplies sheafification existence, not geometric-stalk invariance. Etale point and strictly henselian etale results do not state the pro-etale assertion. Upstream master is reference material, not a closed-proof certificate.

## WANTED

None.

## Faults found and changes

The item had no proof. Its statement is retained exactly: arbitrary schemes, arbitrary abelian presheaves, the fixed algebraically closed geometric field, all pointed weakly etale neighbourhoods, the unit-induced homomorphism, and naturality. No condensed-coefficient or derived-complete comparison is asserted here.

The existing Mathlib candidate is valid only after constructing a point of the site. Generic fiber statements therefore do not make this item a Mathlib leaf. The new searches are recorded from searches.jsonl, with LeanSearch's HTTP error marked unavailable. A second semantic phrasing found Point.toPresheafFiber_map_bijective, still conditional on a site point.

The six-step argument follows proetale.tex 0F6B and 0F6C and the paragraph before 0993, together with the local-representative content of the comparison in sites.tex 00Y8(3). The unit has no proof steps; this is a refinement of the ancestor extension-by-zero node's stalk-description sentence, and leaves the chapter and unit untouched. The whole blueprint was searched with blueprint_refs.py search sheafification and pro.etale.*stalk|geometric.*stalk. The small etale sheafification stalk nodes are not pro-etale statements and are not used as though they were.

## Unfinished

None at this one-level split. The cited pre-existing unsplit facts remain work for their own items.

## Not duplicates

No new nodes were created. DAG tag searches for 0F6B, 0F6C, 00Y8 and local sheafification terminology located the existing ingredients. In particular the existing weak-etale-field and separable-extension embedding lemmas are reused, as is the general local-bijectivity Mathlib leaf.

## Review by NY

I read proetale.tex, lemma-cofinal-etale (0F6B), lemma-geometric-lift-to-cover (0F6C), and the geometric-point paragraph preceding lemma-classical-point (0993); sites.tex, lemma-point-pushforward-sheaf (00Y8), lemma-sections-sheafification (00WK), and the sheafification adjunction; more-algebra.tex, lemma-absolutely-flat-over-field (092Q); more-morphisms.tex, lemma-weakly-etale-characterize (094S) and lemma-base-change-weakly-etale (094U); fields.tex, lemma-map-into-algebraic-closure (09GU); and topologies.tex, lemma-fpqc (022D), part (3). I also read Mathlib Sites/LocallyBijective.lean lines 114–158 and Sites/Localization.lean lines 76–82, which implement the cited general abelian local-bijectivity leaf. There are no new statement nodes whose sources require review.

Step 1 uses the statement of def-weil-proetale-geometric-stalk for the pointed category and its filtered opposite, def-weil-size-convention for a small index in the larger universe, and def-weil-pbc-category-colimit for the universal property. It does not assume a presheaf has the sheaf property: I give the class relation, the finite common-refinement/equalization argument, the group operations, and the descent of a compatible family of homomorphisms explicitly. This establishes single-section representatives and eventual equality for both presheaves. The definition node's proof is not used as an extra black box.

Step 2 uses the actual statements of lem-galois-fpqc-covering-base-change (an arbitrary scheme base change), lem-weil-pbc-weakly-etale-composition-base-change, lem-weil-pbc-weakly-etale-source-locality, def-weil-pbc-ind-etale-algebra (the affine equivalence), lem-weil-pbc-weak-etale-field (separable algebraic residue fields), and lem-weil-pbc-separable-extension-embeds-separably-closed (an embedding into the specified field). The site definition supplies fpqc coverings. The geometric-point and affine-spectrum definitions give precisely the morphism from the residue embedding; the fibre-product definition proves it lies over the fixed lift. The field theorem is applied over Omega only after weak etale base change and restriction to an affine open, not to an arbitrary residue extension. Algebraic closedness implies the separable-root condition directly. I corrected my preliminary argument: Spec Omega need not be an object of X_proet, so the small-site covering axiom alone cannot justify this base change. The existing general fpqc base-change Mathlib leaf supplies exactly the missing justification. This avoids an extra hypothesis on the geometric point. The selected V_i is an original bounded site object, so all pointed refinements used later are in the original index. The auxiliary fibre need not be an X_proet object.

Step 3 uses def-weil-pbc-sheafification only for its adjunction/universal property, and lem-weil-pbc-site-sheafification-iso-locally-bijective only for its equivalence between an abelian map becoming an isomorphism and its covering-wise local injectivity/surjectivity. I explicitly establish that the sheafified unit is an isomorphism using uniqueness of factorization. No plus construction is inferred from the definition, and no set-valued comparison is silently upgraded to abelian coefficients.

Steps 4 and 5 use the preceding steps, with no additional black box: choose a local preimage then lift the point for surjectivity; first restrict to a pointed refinement killing the image, then to a cover killing the original section, and lift the point for injectivity. The order of these two refinements matters and is written out. Neither an etale-only stalk lemma nor a conservativity assertion is used. Step 6 uses only sheafification's unique extension property and evaluates the naturality square on representatives; inverse naturality follows by composing with inverse components.

I checked arbitrary non-quasi-compact and non-separated bases: none of the cited lemmas imposes either restriction. The empty scheme has no geometric point, so the item makes no claim there; the cover of a neighbourhood carrying the point cannot be empty. For a zero presheaf and a presheaf already a sheaf the comparison specializes to the identity. A cover with many components requires just one component above the fixed point; there is no finite-cover hypothesis in the stalk argument. Auxiliary affine restriction is justified by source locality, not by an unproved affineness of intersections. Natural maps keep the field Omega fixed rather than replacing it with a larger geometric field. Since no new nodes were created, B1–B9 introduce no new-node issue; C1/C4 were checked by reading every cited statement and copying its relevant statement into citations.json. The item was not relabelled as a new lemma, and no cycle goes through its parent or through the classical-stalk comparison.

The off-unit statements listed in split_report.tool_uses are generic weak-etale/field tools for cover lifting; they replace no unit proof step. The fpqc base-change and local-bijectivity results are already Mathlib leaves.

## Second reading by NY

- Item statement: checked arbitrary X, fixed algebraically closed Omega, all bounded pointed weakly etale neighbourhoods, abelian presheaf and unit map against proetale.tex 0F6B (lemma-cofinal-etale), 0F6C (lemma-geometric-lift-to-cover), the paragraph before 0993, and sites.tex 00Y8(3) (lemma-point-pushforward-sheaf); agrees, with the abelian argument supplied rather than inferred from a set-valued statement.
- Step 1: read def-weil-proetale-geometric-stalk, def-weil-size-convention and def-weil-pbc-category-colimit; their statements supply filteredness, the index bound and the colimit universal property. The finite-refinement/equalization construction supplies single representatives, zero detection and abelian operations directly; valid for presheaves as well as sheaves.
- Step 2: read every one of its ten cited node statements; topologies.tex 022D(3) supplies arbitrary fpqc base change, more-morphisms.tex 094T(2)/094U(2) supplies weakly etale composition/base change, and 094S supplies affine source restriction. The affine equivalence and more-algebra.tex 092Q apply to B over Omega, not to an arbitrary residue extension. The cited separable-embedding leaf applies with base field and target both Omega; fields.tex 09GU itself states the algebraically closed version, while the node explicitly records the separable generalization and IsSepClosed.lift. The geometric-point, spectrum and fibre-product statements supply the lift and its exact composite. Replaced the final skeleton-transport sentence by the explicit inverse-isomorphism lift and section restriction maps.
- Step 3: checked the sheafification universal property against sites.tex 00WH and read the abelian local-bijectivity node, Mathlib Sites/LocallyBijective.lean lines 114-158 and Sites/Localization.lean lines 76-82. Its statement gives precisely covering-wise lifts and equality. Wrote both uniqueness arguments with the two distinct units; marked the step non-elementary because it invokes the substantive local-bijectivity theorem.
- Step 4: checked against Steps 1-3; one covering lift and one lifted point give a preimage of each representative. The argument is elementary and uses no further fact.
- Step 5: checked against Steps 1-3; eventual zero of the image precedes local injectivity and a second pointed refinement. Kernel zero implies injectivity; unique preimages prove additivity of the inverse. The argument is elementary.
- Step 6: checked against def-weil-pbc-sheafification and Step 1; the unit identity gives the displayed representative in both directions of the square. If c_P and c_Q are the comparison isomorphisms and f,g the induced presheaf/sheaf stalk maps, g c_P = c_Q f implies c_Q^{-1} g = f c_P^{-1} by composition; naturality of inverses follows.
- New nodes: none, so no B1-B7 form defects, duplicate/special-case nodes, disguised restatement, or new-node Mathlib-leaf search obligation. Independently searched Mathlib with the abelian associated-sheaf/fiber phrasing recorded in searches.jsonl; the point-fiber hit assumes a site point and does not finish this item. Read the slopmaster2 ProEtale/Proetale/Sheafification.lean: it states existence only, with no geometric-stalk comparison; the upstream master remains reference material, not a proof certificate.
- Edge cases: empty X has no geometric point; a neighbourhood containing a point is nonempty and its cover has a component above that point. Zero presheaves and presheaves already sheaves satisfy the construction. Over an algebraically closed field the residue embedding is over that same field; no enlargement is made. Infinite covers require only one component, and no quasi-compactness or separatedness of X is assumed. The finitely generated subalgebra assertion of 092Q was also read and agrees with the existing field node.

Changes: expanded Step 2 skeleton replacement to actual maps (E5); expanded Step 3 unit-isomorphism proof and corrected its elementary flag (C2); added the independent search and this second reading. No statement or citation changed, and no node was created or removed. The existing Review by NY section is retained.

Off-unit tool requests for the maintainer: lem-weil-pbc-weakly-etale-composition-base-change, lem-weil-pbc-weakly-etale-source-locality, lem-weil-pbc-weak-etale-field and lem-weil-pbc-separable-extension-embeds-separably-closed are generic cover-lifting tools, not replacements for a unit argument. The unit sk-prop-sf-cbc has no proof steps; the ancestor lem-cbc-proetale-extension-zero needs its stalk-description sentence made explicit. No unit-local node supplies these generic algebraic tools. Only the maintainer records any required top-level tool_uses. The dry run rejected removal of the worker request list; tools/review_split.py lines 97-100 explicitly distinguish split_report.tool_uses requests from the maintainer field and accept the former, so the original request list is retained.
