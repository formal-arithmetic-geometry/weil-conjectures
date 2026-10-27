# Stage-1 report: lem-sfb-resolved-total-comparison-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-resolved-total-comparison-descent.json: existing statement, now split into seven steps; Mathlib has related object-resolution naturality but no match for this strict cosimplicial total right-derived comparison and its common-resolution descent.
- citations.json: verbatim statement excerpts for every citation of every proof step.
- report.md: this report. searches.jsonl contains the five actual Q118 searches; write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. No unit realization record changes: this item is a supporting lemma, not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures both for the exact blueprint tag/id and for resolved-total, common-resolution and cosimplicial/injective terminology. The exact id and cosimplicial/injective searches returned no declarations. Broader common-resolution hits concern tensor comparisons or other sheaf comparisons, not all clauses of this item. A sorry-free declaration of the project giving the full statement was not found.

## WANTED

None. All sources needed for this split are present.

## What was wrong or missing

The imported item had no proof steps. Its statement is preserved verbatim, including all quantifiers, naturality on columns and totals, the specified zigzag, its augmentation conditions, and independence from choices. No statement dispute was found.

The main danger is applying F to a quasi-isomorphism without justification. F is left exact and additive, not exact. Step 5 instead proves the mapped total is a quasi-isomorphism using inverse derived units on the two injective totals and the finite-biproduct comparison. Applying the cohomology functors through localization then gives the required chain-level assertion. No preservation of injectives by F, or exactness of F, occurs.

The ancestor script returns `blueprint.from.node = None`. This is already the item's inherited ancestry. I retained its null ancestor and complete via list, and explained the current blueprint place in split_report rather than inventing a blueprint ancestor. Current main-20261015 paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md is the open-direct-image route. The inherited parent nonnegative-derived-totalization uses the present item precisely for choice independence and naturality. No chapter or unit route is changed.

## What could not be finished

Nothing remains in the mathematical split. Delivery validation is run after writing this report. The cited finite-total comparison is an existing unsplit DAG node; its later split is separate work, and it is cited only for what its statement explicitly provides.

## Searches and reuse

I read the live item and parent nonnegative-derived-totalization and searched all of dag/nodes, not only the chapter, for functorial injective resolutions, finite totals, inverse derived units, total-comparison naturality, and the source tags 0141, 05TH, 0133. I read the statements of the candidate existing lemmas on functorial resolutions, total replacements, K-injective morphisms, normalized resolution naturality and the finite-total comparison. The two facts actually needed are already stated in lem-sfb-injective-finite-total-derived-comparison and def-weil-abstract-derived-category. The latter is used as a generic definition/tool from another unit and is declared in split_report.tool_uses. Other candidates were unnecessary: the quantified functor I is already given in the item's last clause, so its existence need not be reproved, and the naturality of the derived unit can be inverted directly in three lines.

Blueprint searches with tools/blueprint_refs.py for `functorial injective`, `total comparison`, and `cosimplicial` all returned no imported blueprint-node match. The ancestor command was also run. No new lemma is introduced, so there are no new/existing tag pairs needing a non-duplication justification.

The actual Q118 msearch queries were: leanfinder on naturality/independence of injective replacements for cosimplicial totals; loogle on `"InjectiveResolution", "naturality"`; grep on `(cosimplicial|total).*(resolution|Resolution).*(natur|compar)|[Rr]esolution.*zigzag`; leansearch on a common functorial injective resolution comparing totals; and a second leanfinder phrasing on common-resolution zigzags and the inverse unit of a total right derived functor. All services answered. I read the returned names and inspected Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean, especially iso_hom_naturality and iso_inv_naturality at lines 247–260 and injectiveResolutions above them, and CategoryTheory/Abelian/RightDerived.lean:126–151. These compare resolutions of individual abelian-category objects (and the natural-number-indexed right-derived cohomology functors), not total right-derived objects of arbitrary strict cosimplicial diagrams. Thus these hits do not prove the present item in one specialization. Both inherited searches and the actual new Q118 queries/results are retained.

## Not duplicates

No new nodes. The finite-total comparison is reused, and elementary inversion, two-out-of-three on cohomology, and cancellation along a zigzag stay as proof steps. The item itself remains distinct from that existing comparison: the existing statement gives the normalized comparison and naturality of beta, while this item proves naturality of chi under a strict resolution square and its common-resolution descent.

## Review by Q118

I read Stacks derived.tex, Tag 0141 (lemma-functorial-injective-resolutions and remark-match), including the natural commuting augmentation square, Tag 05TH (lemma-injective-acyclic), and Tag 015J (lemma-two-ss-complex-functor), including its finite-total equality and the computation by the injective total. I also read homology.tex Tag 0133 (lemma-double-complex-gives-resolution) and the K-injective discussion, Tags 070I and 070J, to verify the scope of the existing total-comparison input. These are source material for the existing finite-total lemma; I do not claim that any source states the whole cosimplicial descent result verbatim. The added argument is explicitly agent-authored. The current blueprint's open-direct-image proof and the parent split fix its route. There are no new node statements to check against separate sources.

Step 1 uses the existing finite-total comparison exactly as stated: its hypotheses are two Grothendieck abelian categories, a left exact additive F, nonnegative diagrams, a columnwise quasi-isomorphism, and injective terms in the replacement. These are all hypotheses of this item for u and v. Its statement explicitly supplies T(u), T(v), K-injectivity of the totals, the prescribed chi and column isomorphisms, and naturality of beta for any strict g. It does not require g to be a quasi-isomorphism. citations.json includes the relevant verbatim statement.

Step 2 uses the same node's explicit identification of rho as the inverse right-derived unit on a bounded-below injective complex. A right-derived unit is a natural transformation; I write its naturality equality and multiply by its two inverse components. This is elementary algebra of an already supplied natural transformation, not an additional derived-functor computation or an appeal to a source lemma with unstated hypotheses. Both column complexes and both totals are eligible by step 1. In particular the argument takes place in the stated ordinary unbounded derived categories, with no change to a different bounded derived functor.

Step 3 uses only beta naturality from the finite-total statement, the unit identity proved in step 2, and the given equality gu=vf. I checked the direction and domain of each factor: chi starts at RF(QT(K)), beta ends at QT(FJ), and the resulting equality has target QT(FM). The column formula follows by the same displayed two multiplications, with no beta needed. Identities and composites are the two functor laws, so no coherence theorem is being hidden here.

Step 4 uses def-weil-abstract-derived-category for the meaning of quasi-isomorphism and cohomology. I specified every intermediate augmentation from K. The maps I(u), I(w) are quasi-isomorphisms by the two naturality equations and invertibility of the induced cohomology maps, not because I is assumed exact or additive. The cosimplicial identities are preserved by the functor laws on the category of complexes. The hypothesis on I supplies both nonnegativity and injective terms for I(K), I(J), I(N); J and N already have those properties. This is a construction using the quantified I, not an assertion that arbitrary functorial resolutions have a uniform bound.

Step 5 uses the finite-total statement for T(h) being a quasi-isomorphism and its two totals computing RF. Its hypothesis that the target columns be termwise injective holds for every zigzag leg, irrespective of its direction. The source columns are injective too, providing its invertible rho. Naturality gives the displayed conjugation equality; beta gives the second one. def-weil-abstract-derived-category explicitly states that cohomology factors through Q, and defines quasi-isomorphisms by all cohomology maps being invertible. That is the full justification for passing back from localized isomorphisms to quasi-isomorphisms; it does not invoke an uncited reflection theorem. These statements are quoted verbatim in citations.json.

Step 6 needs no additional cited theorem: it applies step 3 over 1_K to each augmentation-preserving leg, with all chi inverses justified in step 1 and all mapped-leg inverses justified in step 5. I checked both orientations separately. The intermediate factors cancel, giving exactly chi_w chi_u^{-1}; this proves independence even for a different I or a different eligible augmented zigzag. The identity and cocycle equalities are then explicit products. No general descent or path-independence theorem is being assumed.

Step 7 writes both sides of the change-of-replacement naturality square as the same three-factor expression, using steps 3 and 6. It covers two source and two target choices and does not assume a preferred lift. It therefore verifies the last compatibility clause as well as naturality for one fixed set of resolutions.

For B1–B10, there are no new nodes, the statement and its definition dependencies are retained, the actual Mathlib searches are recorded, and the ancestry has been checked. For C1–C8 I opened both cited node statements and prepared an exact quote for every use; all non-elementary totalization and injective-computation assertions come from the existing finite-total statement. I checked dependency reachability and neither cited node depends on this item. The only off-unit citation is the generic derived-category/cohomology definition, explicitly declared as a tool. For D1–D5 no clause has been renamed as a new lemma: the strict-square calculation and the complete zigzag argument are written out. For E1–E7 I checked the bounds, injective terms, direction of the arrows and inverse factors, and every use of two-out-of-three.

The small cases are consistent: for F the identity, beta and rho are the usual identity comparisons and the formulas reduce to the localized resolution square; for an exact zero functor the target is zero and every comparison is the unique isomorphism of zero objects; with only one nonzero internal degree the same calculation is the ordinary cosimplicial total calculation. If u=w, the zigzag value is chi_u chi_u^{-1}=1 even when the common resolution differs. No boundedness in the cosimplicial degree is used: in total degree r there are only r+1 summands because both indices are nonnegative. F is never required to preserve infinite sums. All proof steps are below 2000 characters, and each algebraic subargument is displayed rather than hidden in a long step.
