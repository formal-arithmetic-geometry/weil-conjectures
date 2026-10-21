## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-square-zero-periodic-tensor.json: statement, split into seven steps; no Mathlib match for the whole assertion.
- No new nodes and no Mathlib leaves. citations.json copies the statements used by all sixteen step citations verbatim.

## Attachments

None. Searching WeilConjectures/ for the blueprint tag gave no declaration. Searches for periodic complexes, square-zero multiplication and annihilators found generic algebra and resolution infrastructure, not a declaration giving all the ring and pro-etale clauses. The item has no recorded Lean declaration to attach.

## WANTED

None. The current blueprint and the relevant Stacks sources are present.

## Findings and route

The item statement is correct as written and remains unchanged. Its source is the paragraph “The examples” in literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md. That paragraph constructs the periodic resolution for Z/ell^2. The item's exact-divisor hypothesis is precisely what the same proof needs for general R. I retained the localizing-closure unit's route, including the resolution rather than replacing it with a self-Tor black box. This item is not the unit's key statement, so no unit record is changed.

The existing DAG already contains the general tools: lem-pc-module-bounded-flat-kflat, lem-pc-bounded-above-flat-kflat-site, lem-weil-pbc-finite-type-constant-exact and lem-sf-constant-module-unit-locally-bijective. Their off-unit use is declared in split_report.tool_uses, with the specific purpose of each. Definitions are reused from their existing nodes. The blueprint searches for “periodic”, “square-zero”, “annihilator” and “bounded-above flat”, and the DAG statement/title searches, found no other blueprint node stating the whole item. blueprint.same_as is therefore empty; its existing precise blueprint.from.place is retained.

Some reused nodes have inaccurate source tags although their statements give exactly the facts needed here. The bounded-above flat ringed-site lemma is Tag 06YQ, sites-cohomology-lemma-bounded-flat-K-flat, not the 06YS appearing in lem-pc-bounded-above-flat-kflat-site's source. Exactness of constant sheafification is Tag 093J, sites-modules-lemma-constant-exact, rather than 093U appearing in lem-weil-pbc-finite-type-constant-exact. Tag 093T in the constant-unit node is a locally constant Hom lemma, not by itself the local-injectivity assertion. I read the constant-unit node's actual assertion, the module sheafification construction 03CY and sheafification sections 00WK; I use the node's explicit local-injectivity assertion, not a consequence inferred from 093T. These are source-metadata issues in dependencies, not changes to their statements or permission to edit them. My item uses the correct 06YQ and 093J source places.

Mathlib searches run with msearch.py are recorded in searches.jsonl and appended to the item's inherited searches. LeanFinder and LeanSearch were both available, with different phrasings. They returned generic Tor/projective resolution facts and torsion-by-element results. Loogle and the restricted grep found HomologicalComplex.alternatingConst and its homology interfaces; I read Mathlib/Algebra/Homology/AlternatingConst.lean, including its opening description and construction. It constructs periodic complexes but does not state the augmented exact-divisor resolution or the derived self-tensor calculation on ordinary modules and the pro-etale site. This is not a one-line specialization of those hits.

## Unfinished work

None for this one-level split. This delivery writes no Lean and makes no assertion that the remaining proof dependencies have been formalized.

## Not duplicates

No new nodes are proposed. In particular I did not make a second bounded-flat K-flat criterion, an exact constant-sheafification lemma, a rank-one tensor-unit lemma, a periodic resolution lemma restating the item, or a nonvanishing clause detached from the item.

## Review by Q26

I checked the seven steps against the current blueprint paragraph, the chapter and unit records, and the statements of every cited node. For the ordinary K-flat input I read more-algebra.tex, lemma-derived-tor-quasi-isomorphism (064K), and the K-flat derived-tensor construction/definition (064M). For the sheaf input I read sites-cohomology.tex, lemma-bounded-flat-K-flat (06YQ), including its bounded-above hypothesis. For constant sheafification I read sites-modules.tex, section-constant and lemma-constant-exact (093J); this says “Let C be a site”, with no Noetherian or finite-ring condition. I also read definition-flat (03ER), module sheafification (03CY), the actual 093T locally constant lemma, and sites.tex lemma-sections-sheafification (00WK). There are no new nodes requiring further sources.

Step 1 uses def-weil-abstract-derived-category for the cochain, cohomology and quasi-isomorphism definitions. The proof computes the actual kernels, images and quotient augmentation, so no separate resolution-existence theorem is hidden in it. The annihilator equality is used at each negative degree, and t^2=0 makes the differentials compose to zero. At degree zero the quotient kernel and surjectivity supply the augmentation check. Rank-one freeness is explicit.

Step 2 uses exactly the bounded-above flat module assertion of lem-pc-module-bounded-flat-kflat. Boundedness is above, not below, and is zero here. Flatness of R is proved by the two inverse tensor-unit maps rather than inferred from an uncited theorem about free modules. def-weil-derived-tensor gives the K-flat resolution rule; ordinary modules are its specialization to the one-object site with only the maximal covering sieve. def-pc-tensor-complex-sheaves gives the direct-sum total differential. Only the second factor's degree zero survives, so there is one summand, the multiplication differential becomes zero modulo t, and no infinite-totalization claim is needed. Step 3 uses the cohomology definition in def-weil-abstract-derived-category and spells out the reindexing to Tor, defined here by homology of a tensored free resolution. In particular q=0 is included, not obtained from the negative-degree calculation by an invalid endpoint argument.

Step 4 uses the small ringed site actually defined by def-weil-pbc-proetale-site and the sheafification definition in def-weil-pbc-constant-sheaf. The statement of lem-weil-pbc-finite-type-constant-exact explicitly allows every small site and every commutative B and preserves kernels and cokernels. Thus it gives the exactness needed on this site for this R despite its narrower-sounding title. Images are kernels of cokernels, so the kernel-image equalities survive. I did not use lem-weil-pbc-constant-module-section-properties, which has an unnecessary Noetherian hypothesis, nor any finite-coefficient-only inverse-image result.

Step 5 uses def-pur-sheaf-tensor-product, which actually defines the sheaf tensor as sheafification of the sectionwise tensor presheaf, and def-pc-flat-sheaf-modules, which defines flatness by exactness of tensor. The two sectionwise inverse maps commute with restrictions; after sheafification they prove the needed unit identity. This is an elementary calculation, not a missing theorem about constant sheaves preserving derived tensor. It works for the zero ring and empty schemes as well.

Step 6 uses lem-pc-bounded-above-flat-kflat-site, whose statement is on an arbitrary ringed site, not merely a ringed topological space. Its boundedness and flat-term hypotheses have both been checked. def-weil-derived-tensor then identifies the exact K-flat resolution chosen in step 4 as a valid computation. def-pc-tensor-complex-sheaves and def-weil-abstract-derived-category give the one-summand tensor differential and its kernel/image cohomology formula. Multiplication by t is the constant sheafification of the zero map on F; it is not an assumption that F_V is flat.

Step 7 uses precisely the local-injectivity sentence in lem-sf-constant-module-unit-locally-bijective. The covering definition in def-weil-pbc-proetale-site supplies a nonempty cover member when V is nonempty. Constant presheaf restrictions there are identities, so the written contradiction proves nonvanishing. No assertion that ordinary geometric points detect all pro-etale sheaves enters this step.

I checked delivery-errors B–E as mathematical conditions. All objects in the unchanged statement are introduced, no new node hides a proof, and citations.json contains the actual cited statements rather than their proofs or source tags. Every non-elementary use is one of the four explicit general tools above, and elementary steps write out their tensor identities, cohomology quotient or covering contradiction. No entire clause is exported to a new node, and no lemma is proved and then cited circularly. All proof steps are below 2000 characters. For small cases I checked R=0 (every complex and quotient is zero), t=0 (the annihilator hypothesis forces R=0), q=0, V empty (only the cohomology isomorphism is asserted), disconnected nonempty V (the covering contradiction needs no connectedness), R=k[epsilon]/(epsilon^2) and R=Z/ell^2. In the latter two cases the kernels and images are both the principal square-zero ideal as required. Without the annihilator equality the resolution is generally not exact, so it has been retained throughout. No statement correction or source-level mathematical dispute is needed.
