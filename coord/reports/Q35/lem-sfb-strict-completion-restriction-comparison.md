## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-strict-completion-restriction-comparison.json`: statement, split; seven proof steps, no Mathlib match.
- `citations.json`: sixteen verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: actual msearch results for the item, retained unchanged.

## New nodes

None; zero Mathlib leaves. The scalar-cone and Roos coordinate calculations are elementary steps from cited existing statements, not new lemma nodes.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint docstring tag and by strict completion, section action, completion/restriction and Roos terminology. The exact tag has no declaration; the nearby completion/restriction files concern coherent formal modules and adic scheme completion, rather than the pro-etale coefficient categories here. The general derived-limit files do not state all the item's clauses. No sorry declaration was treated as a finished proof.

## Wanted

None. All sources used are present in the read clone.

## What changed and what was wrong

The live node was unsplit, with no proof. Its statement, source, creation metadata and original five search records are retained. There was no previous sandbox split or report to recover. I added the seven-step proof, its exact proof dependency union, an agent proof-origin record, and the split report with blueprint mapping and generic tool uses. The statement is mathematically consistent; no statement correction or STATEMENT-DISPUTED finding was necessary.

The tempting narrower dependencies `det-sf-open-closed-pullback-limits`, `lem-formal-closed-pullback-derived-products`, and `lem-sfb-integral-pullback-strict-roos-normalization` do not suffice: the first assumes qcqs and a quasi-compact complement, the second assumes separated finite type over a field, and the third assumes characteristic different from ell. I read their statements and instead use the already existing arbitrary-scheme immersion-limit node. This avoids adding those hypotheses to the item.

## Blueprint and duplicate searches

I read the chapter `sec-six-functors-basics`, the inherited unit `sk-prop-sf-comp-coherence`, and the nearest blueprint ancestor `det-sf-comp-coherence-cocycle`. The ancestor's refinement calculation uses the closed-complement proper-base-change calculation; this item is its finite-model-completeness support lemma. The explicit locality source is `main-20261015/.../sk-def-localizing-closure-ctf-equals-bc.proof.md`, Locality, and the explicit completion model is `main-20261015/.../sk-lem-pe-derived-nakayama-first-reduction.proof.md`, Cones. Both were read in full. No chapter/unit text was changed.

`tools/blueprint_refs.py ancestor` gave `det-sf-comp-coherence-cocycle`. Searches for `completion restriction`, `inverse image limits`, `strict completion`, `Roos`, and `section-action`, together with whole-DAG keyword searches, found no blueprint node stating this full augmented comparison. The Roos search found narrower finite-type formal-support statements and general derived-limit statements. Whole-DAG searches for `09AA`, section-action, and limit preservation found the existing arbitrary-scheme `lem-weil-pbc-proetale-immersion-limit-preservation`; it is cited rather than duplicated. The inherited blueprint origin is preserved and `same_as` is empty.

## Mathlib searches

The five original item searches were preserved as received. I ran five additional searches with msearch: two LeanFinder phrasings (exact product-preserving functors and scalar-cone/Roos augmentations; internal/section module equivalence and completion), LeanSearch for locally closed pro-etale inverse image and completion, Loogle `"DerivedComplete"`, and grep `proetale.*complet|complet.*proetale|Roos|sectionAction`. The logged service responses were all successful. LeanFinder returned scalar `AdicCompletion.map_exact`, scalar transition maps, a light-condensed AB4-star instance, free-module Hom and module-sheafification adjunctions; LeanSearch returned ordinary ringed-space open-immersion identities. Loogle and grep returned no hits. These hits do not state the pro-etale augmented derived-completion comparison; even the scalar exactness theorem assumes a Noetherian ring and finite modules and says nothing about this strict derived tower. Every newly recorded query equals a query in the unedited msearch log. No new nodes require their own search records.

## Not duplicates

No new nodes; there are no new/existing same-tag pairs.

## Review by Q35

I checked delivery-errors B through E with the statements of all thirteen cited nodes open. I read Stacks `proetale.tex`, Tag 09AA, `lemma-closed-immersion`: its first clause commutes with limits for a closed immersion of arbitrary schemes, without qcqs or retrocompact-complement hypotheses. I also read `sites.tex`, Tag 00Y0, `definition-localize` and its following restriction formula; `sites-modules.tex`, Tag 03DB, `lemma-limits-colimits` and its sectionwise-limit proof, Tag 03EK, `section-tensor-product`, Tag 0GMW, `lemma-sheafification-tensor`, and Section 03DH with Tag 03DJ, `lemma-extension-by-zero-exact`; `sites-cohomology.tex`, Tags 07A4, `lemma-pullback-tensor-product`, and 0G7E, `lemma-pullback-K-flat`; and `derived.tex`, Tags 014E, `definition-cone`, and 08TC, `definition-derived-limit`. The last source explicitly warns that a derived-limit isomorphism alone is nonunique. Consequently the proof constructs its chain map and its augmentation before localizing. The comparison with internal section action is an agent argument supported by the existing normalized comparison nodes, not attributed as a verbatim Stacks theorem.

Step 1 uses `lem-pe-internal-section-tensor-comparison` for exactness, unchanged underlying sheaves/maps, the pure-tensor formula and K-flat total tensor comparison. Its statement actually includes those clauses. `sk-def-sfb-constructible` supplies the finite matrix characterization with entries in the scalar ring, so preserving this model requires only preserving that matrix and its cokernel. `lem-sfb-internal-module-inverse-image-comparison` supplies the normalized compatibility on local-model charts; its statement says the underlying maps are identities. Cohomology is the kernel/image calculation for an exact functor. The product comparison is obtained directly by applying full faithfulness and the inverse equivalence to the defining Hom/product bijection, not assumed from the internal-Hom conclusion of another node.

Step 2 uses `sk-def-sfb-coefficient-morphisms`, whose statement makes alpha the component of a natural coefficient isomorphism and says it is a ring-object isomorphism. Naturality applies to the specified uniformizer multiplication and quotient maps. The internal/section inverse-image node says precisely that the action comparison has identity underlying sheaf map and intertwines the differential. I did not infer a ring-action normalization from a mere categorical equivalence.

Step 3 applies `lem-weil-pbc-proetale-immersion-limit-preservation` with R the actual section-ring coefficient sheaf and c the coefficient isomorphism of Step 2; its statement includes exactness and all small limits after transport along an isomorphism. The isomorphism hypothesis is satisfied; the argument makes no assertion about arbitrary scalar extension. For a site object, `lem-weil-proetale-weakly-etale-localization` supplies the slice identification, `lem-pur-site-restriction-module-adjunction-exact` explicitly supplies exact module restriction, and `lem-weil-pbc-module-sheaves-limits-sectionwise` explicitly supplies products with projections evaluated sectionwise. The elementary displayed evaluation proves product preservation. All rings, sites and products stay in the fixed coefficient universe. The argument composes these particular functors, not arbitrary inverse images presumed to preserve products.

Step 4 uses the tensor and K-flat clauses of the internal/section tensor comparison and the unbounded bifunctorial tensor/pullback theorem `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Its statement allows arbitrary small ringed topoi and supplies K-flat preservation. `lem-sf-exact-functor-derived-triangulated` supplies termwise localization of exact functors. The coefficient map here is an isomorphism, so no higher derived pullback of k_n remains. The transition follows by naturality in the coefficient morphism; the unit square is verified on m tensor 1. Scalar restriction forgets only action, so it retains this same normalized map.

Step 5 cites `lem-pe-principal-reduction-cone-calculus`, whose statement explicitly fixes the transition (x,y) -> (x,pi y), the inclusion m -> (m,0), their derived normalization, and the cone convention. The calculation uses only additive biproduct preservation and transported pi-action established earlier. I checked the differential, transition and inclusion coordinates, including signs. This is an elementary substitution, not a new node restating the item's reduction clause.

Step 6 cites `lem-pe-roos-cone-calculus`, whose statement explicitly gives the differential (dv,-du-(1-T)v), the product projections defining T, and the zero-second-coordinate augmentation. Projecting the proposed product comparison to coordinate n gives its equality with T, hence 1-T; the same beta in both cone coordinates then gives the chain isomorphism. Its value on the actual augmentation is written out. No nonunique triangle-filling assertion is used to select the unit. This is the other elementary calculation.

Step 7 cites `lem-pe-completion-triangle-comparison`, whose statement identifies precisely QH(D(M)) and the displayed augmentation with the specified completion unit. The exact-functor localization node permits termwise E and h-star to descend. All earlier maps are natural on complexes; exactness preserves quasi-isomorphisms, so their localized naturality is independent of representative. Composite compatibility is checked using the same projections and the same two coordinates. These statements are generic tools below the compactification unit; their specific roles and why the unit supplies no substitute are declared in `split_report.tool_uses` for the maintainer's route review.

I tested the identity and empty composite, the empty source scheme, a single closed immersion with non-quasi-compact complement, a site object that is not an open immersion, and arbitrary unbounded complexes. None require finiteness, characteristic, invertibility or constructibility. For the sign/transition check, at n=1 and for the module B/pi, pi acts as zero: the transition is identity on the first summand and zero on the second, while the augmentation still lands in the first. This confirms the argument does not accidentally replace the derived reduction by the underived quotient. The product comparison also sends zero to zero in both cone coordinates. There are no newly asserted statements requiring separate edge-case tests.

All seven steps are below 2000 characters. The two coordinate calculations are elementary consequences of the cited models and earlier functor properties; every other non-elementary fact is an existing cited node. Each cited statement was checked against the use, and `citations.json` uses literal substrings of those statements. I corrected the initial temptation to use the finite-type strict-Roos normalization by replacing it with the general scalar-cone and Roos argument; the live item statement did not change. No work is left incomplete at the stage-1 mathematical level.

## Validation

The server dry run returned `OK (not pushed)` with preflight passed at `894a59834bd`. The first attempt rejected one quotation shorter than 40 characters; I expanded it to the complete exactness/adjunction clause and the second attempt passed. The statement is byte-for-byte unchanged, the proof dependency list equals the union of step citations, all sixteen quotes are literal statement substrings, and no new DAG node was created. No Lean source was written and no compiler, Lake or build command was run. A final dry run validates this report update before pushing.
