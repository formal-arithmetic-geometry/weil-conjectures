## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-kun-filtered-page-localization.json` (repaired statement and split), `dag/nodes/sec-smooth-purity/lem-kun-filtered-page-functor-normalized.json` (one new statement-only node, Mathlib no match), `citations.json`, and this report. The item has eleven proof steps; the new node records the page functor and normalized successor isomorphisms required by the returned C3/C4/E5 finding. There are no new Mathlib leaves.

Attachments: none. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item tag and filtered-page/localization terminology found no declaration stating this item. The upstream master checkout was not treated as proof evidence.

WANTED: none.

The returned version left the successor isomorphisms of the existential page-core witness unspecified. I repaired this by adding `lem-kun-filtered-page-functor-normalized`, recording a choice of the core page functor together with uniquely normalized successor homology isomorphisms, their naturality, and the spectral-sequence successor equation. The item statement now names this recorded package. Steps 1, 9 and 10 use it explicitly; the cone criterion used in Step 3 is now declared in `split_report.tool_uses`. The source place is corrected from the placeholder section name to `section-filtered-complex`, Tag 012K.

Nothing remains unfinished. The full dry run and delivery are performed after this report.

## Blueprint and searches

I read the chapter `sec-smooth-purity`, unit `sk-prop-sf-kunneth-ordinary`, and current `main-20261015` text of `lem-kun-0f0f`. The item's blueprint ancestry is the projection-formula proof paragraph beginning “Both sides of [def-kun-projection-formula-map] are triangulated functors in K”; the new node's `blueprint.from.place` names the same paragraph and its `via` chain includes the repaired item.

Whole-blueprint searches used `tools/blueprint_refs.py search` for `filtered`, `spectral sequence`, `filtered homotopy`, `stationary`, `filtered derived`, `localization`, and normalized successor terms, together with DAG searches for Tags 012K, 012M, 012O, 012W, 05S1, 05S2, homotopy, acyclicity, and universal localization. Existing nodes cover the page core/construction and representative normalized homology, but none states the combined finite page-one functor with fixed normalized successor maps and their naturality. The new node is therefore not a duplicate or a restatement of any one existing node.

For the new node I ran `msearch.py` with LeanFinder, Loogle, grep, and LeanSearch using the exact queries recorded in its `mathlib_searches` field. LeanFinder and LeanSearch returned connected-complex, Dold–Kan, truncation, and ordinary homology declarations; Loogle returned no hit and reported its identifier unknown; grep found no matching Mathlib source. I read the returned signatures and none states the filtered spectral-sequence package. Earlier inherited searches for the item remain in `searches.jsonl`; no search result was invented.

## Not duplicates

`lem-kun-filtered-page-functor-normalized` vs `lem-sp-bounded-filtered-page-core`: the core gives an existential page functor and comparisons but does not fix successor homology isomorphisms or their normalization.

`lem-kun-filtered-page-functor-normalized` vs `lem-sp-bounded-filtered-page-construction`: the construction gives page-one and image comparison data and an exact couple, but asserts no normalized successor-map choice or successor naturality package.

`lem-kun-filtered-page-functor-normalized` vs `lem-sp-filtered-complex-canonical-sequence`: the canonical-sequence node starts at page two for all filtrations and does not provide the finite-filtered page-one/abutment clauses used here.

`lem-kun-filtered-page-functor-normalized` vs `lem-sp-filtered-complex-normalized-homology`: normalized homology concerns one representative differential datum and its quotient comparison; it does not state a functor on finite filtered complexes or its natural successor maps.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-complex-decalage-page-data: the existing definition is a decalage page embedding and normalization equation for r≥2, while the new node fixes a page-one spectral-sequence functor and all successor maps for finite filtrations.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-complex-decalage-tower: the existing definition constructs a mapping-cone spectral object for the decalage tower; it does not state the finite page-one quotient functor or normalized successor compatibility.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-complex-decalage: the existing definition only abbreviates shifted-cycle subcomplexes and inclusions; it contains no spectral-sequence functor or successor isomorphism.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-complex-subquotients: the existing definition gives cycle, boundary and subquotient objects; the new node uses those objects to state a functor and normalized successor maps.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-homology-couple-data: the existing definition gives explicit exact-couple homology terms and maps, not a page-one spectral-sequence functor or successor normalization.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-homology-exact-couple: the existing definition packages the concrete filtered homology exact couple; it does not fix spectral-sequence successor isomorphisms.

lem-kun-filtered-page-functor-normalized vs def-sp-filtered-page-two-model: the existing definition starts at page two and only supplies page/image comparisons, whereas the new node starts at page one and fixes all normalized successor maps.

lem-kun-filtered-page-functor-normalized vs def-sp-map-good-upper-truncation: the existing definition concerns left exact functors and upper truncations of complexes, with no filtered spectral sequence.

lem-kun-filtered-page-functor-normalized vs lem-sp-ce-canonical-truncation-comparison: the existing lemma compares a CE quotient model with truncation spectral sequences and asserts page-two naturality only; it does not provide the finite page-one functor here.

lem-kun-filtered-page-functor-normalized vs lem-sp-ce-filtered-truncation-comparison: the existing lemma is a Grothendieck CE/truncation comparison with page-two models and different hypotheses, not a normalized finite filtered page construction.

lem-kun-filtered-page-functor-normalized vs lem-sp-ce-good-cut-identification: the existing lemma identifies a good-cut total with a truncation and decalage complex under bounded-below CE hypotheses; it does not state successor maps for arbitrary finite filtrations.

lem-kun-filtered-page-functor-normalized vs lem-sp-filtered-cohomology-image-finite: the existing lemma proves only finiteness of the cohomology image filtration degreewise; it does not construct a spectral-sequence functor or normalize successor isomorphisms.

## Statement corrected

The old item statement referred only to “the page functor S of [lem-sp-bounded-filtered-page-core]” and asserted agreement under unspecified successor isomorphisms. The new statement refers to the normalized page functor supplied by `lem-kun-filtered-page-functor-normalized` and explicitly says that adjacent-page agreement is under its normalized successor maps. This is the recorded correction requested by the return; the mathematical localization and stationary-image clauses are unchanged. The only citer is `lem-kun-bounded-tensor-tor-spectral-sequence`, whose page-localization step now uses the repaired compatibility statement.

## Review by Q86

I read Stacks `homology.tex`, Tag 012K (`section-filtered-complex`, including the displayed cycle/boundary formulas, representative differential and successor quotient construction), Tag 012M (`lemma-spectral-sequence-filtered-complex`), Tag 012O (`lemma-spectral-sequence-filtered-complex-functorial`), Tag 012P (`definition-filtration-cohomology-filtered-complex`) and Tag 012W (`lemma-biregular-ss-converges`). I also read `derived.tex` Tags 05S1, 05S2 and 05S3, `categories.tex` Tag 04VK, and the source of the recorded fraction and localization tools. The new node's statement matches the Tag 012K construction: the core comparison data are retained, while the successor map is the unique map carrying a successor-cycle representative to the canonical quotient representative, and the maps are natural for filtered morphisms. Its hypotheses are finite filtration and no cochain-degree bound, exactly as used by the item.

Step 1 now cites the new normalized page-functor statement and `def-sp-filtered-complex-subquotients`. The new statement supplies the page-one/image/representative clauses and fixes the successor maps; the subquotient definition supplies the two containments defining φ. I checked the containments for every t≥1, including t=1. Step 2 uses the filtered-homotopy definition, ordinary cohomology, the core's page-one naturality, and the spectral-sequence successor equation; its cycle calculation is elementary. Step 3 uses the exact cone criterion `lem-pur-quasi-iso-cone-acyclic`, the degreewise filtered-acyclic criterion, the finite filtration definition, and the cone construction; the cone filtration and every step restriction have common finite bounds in all cochain degrees. Step 4 uses the core page-one comparison and the spectral-sequence morphism equation to invert each page map. Step 5 checks the image filtration square and the lift through the step cohomology isomorphism from Step 3. Step 6 uses the localization universal property, ordinary derived cohomology factorization, filtered homotopy definition, and core naturality; it verifies both functor and natural-transformation hypotheses.

Steps 7 and 8 use the filtration/subquotient and cohomology definitions plus the core image comparison. I checked both kernels explicitly: the image in `H^n(U/F^(a+1)U)` has kernel `D_a+B_a`, and the inverse image of `I_n^{a+1}` in `C_a` is the same `D_a+B_a`; hence both stationary isomorphisms use the same cycle representative. Step 9 cites the new normalized page-functor statement and the subquotient formulas. For the bound `t≥max(1,h-a,a-ell+1)`, outgoing targets lie at or beyond the zero step and incoming sources below the whole step. The normalized successor equation then carries each stationary cycle representative to the identical representative on the adjacent page, so the two comparisons agree. Step 10 cites the right-fraction calculus, the opposite-category fraction representation, localization, the spectral-sequence definition, and the new normalized successor statement. I checked the intermediate roof object is only required to be stationary at a larger `t'`; Step 9 applies there, the W-roof map is invertible by Steps 3–5, and the normalized endpoint successor equations descend the square to the requested `t`. Step 11 checks zero complexes, zero rings, repeated filtration steps, indices outside the filtration range, and arbitrary positive and negative cochain degrees.

The return's C3/C4/E5 issue is repaired by the new node and the statement correction; the old placeholder source label is corrected to Tag 012K; and `lem-pur-quasi-iso-cone-acyclic` is declared under `split_report.tool_uses` for Step 3. Every citation quote in `citations.json` is verbatim from its node, including the new node's quote in Steps 1, 9 and 10. All proof steps are below 2000 characters (maximum 1373), and the added node is intentionally statement-only rather than a hidden reproof of the item.
