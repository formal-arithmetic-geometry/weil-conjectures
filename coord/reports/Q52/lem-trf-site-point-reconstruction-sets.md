# Q52 stage-1 delivery: lem-trf-site-point-reconstruction-sets

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-site-point-reconstruction-sets.json`: item, statement unchanged, split into four proof steps; no new nodes.
- `citations.json`: verbatim statement quotations for every cited node in every step.
- `searches.jsonl`: reused the logged Mathlib searches from the earlier read of this item; the repository node already records their results and no Mathlib declaration matches the reconstruction theorem.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, blueprint tag, and the site-point/reconstruction terminology. No sorry-free project declaration states this item exactly.

## WANTED

None. The Stacks sources used below are present in `literature/stacks-project/sites.tex`.

## Corrections and route

The imported statement is mathematically the set-valued reconstruction in Stacks Tags 00YA, 00YB, and 00YC, and I kept it verbatim. The existing `lem-trf-site-point-fibre` node is a constant-coefficient module theorem: it does not state the arbitrary sheaf-of-sets comparison or cover-surjectivity, so it is not an attachment or a one-line specialization. The proof therefore remains a direct set-valued split with no new support node.

## Not duplicates

`lem-trf-site-point-reconstruction-sets` vs `lem-trf-site-point-fibre`: the existing node requires a constant ring and reconstructs module inverse images (plus module exactness), whereas this item reconstructs every sheaf of sets and proves joint surjectivity for site covers; the former does not specialize to the latter in one line.

## What remains

Nothing remains for this split. It introduces no `sorry`, no Lean code, and no statement dispute.

## Review by Q52

I read `literature/stacks-project/sites.tex` at Tags 00YA (lemma-point-site-topos, especially part (2) and its canonical comparison), 00YB (lemma-neighbourhoods-directed), 00YC (proposition-point-limits), 00Y6 (points-recover), and 00Y7 (adjoint-point-push-stalk). For the repair I additionally read 00WN (lemma-mono-epi-sheaves, whose proof is omitted) and 00WT (lemma-covering-surjective-after-sheafification); the repaired text supplies the required cancellation direction itself from the cited sheaf axiom. I also read the fixed `sec-trace-formula` chapter, unit `sk-i-curve-zero`, the item’s imported blueprint ancestry, and the cited DAG statements in full.

Step 1 uses `lem-weil-pbc-sheafification-sets-exact` for finite-limit preservation by sheafification, `def-trf-geometric-morphism` for finite-limit preservation by (p^{-1}), `def-weil-size-convention` for the small skeleton and universe, and `def-weil-pbc-category-colimit` for the colimit/cofiltered indexing conventions. I checked that the terminal object, binary product, and equalizer constructions give the three cofilteredness conditions and that the object and arrow sets stay in the chosen universe.

Step 2 now supplies the missing cancellation argument in full. I reopened `lem-weil-pbc-site-sheafification-sections-local`: its statement really gives representatives of each section of the sheafification of $h_U$ on a covering, with no subcanonical-site assumption. In `def-weil-pbc-sites-and-cohomology` I checked both pullback/composition of coverings and the equalizer axiom for sheaves of sets. Pulling the original cover back to each representative gives lifts through the appropriate $h_{U_i}^{\#}$. For any two maps out of $h_U^{\#}$ agreeing on those sheaves, naturality makes their values agree on the refined cover; injectivity in the equalizer axiom makes their values equal globally. This proves joint epimorphy instead of invoking an unstated criterion. The adjunction stated in `def-trf-geometric-morphism`, natural in its sheaf variable, turns this cancellation into cancellation for maps from $u(U)$ to every set. The characteristic function of any missed point contradicts that cancellation, proving joint surjectivity directly. No assertion about effective epimorphisms, coproduct preservation, or coequalizer presentations is left to justify.

Step 3 uses the sheafification adjunction (`def-weil-pbc-sheafification`), the natural Yoneda bijection (`lem-galois-yoneda-hom-bijection`), and the geometric-morphism adjunction (`def-trf-geometric-morphism`) to identify ((p_*E)(U)) with (operatorname{Map}(u(U),E)). I checked naturality in (U) is the stated precomposition action.

Step 4 uses the colimit universal property (`def-weil-pbc-category-colimit`), the Yoneda naturality statement, and the same adjunctions to curry compatible families over pointed objects into maps (F\to p_*E). The resulting natural bijection of maps into every set identifies the colimit with (p^{-1}F); tracing the adjunct gives precisely (s\mapsto p^{-1}(s)(a)), and the formula is natural in (F). Every citation in `citations.json` is a verbatim substring of its node statement. I checked the empty and terminal cases, parallel-arrow equalization, and a one-object site as small sanity cases. No step exceeds 2000 characters, and no source route uses SGA.

## Returned delivery repair — C1

The returned head was `e959e25a83`; the retained sandbox contained its four-step split and searches. The current repository still has the same item statement, source, blueprint ancestry, chapter, unit, and search records, but no accepted proof. I retained the existing work and first ran the required unchanged dry run, which passed at `7cb28548a1`. That mechanical success did not resolve the reviewer's mathematical objection.

C1 is repaired in step 2 by the explicit cancellation proof and adjunction argument described above. This is a proof from the cited local-representative theorem and the definitions, not a new lemma that restates a clause of the item. Accordingly there are zero new nodes and no new Mathlib claims or searches; all prior search records and results are retained. I also replaced the step-2 quotation of the site node, formerly only its opening definition, with its actual covering axioms and sheaf equalizer axiom.

I rechecked B--E with the item, sources and cited statements open: B has no new nodes to audit; C has exact quotations for every cited statement and an explicit argument for the formerly uncited inference; D keeps the reconstruction argument in the item; E uses only finite limits, smallness and a geometric-morphism datum, with no assumption that representables are sheaves or that a cover is nonempty. For an empty covering, the sheaf equalizer axiom forces a singleton set of sections, so cancellation still holds and the characteristic-function argument forces $u(U)$ empty. For an identity covering, the family already has an identity map. Multiple local representatives require no chosen compatible lifts: only equality of the two images is descended. The proof steps remain below 2000 characters. The required final dry run and push will verify the repaired delivery on current server state.
