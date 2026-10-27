# Stage-1 report

1. Files written: dag/nodes/sec-trace-formula/lem-trf-log-condition-fine-chart-locality.json — statement, split; no Mathlib match. No new nodes and no new Mathlib leaves. citations.json contains verbatim statements for every step citation; searches.jsonl records the actual new searches. Only the sandbox was written.
2. Attachments: none. Searches of lean/WeilConjectures for the blueprint tag, LogStructure, prelog, logarithmic, fine log and fine saturated found no declaration stating this item. Logarithmic-derivative hits concern unrelated power series.
3. WANTED: none.
4. The live item was unsplit with no proof, and there was no previous sandbox split or report. Its statement is retained verbatim. The given log axiom is a sheaf isomorphism on the whole restricted slice, not just a bijection of sections on T_a; this stronger hypothesis is essential when checking overlaps. The current latest ancestor blueprint proof discusses contracting correspondences, not logarithmic structures. The inherited from.place refers to earlier split genealogy, which is preserved and explicitly explained in split_report.blueprint. No unit route was replaced.
5. Unfinished mathematics: none for this item.

## Sources and searches

Read ILO, Travaux de Gabber, Expose VI 1.1, printed p. 69 (PDF page 75), and Expose VIII 3.3.4(ii), 3.3.8, printed p. 107 (PDF page 113). VI 1.1 defines fine and fs by etale-local charts; VIII supplies the strict-etale-chart convention and descent context. These paragraphs do not spell out the log-unit argument. That argument is written out from the sheaf equalizer, so proof_origin.by is agent. Read Stacks sites.tex, definition-sheaf-sets (00VM), and topologies.tex, lemma-etale (0217), especially parts (2) and (3). No SGA source was used.

Mathlib searches were run using msearch.py: LeanSearch, two differently phrased LeanFinder searches, Loogle and grep in AlgebraicGeometry. The services answered. The first phrasing returned ordinary etale topology and locality. The second phrasing returned submonoid presheaves, units on ringed spaces, and sheaf modules; none states the logarithmic assertion. Loogle has no LogStructure identifier, and the grep found no logarithmic chart definition. The existing item's older searches are retained as history and new Q63 searches appended. The statement of a generic section-gluing theorem alone would not be an exact attachment or Mathlib match for all clauses of this item.

DAG and blueprint searches included log structure, fine, logarithmic and sheaf isomorphism; the broad fine search was inspected for logarithmic content, and direct searches of latest blueprint found no matching logarithmic node. Existing cover-composition and cover-base-change nodes supply the two nontrivial geometric facts, without creating duplicates. The open-cover module-isomorphism node is not used: it has different objects and only Zariski covers.

## Review by Q63

I read every cited statement, including the full equalizer definition in def-weil-pbc-etale-sheaf-of-sets, the sectionwise restriction/relocalization formulas in def-pur-localized-ringed-site, and the explicit geometric-point pushout chart formula and fs condition in def-trf-fs-log-blowup. I compared them with the item rather than borrowing their proofs.

Step 1 uses lem-weil-pbc-etale-covering-base-change exactly for W times_T T_a covering W; its hypothesis permits any scheme morphism, hence W to T. The localized-site definition says evaluation is the same section set. The assumed local log-unit isomorphism therefore applies to all W_a and their overlaps, not only the covering objects themselves. No geometric-stalk conservativity or unstated local-isomorphism theorem is used.

Step 2 uses the equalizer axiom for the given sheaf M. Local injectivity makes the uniquely lifted sections agree on double overlaps; existence and uniqueness then glue them. The structure sheaf is a ring sheaf in the given ringed-site/log setup, so its separatedness verifies alpha(m)=u. This also ensures m belongs to the inverse image of units. Restriction and multiplication of these unique lifts give a natural monoid inverse, proving an isomorphism of monoid sheaves, not merely objectwise surjectivity. The cited log definition identifies precisely this axiom. This is an explicit equalizer application, not an appeal to a hidden sheaf-descent lemma.

Step 3 uses lem-weil-pbc-etale-covering-composition, whose statement gives both etaleness and joint surjectivity with arbitrary index sets. Both covering hypotheses are exactly those supplied by the item. The relocalization statement gives equality of the restricted sections and structure maps; hence the chart condition is unchanged. The definition's local chart condition concludes fs in the saturated case; its finite-generation/integrality part is the fine condition spelled out in the item's hypothesis and in ILO VI 1.1. This asserts no global chart and performs no descent of a chart monoid.

Step 4 uses the actual chart definition: an isomorphism over O fixes the prelog map beta, so the source pushout is identical and the target map is literally composed with e on stalks. Its inverse is induced by the already given inverse e^{-1}. This proves chart transport directly, without assuming logification commutes with an unexplained functor. The chart monoid is not changed.

I checked the identity covering, repeated covering indices and an empty scheme (the sheaf equalizer for the empty cover gives singleton sections). I checked the trivial unit log structure and a chart with fine integral but nonsaturated monoid generated by 2 and 3: the fine conclusion holds but the proof does not claim fs without the extra hypothesis. Infinite covers need no finite extraction. Local Noetherianity is retained and no stronger finiteness, separation or normality is introduced. All proof steps are under 2000 characters and are elementary section arguments or specializations of the two existing Mathlib leaves; no new lemma is hidden. The proof-dependency list is the union of the step uses and citations.json copies only actual cited statements. No statement dispute was found.

## Not duplicates

No new nodes were created.
