## Files written

- dag/nodes/sec-trace-formula/lem-trf-qcqs-relative-finite-presentation-approximation.json: item, statement unchanged, split into four proof steps.
- dag/nodes/sec-trace-formula/lem-trf-qcqs-arrow-absolute-approximation.json: one new statement-only unsplit lemma, Tag 0GS1; no Mathlib match.
- citations.json: ten entries, one verbatim statement quote per step/cited-node pair.
- searches.jsonl and search-output.json retain the actual search records and responses. Existing sandbox item and prior searches were read before continuing; no previous split or report existed. The copied item matched the live unsplit statement and proof.

New nodes: 1. Mathlib leaves: 0. All writes are in the assigned sandbox. No Lean was written or compiled.

## Attachments

None for the item. Project searches for its exact blueprint tag, 09MV, relative approximation and finite-presentation approximation found AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation in WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:4579. Its hypothesis LocallyOfFiniteType f excludes arbitrary morphisms, so it cannot attach this item. The related NoetherianStageData existence theorem likewise assumes locally finite type and gives an immersion model, rather than the required arbitrary-arrow system. The Mathlib hits Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (AffineTransitionLimit.lean:1232) and exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType descend/equalize maps from a system already supplied: they do not construct the approximation.

WANTED: none.

## What was wrong or incomplete

The imported item had a correct, unsplit statement, no proof and no proof dependencies. It does not require a statement correction. Its source 09MV has the more general quasi-separated-base formulation, whereas this item already assumes a qcqs base, so the preliminary replacement of the base by a qc open is unnecessary here. The project's available finite-type approximation machinery does not cover the arbitrary morphism in the item. The missing content is now isolated as the simultaneous varying-base absolute approximation theorem, not as a new fixed-base approximation theorem that would simply restate the item.

The latest blueprint source was read at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md, together with the latest unit _section.md, the recorded chapter and unit. This item is a deep auxiliary 09NI-neighbourhood dependency of that ancestor, not a new proof of the trace assertion. The source-based approximation route is retained and the existing blueprint ancestry/via chain is preserved.

## Source error

In the proof of Stacks 0GS1, limits.tex after lemma-approximate-morphism, the paragraph testing two triples chooses b'' <= min(b,b') and equalizes maps to S_b''. This does not prove that the preorder of triples, ordered by a >= a' and b >= b', is directed. To obtain a common upper bound one must instead first choose b'' >= b,b', factor X -> S -> S_b'' through a source stage by 01ZC, then enlarge the source stage so its two composites to S_b and S_b' agree with the two prescribed maps by the equality part of 01ZC. The corrected triple dominates both original triples. The statement of 0GS1, used here as a statement-only new node, remains correct. This is a direction error in the source's proof, not a reason to weaken either statement.

## Not duplicates

lem-trf-qcqs-arrow-absolute-approximation vs lemma-nagata-relative-stage-morphism-data-exists: the latter assumes f locally of finite type and supplies a selected finite-stage immersion datum; the new node treats arbitrary f and simultaneously models the whole arrow with both source and target varying.

lem-trf-qcqs-arrow-absolute-approximation vs prop-nagata-noetherian-inverse-system: the existing result approximates one scheme; the new result additionally gives a common directed index and compatible descended arrows for an arbitrary morphism.

lem-trf-qcqs-arrow-absolute-approximation vs lem-weil-pbc-proper-limit-noetherian: the existing result assumes the arrow proper and models proper arrows; the new result imposes no finite-type or properness hypothesis.

lem-trf-qcqs-arrow-absolute-approximation vs lem-trf-qcqs-relative-finite-presentation-approximation: the new node has varying integer-finite-type targets, and does not give a system over the fixed S. The item's proof performs the fixed-target base change, proves finite presentation of its structure maps, and identifies its limit.

Whole-DAG source/tag and concept searches found no node for 0GS1 or lemma-approximate-morphism. Blueprint searches for 0GS1 and relative approximation returned no match; broader approximation/arrow searches were inspected for the Noetherian and proper variants above. Lean source searches similarly found only the stronger-hypothesis finite-type model results. The new id was absent before creation.

## Review by NG

I read the complete proofs of Stacks 09MV and 0GS1 in limits.tex and the finite-presentation arguments 01TX and 02FV in morphisms.tex. For the item I checked that 09MV is exactly the fixed-base construction needed and that the added qcqs-stage clause follows over a qcqs base. For the new node I checked the source statement of 0GS1, with arbitrary f and two varying absolute systems, and noticed the directedness error in its proof described above. That proof repair belongs to the eventual split of this new statement-only node; the report retains the explicit repair argument. This new node is a genuine theorem with extra compatibility data, not an elementary step, a clause of the item, or a relabeling of 09MV.

Step 1 cites only the new arrow-approximation statement. Its statement supplies every datum used: a small nonempty directed poset, finite-type integer stages that are qcqs, both affine transition systems, commuting arrows, and both limiting cones. No local finite-type assumption on f is introduced.

Step 2 uses lem-weil-pbc-finite-type-over-noetherian specifically for Spec Z Noetherian; pqf-lem-lft-fp-locnoeth specifically for local finite presentation of A_i over Spec Z; lem-a1-map-over-base-finite-presentation for h_i locally of finite presentation over the common integer base; and lem-weil-pbc-qcqs-morphism-permanence for its quasi-compactness and quasi-separatedness. I opened and read each statement. The permanence lemma's hypotheses concern the two structural maps over Spec Z, not f. Finite type over Z supplies local finite type of both stages. The target B_i is quasi-separated and the source A_i is qcqs from step 1. Thus finite presentation includes quasi-separatedness and does not mean merely local finite presentation plus quasi-compactness.

Step 3 uses the actual fibre-product definition, the base-change and source-over-qcqs-base clauses of the qcqs permanence node, and the full statement of lem-weil-pbc-limit-fibre-products, including its explicit affine-transition conclusion. I read this latter statement to ensure I was not merely using a comparison appearing in its proof. Its three systems are A_i, B_i and the constant S, whose transitions are identities and hence affine. The structure maps S -> B_i satisfy the required commuting squares. This theorem avoids a second duplicate lemma for affineness of varying-base fibre-product maps. The component formulas explicitly give the identity and composition laws and S-linearity of the transitions.

Step 4 uses the limit clause of that same theorem and the fibre-product universal property, not an uncited general assertion that all limits of schemes exist. The common map from a compatible constant-system cone is justified by nonemptiness and directedness. The limit maps are f and id_S, so the result is Z x_S S, explicitly isomorphic to Z. The argument checks uniqueness on arbitrary test schemes, as the item's last sentence requires; it is not merely a limit in the category over S.

I compared every uses entry against the cited node statement and wrote ten verbatim quotes in citations.json. The proof-dependency list is exactly their union. Both off-unit non-Mathlib tools are declared in split_report.tool_uses with their generic purposes. Definitions and Mathlib leaves are tools already. Each step is under 2000 characters and none hides a separate comparison lemma.

I tested the statements on empty Z, empty S (then necessarily empty Z), an arbitrary affine map Spec B -> Spec A with infinitely many algebra generators, and qcqs nonseparated schemes such as a doubled origin. The varying-base theorem allows empty stages, and the fixed-base construction needs neither nonempty schemes nor separatedness of the absolute stages. No intersection of affine opens is assumed affine. For an already finitely presented morphism the conclusion permits the constant system. The infinite-generator affine example verifies why replacing arbitrary f by the available finite-type Lean theorem would be invalid. The source's directedness typo was corrected in the recorded argument, without changing the theorem statement.

## What remains

The new node is intentionally unsplit: stage 1 here is one level only. Nothing in the item's four-step assembly remains unaccounted for. The maintainer independently reviews this direct delivery. The server dry run completed successfully: OK (not pushed), preflight passed at f3b93cc79c5. The final delivery is run only after that process exited; its pushed commit is reported in the final one-line delivery response.
