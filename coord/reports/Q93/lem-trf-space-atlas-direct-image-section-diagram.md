# Q93 stage-1 report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-space-atlas-direct-image-section-diagram.json: statement, split in six steps; no exact Mathlib match.
- citations.json: verbatim statement quotations for every proof citation.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The pre-existing searches.jsonl is retained and all seven records are appended verbatim to the item's search history with verdicts.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, enlarged etale and atlas direct-image terminology and AlgebraicSpace, and inspected the scheme-sites hits. No project declaration states this algebraic-space module diagram with all its normalized chart projections. Nothing was compiled or written in Lean.

## WANTED

None. All sources used are present in literature/stacks-project.

## Corrections and source limits

The item was statement-only. Its statement, statement dependencies and ancestry are unchanged. Its proof and proof dependencies now distinguish the limiting-cone comparison, tensor-unit normalization, explicit fibre-product maps and naturality. No claim of an exact Mathlib match was inferred from the Zariski-scheme analogues.

Read the latest blueprint's chapter and sk-i-curve-zero unit and lem-trf-local-term-locality statement/proof, together with the DAG chapter/unit records. The current ancestor concerns contracting local terms; this node is a historical helper in the existing polarized-descent chain. Its retained ancestry records the 03M9/03M8 input. This delivery neither replaces the unit route nor creates a new trace-formula input.

Tag 03M8's proof writes a displayed Cech product over X; for this purpose the intended product is over V times_Y X. This item's section diagram does not assert that displayed Cech identity, so no disputed statement or changed hypothesis results here. Our fibre-product identities in steps 4 and 5 instead give both projections explicitly.

## Unfinished work

None for this one-level split. The independent existing dependencies remain separate tasks. No new tasks were manufactured from the three clauses of the item.

## Not duplicates

No new nodes. Reused lem-trf-space-chart-limit-enlarged-sections for the projection-normalized module limit (rather than restating it); reused lem-trf-space-chart-adjunction-tensor-realization for unit-preserving tensor transport and composition (rather than creating a unit-normalization lemma); reused the existing enlarged site and etale permanence statements. A tag search for 03M8 and the whole-blueprint searches for 03M8 and atlas-direct-image found no additional blueprint statement of this item. The direct-image keyword search was broader and its hits were read as potential candidates, not treated as matches.

## Review by Q93

I read Stacks spaces-morphisms.tex Tag 03M8 (lemma-compute-pushforward), including its extension-to-enlarged-site and restriction-arrow proof; spaces-properties.tex Tags 03LP (lemma-etale-morphism-topoi), 03G8 (lemma-morphism-ringed-topoi), 03LV (lemma-etale-exact-pullback), and 03LW (equation-restrict-modules); and sites-modules.tex Tag 03D7 (lemma-adjoint-pullback-pushforward-modules). These give the source route, while the existing DAG comparison and tensor-realization statements supply the already separated non-elementary facts. I also read Sites Tag 03CE to check that localization really has the stated section formula, not an arbitrary abstract adjoint. There are no new-node sources to review.

For step 1 I opened the statements of lem-trf-space-fibre-products-etale-covers, lem-trf-space-chartwise-etale-permanence, and lem-trf-space-enlarged-etale-ringed-site-model. The first gives representability of R as a scheme, the second gives base change and composition of etale maps, and the third gives precisely the site and structure-ring localization identifications. The hypotheses are etaleness of p and V to Y, not surjectivity, affineness, quasi-compactness or representability of f.

For step 2 I read the whole statement of lem-trf-space-chart-adjunction-tensor-realization. Its etale specialization identifies the specified tensor left adjoint and its unit with restriction using c tensor m to cm, and its general composition clause gives the iterated tensor multiplication. This verifies the common normalization of both pullbacks to R; no unmentioned descent isomorphism is used.

For step 3 I read lem-trf-space-chart-limit-enlarged-sections and def-trf-space-etale-module-functors. The former explicitly states the limiting cone, all its chart projections, naturality and a small vertex even for a larger chart category. Thus it applies to f, a and b without a hidden small-index existence assumption. The latter is the actual specified direct-image limit definition. The two restricted extensions furnished in step 2 identify the latter two vertices with sections of the same extended F.

For step 4 the two cited statements provide unit normalization and detection/evaluation on every chart, not just a bare existence of pullback isomorphisms. On a chart the unit is 1 tensor the restricted section and multiplication sends it to that section. Therefore the composite map f_* eta followed by composition has the asserted restriction component. I wrote the isomorphism W times_X U to Z and its inverse explicitly so that the arrow's direction and projection normalization can be checked.

For steps 4 and 5 I also opened lem-trf-space-enlarged-ringed-composition-localization: it explicitly gives the projection-preserving direct-image composition isomorphism and its ring-map compatibility for normalized rings. The enlarged model fixed in step 1 supplies those normalized rings and morphisms. This reference makes the composition comparison used after each unit explicit.

For step 5 I checked the same cited normalization for each p_i. The explicit maps from Z times_U R to Q use p_i, so the two arrows really are the two requested face restrictions, with the common target fixed by step 2. This is a repeated application of the same calculation, not a new lemma restating the item.

For step 6 I reread the naturality and scalar clauses of lem-trf-space-chart-limit-enlarged-sections and the semilinearity and morphism clauses of def-weil-sheaf-of-modules-category. Every square reduces to composition of the displayed projection maps. Since the maps to V coincide, semilinear restriction is linear over O_Y(V). This step is elementary after the cited formulas; the other steps are marked non-elementary. No step exceeds 2000 characters.

I tested p equal to the identity, the empty etale source, a non-surjective open immersion, F equal to zero, and an arbitrary nonrepresentable f. Identity gives identity restrictions, empty gives zero section modules, and an open immersion uses only the same restriction unit. None requires an atlas to cover. I checked that every cited statement gives exactly the fact used, that citations.json contains actual verbatim statement text, that every proof dependency occurs in a step, and that none of these existing dependency closures uses this item. There are no off-unit theorem tools and no SGA citations. The B--E checklist therefore adds no statement-only node: the remaining tensor multiplication and fibre-product projection computations are explicit elementary calculations inside the steps.

The interrupted searches were not rerun. I read their logged hits and the corresponding Mathlib source: SheafOfModules.pushforward and its overFunctor/overPullback constructions (Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean), the pullback unit helpers (Sheaf/PullbackFree.lean), and AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj at Modules/Sheaf.lean:170 and restrictAdjunction_unit_app_app at line 442. Those last formulas concern scheme Zariski opens. The abstract sheaf functors do not state the normalized algebraic-space chart equivalence. Thus these are useful ingredients, not exact or one-line matches for this item. The search log contains both semantic phrasings, Loogle and grep; successful services are not recorded as unavailable or vice versa.

The initial dry run passed at e940ed5447e. I then made the composition citation explicit in steps 4 and 5 and updated quotations; the final dry run checks that strengthened version.
