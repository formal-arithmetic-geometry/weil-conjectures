# Repair report: lem-trf-etale-flattening-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-flattening-descent.json`: unchanged statement; five-step assembly, 2665 proof-text characters.
- `dag/nodes/sec-trace-formula/lem-trf-etale-flatification-affine-refinement.json`: statement, unsplit, no Mathlib match; empty proof and proof_deps.
- `dag/nodes/sec-trace-formula/lem-trf-etale-flatification-blowup-stability.json`: statement, unsplit, no Mathlib match; empty proof and proof_deps.
- `dag/nodes/sec-trace-formula/lem-trf-factorized-centres-product-transform.json`: statement, unsplit, no Mathlib match; empty proof and proof_deps.
- `dag/nodes/sec-trace-formula/lem-trf-module-flatification-zariski-gluing.json`: statement, unsplit, no Mathlib match; empty proof and proof_deps.
- `citations.json`: verbatim full-statement quotations for every citation in every parent step.
- `searches.jsonl`, `research/*`: actual searches, full responses, the returned node, preserved earlier reports and sandbox-only preparation scripts.

## Attachments

None. The project declaration in `lean/Sheaf/TraceFormula/EtaleFlatteningDescent.lean` has `sorry` and cannot finish the item. Searches of `lean/WeilConjectures/` for the blueprint tag and etale/flattening/flatification concepts find no exact finished declaration. The existing blowup results concern the generic interfaces reused here, not these four combined module assertions. No Lean was written or compiled.

## WANTED

None. All mathematical sources needed for this repair are in the Stacks TeX checkout.

## Landing-refusal repair (2026-10-23)

The present return again reports the side-completion promotion refusal, not a mathematical rejection. The shared return entry now names head `056c32f54ce`. I retained all five sandbox node files, earlier reports, the full ten-step argument, citations and logged search responses. As required for an existing split, I first ran the unmodified dry run to completion: it exited successfully with `OK (not pushed)` at `6aaa2530700`. The delivery tool prepares its commit on the current server DAG; no git command was run in the shared read clone.

I compared every existing statement and its source/status against `research/rebase-current-citations-retry.json`; all nineteen existing interfaces are unchanged. I nevertheless re-read every statement used by the assembly, and verified the 22 citation quotations and exact step/node coverage. The new dated snapshot is `research/rebase-current-citations-20261023.json`. The current item still has the original ten-step proof, while the four statement-only children remain absent from the current shared DAG. Its statement and statement dependencies are identical to this delivery, and its released stage-1 repair note explicitly orders this four-way type of re-split despite the old passing review.

A concrete correction was necessary in the retained assembly: step 4 wrote `X times_{S_1} B_alpha`, although the original X has only a morphism to S. Step 1 now explicitly defines `X_1 = X times_S S_1`, step 3 explicitly transforms F_1, and step 4 uses `X_1 times_{S_1} B_alpha`. Thus every displayed fibre product has the stated structure maps. This is a proof-notation repair, with no change to the theorem or child statements; the argument, source and search questions are unchanged. This repair is not an unchanged re-push.

I re-read Stacks 0814 (`flat.tex`, `lemma-flatten-module-etale-localize`), 0813 (`lemma-push-ideal`) and 080Y (`remark-successive-blowups`), and Divisors 0805, 080A, 080F, 080I, 080M and 080N. I checked the refined bases are qcqs before stability is applied, the Cartier generator is a nonzerodivisor before the stronger refinement clause is applied, and both the base and source covers survive refinement and base change. The product node supplies ordinary pullback of a flat strict transform over the intermediate base; step 4 uses flat local-ring transitivity and the source-cover node to descend to B_alpha. The gluing clause extends the ideals and compares the actual quotient modules; calculus then identifies the composite transform over S. Empty schemes, unit ideals, one-member covers and U=S still satisfy these same interfaces. No step exceeds 2000 characters and the full assembly remains below 3000.

I read the saved search responses, including the second phrasings: affine-refinement and etale-locus results do not provide ideal factorization, general flatness and localization results do not compare blowup transforms, and scheme-flat descent does not extend centres and glue module flatifications. The unchanged four child statements therefore retain their logged no-match verdicts and remain unsplit, with empty proof lists. No new node or search record was invented. The current project-source search again finds no completed exact attachment, and the Sheaf theorem still has sorry. No Lean was written and no compiler was run.

## Resumed rebase review (2026-10-22)

The interrupted initial dry run completed successfully: its durable `.stage1-ready.json` receipt names `d6de6f843a7`, and the delivery process had exited before this retry. I did not overlap delivery commands. The current shared return entry names head `7c1a2884907` and repeats the side-completion promotion refusal; the prior sandbox delivery log names `9a819752b8f`. Those records and the earlier rebase report below are retained, rather than treating the interruption as loss of work. The current read-clone item and the saved returned item both still have the 9160-character ten-step proof, whereas this delivery retains four separate statement-only children and a short assembly. The delivery tool builds on freshly fetched current `origin/sheaf-dag` and preserves maintainer-owned metadata.

I re-read every existing statement cited by the assembly and compared it to `research/rebase-current-citations.json`: none changed. All 22 citation quotes still appear verbatim, with exact coverage of the five steps. The refreshed statement audit is `research/rebase-current-citations-retry.json`. I also re-read Stacks 0814, 0813 and 080Y and the relevant Divisors comparisons (0805, 080A, 080F, 080I, 080M, 080N), the actual helper statements, and the retained search responses. No statement or search question changed, so the logged Mathlib searches are reused. No completed matching declaration was found under the project source; the existing Sheaf theorem remains sorried.

The additional concrete repair is in assembly step 1. Its old wording could suggest that the original S_i were quasi-separated merely because e_i is quasi-compact etale. The first clause of the refinement node instead supplies finite affine charts W_r and their inverse-image source schemes Y_r, with both covers and the local flatifications retained. The proof now explicitly replaces and relabels those diagrams before applying blowup stability, whose hypothesis really does require qcqs S_i. The theorem statement and all dependency interfaces are unchanged. Step 2 then applies the stronger refinement clause only after the Cartier-boundary reduction supplies a nonzerodivisor; Step 3 uses exactly its centre factorization; Step 4 uses the named intermediate and final local rings with flatness transitivity and source-cover descent; Step 5 uses the finite gluing statement and composite-transform calculus. The assembly remains below 3000 characters, with no step over 2000.

I checked the empty base and source, unit-centre, singleton refinement and U=S cases again. None requires nonempty schemes or a finite source scheme. In particular all refined charts are retained before the finite subcover is taken, and no intersections of affine opens are assumed affine. The four children remain self-contained statements with empty proofs; the old arguments and reports below remain intact. This is an adjustment of the retained split, followed by a fresh dry run, not an unchanged re-push.

## Rebase repair of the landing refusal (2026-10-22)

This is the follow-up to the return headed `9a819752b8f`: the reader approved the split, but landing refused it because the side-project completion had not been promoted into the live DAG read by the queue. The earlier section below concerns the previous content return and is retained as history. The present sandbox already contained all five node files, the complete report, citations and search results; I continued those files.

The required initial dry run completed with `OK (not pushed)` at `13543e32d08`. The delivery tool constructs its commit on the freshly fetched current `origin/sheaf-dag`, and overlays only split-owned fields, keeping current maintainer metadata. I compared the retained delivered item against the current shared read clone: the only differing fields were `proof`, `proof_deps` and `split_report`; its statement and statement dependencies agree exactly. The current released stage-1 repair note still requests the short assembly and at least three separate unsplit children. All four retained children are absent from the current read clone and are retained as the requested work items.

I re-read every existing statement used by the five assembly steps, rather than relying on the earlier review. All 22 citation entries are still verbatim substrings of the current statements (including the four sandbox children). Thus no changed statement calls for a replacement dependency. `research/rebase-current-citations.json` records the current existing statement interfaces and their hashes. I also re-read the statement dependencies and checked the current source interfaces for strict transform, admissibility, relative module flatness and pullback. No cited node has become merged.

The concrete assembly adjustment is step 4: it now names the source fibre products Z and Z_r, the point of the intermediate base and its image in the final base, and the two local rings along which flatness is composed. The product-centre node gives flatness over the intermediate base; the etale base map gives flatness of its local ring over the final local ring; module-flatness transitivity and then the jointly surjective flat source-family theorem give the claimed relative flatness. These are exactly the current statements of `lem-trf-factorized-centres-product-transform`, `lem-weil-pbc-etale-covering-base-change`, `def-weil-etale-morphism`, `def-weil-flat-morphism`, `lem-pc-module-flat-transitive`, `def-pc-scheme-module-flat-over` and `lem-trf-relative-flatness-source-cover`. No new mathematical assertion or hypothesis is introduced. The proof remains below 3000 characters.

For this rebase I re-read Stacks 0814 and 0813 and the 080Y boundary/gluing strategy in `flat.tex`; for the retained children I re-read Divisors 0805, 080A, 080F, 080I, 080M and 080N. The four arguments and edge cases reviewed below still apply: the preliminary affine refinement supplies qcqs local bases; the Cartier chart supplies an actual nonzerodivisor; product-centre transforms retain their support and quotient comparisons; gluing extends ideals from quasi-compact opens without assuming intersections affine. The empty source/base, unit centre and singleton cover cases impose no additional hypotheses. All steps remain short, and no long step hides an additional lemma.

I read the retained `searches.jsonl` and the saved result files. The search questions and all four helper statements are unchanged, so I reused those searches as instructed. The affine-refinement and flatness hits still do not supply the ideal factorization, strict-transform comparisons or global blowup assembly asserted by these nodes. There is no new node to search in this rebase. The project item theorem still ends in `sorry`, and the project-source search finds no completed exact attachment. No Lean writing or compiler was used.

## Correction of the return

The dedicated handoff is identified in `coord/returns/Q25.md` by returned head `adf3670da5fa81b4b128e91507bbaa06a17513de`. The sandbox contained only dispatcher marker files, not the promised earlier node/report/search log. I therefore used the current repository's retained ten-step proof, including its source, blueprint and Mathlib records. I read and preserved the earlier Q42 stage-1 report and NX statement report; their text appears below. Delivery rebases the split-owned fields over current server main, preserving maintainer records.

The return asks to spread the work, retain the item statement, add at least three comparable statement-only nodes, and make the parent at most 3000 characters. This repair adds four independent arguments. Their statements are approximately 2.0--2.5k characters each; none assumes or asserts the full etale flattening descent theorem. The new nodes have no proof steps, proof dependencies, or proof origin. The detailed old arguments have not been deleted: the complete original ten-step proof is reproduced verbatim below with every original dependency, and the assignment of its work is explicit.

| Returned steps | Destination of the argument |
| --- | --- |
| 1 and 5 | `lem-trf-etale-flatification-affine-refinement`: general finite affine refinement, and the stronger Cartier-chart refinement with factorized centre ideals; both covers and the restricted flat transforms are in its statement. |
| 2 and 3 | `lem-trf-etale-flatification-blowup-stability`: arbitrary earlier blowup, all pulled-back diagram properties, two orders of the blowups, product support, and equality of the module quotients. |
| 4 | Parent step 1 assembles the already existing complement-ideal, principalization, Cartier-ideal and module-calculus statements, then uses the new stability node. The elementary finite subcover is retained; no extra boundary theorem is invented. |
| 6 and 7 | `lem-trf-factorized-centres-product-transform`: product-centre construction, both blowup comparisons, union support, equality of module quotients, ordinary further pullback and local flatness. No covering/descent conclusion is assumed. |
| 8 | Parent step 4 assembles the existing etale-cover base-change, local-ring transitivity and relative-flatness source-descent statements. This is not hidden inside the product-centre node. |
| 9 | `lem-trf-module-flatification-zariski-gluing`: extend the centre ideals, take their product, describe its restriction/factorization and module comparison, then conclude base-local flatness. |
| 10 | Parent step 5 applies the existing module calculus to the preliminary and glued blowups; the unit and empty cases are retained. |

No statement dispute was found. In particular the module remains arbitrary quasi-coherent: no finite type, finite presentation, Noetherian, separatedness, density, or nonempty hypothesis was added to the item. The new stability and product nodes explicitly require qcqs local bases, which the refinement node supplies at their applications. The original non-quasi-separated etale bases are not silently assumed qcqs.

## Not duplicates

lem-trf-etale-flatification-affine-refinement vs lem-trf-module-strict-transform-flat-pullback: the existing node compares a single module quotient under flat source/base maps; the new statement also constructs a finite cover with factorized centre ideals.

lem-trf-etale-flatification-affine-refinement vs lem-trf-etale-flattening-descent: only refines given data and supplies local base-ideal factors; it constructs no global flattening blowup.

lem-trf-etale-flatification-blowup-stability vs lem-trf-module-strict-transform-flat-pullback: the existing node compares a single module quotient under flat source/base maps; the new statement also compares two blowup orders and preserves local-flatification hypotheses.

lem-trf-etale-flatification-blowup-stability vs lem-trf-etale-flattening-descent: preserves given local flatifications after an arbitrary chosen earlier blowup, with no global flattening conclusion.

lem-trf-factorized-centres-product-transform vs lem-trf-module-strict-transform-flat-pullback: the existing node compares a single module quotient under flat source/base maps; the new statement also constructs product domination and compares successive blowup transforms.

lem-trf-factorized-centres-product-transform vs lem-trf-etale-flattening-descent: assumes extra factorized base-centre data and proves local quotient/flatness comparisons; it does not assume covers or descend global flatness.

lem-trf-module-flatification-zariski-gluing vs lem-trf-module-admissible-blowup-calculus: the existing statement treats successive blowups over one base; it neither extends centres from an open cover nor gives the finite-cover gluing conclusion.

lem-trf-module-flatification-zariski-gluing vs lem-trf-module-strict-transform-flat-pullback: the existing node compares a single module quotient under flat source/base maps; the new statement also extends local centres and assembles a global flat transform.

lem-trf-module-flatification-zariski-gluing vs lem-trf-etale-flattening-descent: a generic open-cover gluing theorem with already-flat solutions on the base opens; it does not turn arbitrary etale charts into base-open solutions.

Further searches of the entire DAG and blueprint found no statement equivalent to a new node. `lem-trf-etale-ideal-local-factor` (0813) is deliberately reused as the ring-theoretic input for the refinement work: it is a primewise factorization and has no finite cover, inverse-image source cover, or restricted-transform conclusion. `lem-pc-fppf-affine-refinement` and `lem-trf-fppf-affine-refinement-pullback-model` concern fppf covers/descent data and do not provide centre factorization or module strict transforms. The scheme-only strict-transform nodes do not identify these module quotients. `sk-lem-nagata-sketch-blowups` and `lemma-nagata-extend-admissible-blowup` supply common blowups and extension, not the module statement in the gluing node. General flattening theorems 0815/081R add finite-type or geometric hypotheses absent here and are not alternative duplicates.

## Review by Q25

For the 2026-10-23 return I re-read the current statements, sources and saved search results as detailed above. I corrected the source scheme of the step-4 fibre product and named F_1 in step 3; all hypotheses and verbatim citation interfaces are unchanged. The nineteen existing interfaces were compared field by field, and all 22 step citations were checked against their current statements.

For the resumed rebase I checked the original and refined bases separately, and corrected step 1 to replace and relabel the finite affine diagrams explicitly. This discharges the qcqs hypothesis of blowup stability using the actual first clause of the refinement statement. The current cited statements still agree with the retained statement audit; the sources, hypotheses, each step and the unchanged search results were re-read as recorded in the resumed review above.

I read the whole proof of Stacks 0814 (`flat.tex`, `lemma-flatten-module-etale-localize`), the immediately preceding 0813 (`lemma-push-ideal`) and 080Y (`remark-successive-blowups`). I checked the chapter and unit records and the blueprint ancestor in current main-20261015. The node is a generic module-flatification input under the already recorded flattening branch of `lem-trf-local-term-locality`; neither the chapter nor unit route is changed. The four new statements make that same 0814 proof usable as four parallel work items.

For the refinement node I read 0814 paragraph 2 and 0813, and opened the statements of the finite-affine-cover, qcqs-morphism-permanence, affine-qcqs, etale-composition/cancellation, affine-etale ring equivalence and flat-transform-pullback nodes. The original S_i are quasi-compact since e_i are qc over qc S; this does not give quasi-separatedness, so all members of finite affine covers must first be retained. Refining X_i by inverse images preserves the source cover as well as the base cover. On each affine B chart, 0813 applies because the generator a on the Cartier base chart is a nonzerodivisor, J is finitely generated and V(J) is contained in V(aB). Its neighbourhoods D(g) cover Spec B; taking finitely many retains all base and source points. Both the first affine-refinement clause and its stronger factorization clause are stated, along with the comparison of the restricted module transforms. A mere affine-cover existence lemma would not say this.

For stability I read 0814 paragraph 1, plus Divisors 0805 (`lemma-flat-base-change-blowing-up`), 080A (`lemma-blowing-up-two-ideals`), 080F (`lemma-strict-transform-flat`) and 080I (`lemma-strict-transform-composition-blowups`). I opened the actual module-calculus and flat-pullback statements. Flatness is needed on both e_i and j_i, supplied by etaleness; the starting square need not be cartesian. The product ideal on S_i is (I O_Si)J_i, and the same final scheme can be reached with the factors in either order. The union of their zero sets is the composite support, so the quotients for the supported-section kernels agree, not just the blowup schemes. In the order beginning with the supplied flat transform, calculus (2) says the further transform is ordinary pullback and remains flat. The qcqs local-base hypothesis is explicit in this new node and is supplied by refinement before use in parent step 1. No global-flatification existence is asserted by stability.

For product domination I read the product-centre paragraph of 0814 with those same Divisors results. I checked that K_r=J'_r times the extensions of the other base ideals is written in the statement, and I O_Tr=J_r K_r. The product generators show finite type, and the finite union of zero loci proves admissibility. The product blowup factors through Bl_Jr as an actual further blowup; an arbitrary dominating morphism would not suffice. The support equality is stated, so calculus (1) and the quotient definition compare the same modules. The given first transform is flat; calculus (2) gives ordinary further pullback, and the flat source/base comparison identifies it with the pullback of the global product transform. The conclusion stops at local relative flatness on T_r^b; parent step 4 still supplies descent. No cover assumption was put in this node because its conclusion does not require one.

For finite Zariski gluing I read the last paragraph of 080Y, Divisors 080M (`lemma-extend-admissible-blowups`) and 080N (`lemma-dominate-admissible-blowups`), and opened both `def-nagata-extended-admissible-blowup` and its theorem. The extension interface allows arbitrary qc opens U and V, with local preservation open U intersect V; I did not substitute the weaker sketch interface requiring V to contain U. The new node states extension of the ideals themselves, the product construction, each further-blowup factorization, the restricted module comparison and flatness on each base open. This preserves all of old step 9. The opens and U have qc intersections because S is quasi-separated, so extension applies; no assumption on intersections being affine is made. Flatness of the final module is read stalkwise on the inverse-image open cover.

I checked every parent step against its cited statements (the whole statements are copied verbatim into citations.json). Step 1 uses the first refinement clause to make the S_i qcqs, the complement-ideal existence theorem to get V(K)=S minus U, principalization to obtain the Cartier boundary, its definition to choose affine charts with regular generator, module calculus to keep the new base qcqs and module quasi-coherent, and the new stability statement to preserve the local inputs. The finite subcover is just quasi-compactness. Step 2 uses etale-cover base change for both covers, qc base change for the base maps, and flat pullback of strict transforms to identify the restricted local flatifications. Its source/base maps are flat by the cited etale definition. The second refinement clause therefore applies with the actual regular element a_alpha, and returns exactly the ideals used in Step 3. Step 3 applies the new product statement with W_r affine and hence qcqs, e_r qc and flat, j_r flat, and the factorization supplied by Step 2; it obtains precisely the local flatness asserted, not global flatness. Step 4 uses the base-changed source cover and flat etale base maps. At every point, the local-ring maps are flat by `def-weil-flat-morphism`; `lem-pc-module-flat-transitive` is explicitly a theorem about flat modules along flat ring maps, and `lem-trf-relative-flatness-source-cover` explicitly states descent along arbitrary jointly surjective flat source families. The stalkwise definition of relative flatness checks the base rings. Step 5 uses the new gluing statement with the finite affine Cartier chart cover and the local solutions just obtained, then calculus (1) identifies the original-base composite transform with this successive transform.

Edge cases: for empty S or an empty covering index, the covering hypotheses force the relevant targets empty, products are unit ideals, and flatness is vacuous. Empty source X and the zero module require no ranks or nonempty stalks. If U=S, all local and global centres are units and the relative-flatness descent in Step 4 applies without modification; in the refinement node a unit a forces the local J and I to be unit ideals. If U is empty, an empty blowup is allowed, so no density hypothesis is imposed. In the product node a unit factor gives the identity blowup and a zero centre gives the empty blowup, consistently with the factorization and flatness conclusions. For a singleton diagram A=B the refinement factorization may take I=J and J'=B on the affine base. On a nonreduced base a nonunit regular element is still allowed; the regularity condition is multiplication injectivity, not integrality. Identity prior blowup makes stability tautological. A singleton global open cover makes gluing the original solution. The same-support assertion always concerns the specified composite/product centres, not an arbitrary isomorphic blowup with unrelated centre.

I checked delivery-errors B--E against the actual JSON and sources. Each new node introduces its own objects, has no proof sketch in its statement and has empty proof/proof_deps. The assertions are non-elementary separate tasks, not an elementary new fact, a restated full item, or an uncited source theorem. Definition dependencies name the actual module, blowup, etale/flat and spectrum notions. Sources carry Stacks tags and exact labels. Mathlib searches were made only via msearch.py, with two semantic phrasings per new node plus LeanSearch, Loogle and grep; the complete actual responses are in research and in the JSON. The affineRefinement hit gives only an open cover, flat/localization/descent hits give only module or morphism flatness, and none gives the requested blowup construction with comparisons. The only grep hit for product blowup was a comment in tactic GRewrite; the others had zero hits. Blueprint searches included 0814, 080Y, flatten, flatification, strict transform, etale local and admissible blow; every matching statement was read or ruled out as above. Every new node has the exact ancestor/via chain and its returned-step place. No long non-elementary parent step remains; the longest is below 700 characters. No SGA source, Lean edit, compiler, local preflight, or repository write was used.

The earlier report's source-label issue remains advisory: the generic module-calculus node calls `lemma-composition-finite-type-blowups` 080K, but the local tag table labels it 080B. Its actual statement and the read source supply the precise interface used. I did not edit that other node. Nothing in this repair is blocked; the four unsplit children are intentional future work, as the return requests.

## Validation

The preliminary server `check_dag` returned: `check_dag OK: no finding introduced by the sandbox or on its nodes`. Full dry run and delivery results are recorded after completion below.

## Preserved returned proof, without abbreviation

### Returned step 1

First refine every $S_i$ by all members of a finite affine open cover, and replace $X_i$ by its inverse images. Indeed $S_i$ is quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](2), and a finite affine cover exists by [lem-weil-pbc-qcqs-finite-affine-open-cover]. Retaining every member preserves both jointly surjective families. Affine schemes are qcqs by [lem-weil-pbc-affine-scheme-qcqs], and each new map to the quasi-separated scheme $S$ is quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](1). The open restrictions and their composites are etale by [lem-weil-pbc-etale-composition-cancellation], hence flat by [def-weil-etale-morphism]. The blowups restrict by [thm-nagata-blowup-flat-base-change], and their module transforms restrict by [lem-trf-module-strict-transform-flat-pullback]. Thus the original hypotheses hold for the refined diagrams. In particular all $S_i$ may now be assumed affine, so the qcqs hypothesis of the module blowup calculus is available when it is used on $S_i$.

Uses: lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-qcqs-finite-affine-open-cover, lem-weil-pbc-affine-scheme-qcqs, def-weil-etale-morphism, thm-nagata-blowup-flat-base-change, lem-trf-module-strict-transform-flat-pullback, lem-weil-pbc-etale-composition-cancellation.

### Returned step 2

First check stability of the hypotheses under any $U$-admissible blowup $b:S_1\to S$ with centre ideal $\mathcal I$. Put $T_i=S_i\times_SS_1$ and $Y_i=X_i\times_SS_1$. The two families $T_i\to S_1$ and $Y_i\to X\times_SS_1$ remain jointly surjective and etale by [lem-weil-pbc-etale-covering-base-change]; the former maps remain quasi-compact by [lem-pc-quasi-compact-base-change]. Etale maps are flat by [def-weil-etale-morphism]. Thus [thm-nagata-blowup-flat-base-change], with its comparison [def-nagata-blowup-flat-base-change-map], identifies $T_i$ with the blowup of $S_i$ in $\mathcal I\mathcal O_{S_i}$. By [lem-trf-module-strict-transform-flat-pullback], the pullback of $\mathcal F^b$ to $Y_i$ is the strict transform of $j_i^*\mathcal F$ under this blowup. The ideals are pulled back as ideals, and remain the unit ideal over the inverse image of $U$.

Uses: lem-weil-pbc-etale-covering-base-change, lem-pc-quasi-compact-base-change, def-weil-etale-morphism, thm-nagata-blowup-flat-base-change, def-nagata-blowup-flat-base-change-map, lem-trf-module-strict-transform-flat-pullback.

### Returned step 3

Write $\mathcal J_i$ for the given centre on $S_i$. Blow up $T_i$ in the extension of $\mathcal J_i$. By [thm-nagata-blowup-product-ideal] and the specified comparison [def-nagata-blowup-product-comparison], this is the blowup of $S_i$ in $(\mathcal I\mathcal O_{S_i})\mathcal J_i$; reversing the factors gives a blowup over $S_i^*$. Along either order the composite centre has zero set $V(\mathcal I\mathcal O_{S_i})\cup V(\mathcal J_i)$. Apply [lem-trf-module-admissible-blowup-calculus](1) to compare successive module strict transforms. Its chosen composite ideal and the product ideal have this same zero set, so [def-trf-module-strict-transform] identifies their quotients on the same final fibre product. Along the order starting with $S_i^*$ the first transform is flat by hypothesis; its further transform is its flat ordinary pullback by clause (2) of the calculus. Along the other order it is the strict transform of the pullback in Step 2. This proves the required local-flatification hypothesis for $\mathcal F^b$.

Uses: thm-nagata-blowup-product-ideal, def-nagata-blowup-product-comparison, lem-trf-module-admissible-blowup-calculus, def-trf-module-strict-transform.

### Returned step 4

Choose a finite-type quasi-coherent ideal $\mathcal K$ with $V(\mathcal K)=S\setminus U$ by [lemma-nagata-qc-open-complement-ideal-exists]. Blow it up. By [thm-nagata-blowup-principalizes-center] its extension is an effective Cartier ideal, whose support is exactly the complement of the inverse image of $U$. The new base is qcqs and the new module quasi-coherent by [lem-trf-module-admissible-blowup-calculus]. Steps 2 and 3 preserve the local-flatification hypotheses. By [def-nagata-effective-cartier-ideal], cover this base by affine opens on which this ideal is generated by a nonzerodivisor; quasi-compactness gives a finite subcover. We will solve the problem over each such affine and then combine the solutions. A solution after this preliminary blowup gives a solution over the original base by clause (1) of the calculus.

Uses: lemma-nagata-qc-open-complement-ideal-exists, thm-nagata-blowup-principalizes-center, lem-trf-module-admissible-blowup-calculus, def-nagata-effective-cartier-ideal.

### Returned step 5

Work now over one affine $S=\operatorname{Spec}A$ with $U=D(a)$, where $a$ is a nonzerodivisor. Cover each quasi-compact $S_i$ by finitely many affine opens using [lem-weil-pbc-qcqs-finite-affine-open-cover]. Restrict $X_i$ to the inverse images of these opens, retaining all the opens, so the source charts still cover $X$. These restrictions and their composites remain etale by [lem-weil-pbc-etale-composition-cancellation]. The original local blowup restricts to the blowup of the restricted ideal by [thm-nagata-blowup-flat-base-change]; module strict transforms restrict by [lem-trf-module-strict-transform-flat-pullback]. Write each affine base chart as $\operatorname{Spec}B$. Its map $A\to B$ is etale by [lem-weil-pbc-etale-ring-map-iff-etale-affine]. Its centre is a finitely generated ideal $J\subset B$ with $V(J)\subset V(aB)$. For every prime of $B$, [lem-trf-etale-ideal-local-factor] supplies a principal neighbourhood $D(g)$ and a finitely generated ideal $I\subset A$ with $V(I)\subset V(a)$ and $IB_g=(JB_g)J'$. Choose finitely many of these neighbourhoods covering each affine base chart, and again restrict the corresponding $X_i$ by inverse images. Thus all source and base points remain covered.

Uses: lem-weil-pbc-qcqs-finite-affine-open-cover, thm-nagata-blowup-flat-base-change, lem-trf-module-strict-transform-flat-pullback, lem-weil-pbc-etale-ring-map-iff-etale-affine, lem-trf-etale-ideal-local-factor, lem-weil-pbc-etale-composition-cancellation.

### Returned step 6

Reindex the finite refined diagrams by $r$. Their centres $\mathcal J_r$ and base ideals $I_r\subset A$ satisfy $I_r\mathcal O_{S_r}=\mathcal J_r\mathcal J'_r$. Set $I=\prod_r I_r$, with the empty product equal to $A$. The ideal is finitely generated by the products of chosen generators, and $V(I)=\bigcup_rV(I_r)\subset S\setminus U$; hence $S^b=\operatorname{Bl}_I S$ is $U$-admissible by [def-nagata-admissible-blowup]. By [thm-nagata-blowup-flat-base-change], its pullback to $S_r$ is the blowup in $\mathcal J_r\bigl(\mathcal J'_r\prod_{t\ne r}I_t\mathcal O_{S_r}\bigr)$. By [thm-nagata-blowup-product-ideal] with the comparison [def-nagata-blowup-product-comparison], this factors as the given $\mathcal J_r$-blowup followed by the blowup of the other factor. The two centres in this factorization have union of images equal to $V(I\mathcal O_{S_r})$.

Uses: def-nagata-admissible-blowup, thm-nagata-blowup-flat-base-change, thm-nagata-blowup-product-ideal, def-nagata-blowup-product-comparison.

### Returned step 7

On the pullback to $S_r\times_SS^b$, use the factorization in Step 6. Its first module transform is the given flat module on the local blowup; its further transform is flat by [lem-trf-module-admissible-blowup-calculus](2). Clause (1) identifies this successive transform with the transform for the product centre, using the support equality of Step 6; replacing a centre by another with the same zero set leaves the quotient unchanged by [def-trf-module-strict-transform]. By [lem-trf-module-strict-transform-flat-pullback], this module is the pullback of the global $\mathcal F^b$ along $X_r\times_SS^b\to X\times_SS^b$. Thus each of these pulled-back modules is flat over $S_r\times_SS^b$.

Uses: lem-trf-module-admissible-blowup-calculus, def-trf-module-strict-transform, lem-trf-module-strict-transform-flat-pullback.

### Returned step 8

The maps $S_r\times_SS^b\to S^b$ and $X_r\times_SS^b\to X\times_SS^b$ are etale and remain covering families by [lem-weil-pbc-etale-covering-base-change]. In particular they are flat by [def-weil-etale-morphism]. At every point of $X_r\times_SS^b$, the module of Step 7 is flat over the local ring of $S_r\times_SS^b$, which is itself flat over the corresponding local ring of $S^b$ by [def-weil-flat-morphism]. By [lem-pc-module-flat-transitive] it is flat over $S^b$. The stalk characterization in [def-pc-scheme-module-flat-over] applies without finiteness assumptions. The family of source maps is jointly surjective and flat, so [lem-trf-relative-flatness-source-cover] gives flatness of $\mathcal F^b$ over $S^b$. This proves the assertion on each affine Cartier chart of Step 4.

Uses: lem-weil-pbc-etale-covering-base-change, def-weil-etale-morphism, def-weil-flat-morphism, lem-pc-module-flat-transitive, def-pc-scheme-module-flat-over, lem-trf-relative-flatness-source-cover.

### Returned step 9

Return to the qcqs base with Cartier boundary from Step 4, and its finite affine open cover $V_\alpha$. Extend each solution over $V_\alpha$ to an admissible blowup of the whole base using [def-nagata-extended-admissible-blowup] and [lemma-nagata-extend-admissible-blowup]; the preserved open is $U$, so the local admissibility is relative to $U\cap V_\alpha$. Let $\mathcal L_\alpha$ be the extended finite-type centre ideals and blow up their product. By [thm-nagata-blowup-product-ideal] and [def-nagata-blowup-product-comparison], the product blowup factors over each extended blowup as a further admissible blowup. Open immersions are etale by [lem-weil-pbc-etale-composition-cancellation], hence flat by [def-weil-etale-morphism]. Restricting to $V_\alpha$ is compatible with these constructions by [thm-nagata-blowup-flat-base-change] and [lem-trf-module-strict-transform-flat-pullback]. Over $V_\alpha$ the first transform is the flat solution already constructed. The final transform is its further transform by [lem-trf-module-admissible-blowup-calculus](1), since the product centre has the union support of the successive centres; clause (2) keeps it flat. The inverse images of the $V_\alpha$ cover the final base, and the stalk definition of [def-pc-scheme-module-flat-over] therefore gives flatness everywhere.

Uses: def-nagata-extended-admissible-blowup, lemma-nagata-extend-admissible-blowup, thm-nagata-blowup-product-ideal, def-nagata-blowup-product-comparison, thm-nagata-blowup-flat-base-change, lem-trf-module-strict-transform-flat-pullback, lem-trf-module-admissible-blowup-calculus, def-pc-scheme-module-flat-over, lem-weil-pbc-etale-composition-cancellation, def-weil-etale-morphism.

### Returned step 10

Compose this final blowup with the preliminary boundary blowup. By [lem-trf-module-admissible-blowup-calculus](1) their composite is a $U$-admissible blowup and its module transform is the successive transform proved flat in Step 9. This is the required $S^b\to S$. If the scheme is empty the construction is empty and the flatness assertion is vacuous; finite products use the unit ideal when there are no charts. If $U=S$, all admissible centres are the unit ideal and the same source-descent argument gives flatness already on $S$, as required.

Uses: lem-trf-module-admissible-blowup-calculus.

## Preserved earlier reports

The reports below predate this repair; their file inventories and validation entries describe those earlier deliveries, not the four new children above.

### Q42 report (verbatim)

# Worker report: lem-trf-etale-flattening-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-flattening-descent.json`: split Stacks 0814 in ten steps; no Mathlib match after two semantic phrasings and the other logged searches.
- `dag/nodes/sec-trace-formula/lem-trf-etale-ideal-local-factor.json`: statement only, Stacks 0813; unsplit, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-module-strict-transform-flat-pullback.json`: statement only, flat-pullback compatibility of the quotient construction; unsplit, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-relative-flatness-source-cover.json`: statement only, Stacks 02JZ; unsplit, no Mathlib match.
- `citations.json`: exact statement quotations for every node used in every proof step. The whole cited statement is retained so its hypotheses remain visible.
- `searches.jsonl` and `research/*`: actual Mathlib search log, complete returned responses, and sandbox-only preparation scripts. These are research evidence, not additional project nodes.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag and flattening/flatification, strict-transform and etale-ideal concepts found no project declaration giving the item or any of these three new statements. Existing blowup declarations support the existing nodes already cited, rather than attachments for this item. The upstream master checkout was treated solely as reference material.

## WANTED

None. The needed source is present in the Stacks TeX checkout.

## Corrections and scope

The item had a correct statement but no proof. I kept every hypothesis and the conclusion. I replaced the final reference to etale as smooth of relative dimension zero by the existing equivalent etale-morphism definition, which directly exposes the flatness used in the proof. This is a definition-citation normalization, not a changed hypothesis. The unused module finite-presentation statement dependency was removed: neither the item nor 0814 assumes finite presentation or finite type for the module. Pullback and fibre-product definitions were added explicitly.

The route remains 0814: stability under admissible blowup, Cartier-boundary reduction, local factorization of centre ideals by 0813, product-ideal domination, flatness descent, and patching affine base charts. The chapter and unit records are unchanged. The blueprint ancestry through the flattening-module node is retained on the item and all children. Searches across the full DAG and the blueprint (`ancestor`, `search flatten`, `search strict transform`, `search push ideal`, `search flat pullback`, `search flatness`, `search 0813`, `search 02JZ`, and etale/base-change keywords) located the existing generic tools and no existing node for the three new statements.

An initial draft would have applied the qcqs module-blowup calculus directly over the original quasi-compact etale bases S_i. Those bases are not assumed quasi-separated. I corrected this by a preliminary refinement by all members of finite affine covers, with inverse-image refinements of the source charts, retaining every chart. The existing qcqs-morphism-permanence statement supplies the needed quasi-compactness and quasi-separatedness facts. This does not strengthen the item.

Minor upstream-record issue reported for maintenance: `lem-trf-module-admissible-blowup-calculus.source.place` labels `lemma-composition-finite-type-blowups` as 080K, while this Stacks checkout's `tags/tags` labels that lemma 080B. The statement of the node is the interface used here, and the actual 080B and 080I source texts support it. I did not edit that other node.

## Not duplicates

lem-trf-module-strict-transform-flat-pullback vs lem-trf-flattening-by-admissible-blowup: the former compares two sheaf quotients under flat maps; the latter asserts existence of a flattening modification and does not assert this comparison (shared 080D).

lem-trf-module-strict-transform-flat-pullback vs lem-trf-module-admissible-blowup-calculus: the former allows a separate flat source/base change; the latter treats composition of blowups and preservation of an already flat module, without this pullback comparison (shared 080D).

lem-trf-module-strict-transform-flat-pullback vs lem-trf-etale-flattening-descent: the new lemma is a general quotient comparison, with no covers, local flattening hypotheses, or existence of a base blowup; the item uses it to prove descent (shared 0814).

lem-trf-module-strict-transform-flat-pullback vs lem-trf-strict-transform-sheaf-kernel: the latter states quasi-coherence, the supported kernel, and the quotient's lack of supported sections; it does not identify the kernel after a flat pullback (shared 080D and 07ZP).

lem-trf-module-strict-transform-flat-pullback vs def-trf-module-strict-transform: the existing node defines the quotient, whereas the new node asserts compatibility of that quotient with flat pullback (shared 080D).

lem-trf-module-strict-transform-flat-pullback vs lem-pur-dnc-affine-blowup-complement: the existing node describes a deformation-to-normal-cone scheme chart, not arbitrary quasi-coherent module strict transforms under flat maps (shared 080D).

No existing source node with 0813 or 02JZ states either of the other new lemmas. In particular `lem-weil-pbc-flat-permanence` is the ring-theoretic 039V statement about a faithfully flat module, not relative flatness of a quasi-coherent module under a flat source map. `lemma-nagata-power-torsion-localization` handles localization, not arbitrary flat pullback. The existing `lem-weil-pbc-etale-covering-base-change` was reused after it was found, so no new etale stability leaf was created.

## Review by Q42

I read `flat.tex`, `lemma-flatten-module-etale-localize` (0814), its immediately preceding `lemma-push-ideal` (0813), and `remark-successive-blowups` (080Y). I also read `divisors.tex` for flat blowup base change (0805), the two-ideal blowup (080A), module strict transform (080D), flat-module strict transforms (080F), composition (080I), extension (080M), and domination (080N); `morphisms.tex` for module base-change flatness (01U8), flat permanence (02JZ), etale base change (02GO), and etale flatness (02GS); and `properties.tex` for supported sections (07ZP). The chapter, unit record, current main-20261015 unit and ancestor proof were read before splitting. The generic algebraic-geometric lemmas here serve the inherited flattening argument below the fixed unit route.

Step 1 uses the actual statements of `lem-weil-pbc-qcqs-morphism-permanence`, the finite affine cover node, and the affine-scheme-qcqs node, to make every refined local base qcqs. The existing `lem-weil-pbc-etale-composition-cancellation` states that open immersions are etale and that etale morphisms compose; I cited it explicitly to justify the restrictions. The cited blowup base-change comparison identifies the restricted blowup; the new strict-transform comparison gives the restricted module quotient. Both covering assertions remain true because all inverse-image source opens are retained. In particular I did not apply a finite affine subcover of the target as though it automatically covered the source by arbitrarily chosen source charts.

Step 2 cites the etale-cover base-change theorem, which explicitly preserves both etaleness and joint surjectivity, and the quasi-compact-base-change theorem. I opened both statements. The etale definition supplies flatness. `thm-nagata-blowup-flat-base-change` says its constructed comparison is an isomorphism; its definition node is cited alongside it to specify the two objects being identified. The new comparison node applies because both e_i and j_i are flat and the diagrams commute; no cartesian hypothesis on the original diagrams is inserted.

Step 3 cites both the product-blowup theorem and its comparison definition: their statements really identify the iterated blowup with the product-centre blowup. I used the module clause, not the scheme-only `lem-trf-strict-transform-composition`. The module calculus supplies composition and preservation of flatness. Centre supports are tracked through both orders; quotients for identical support agree by the strict-transform definition. This supplies stability of the local hypotheses rather than quoting that stability as a new lemma restating the item.

Step 4 obtains a finite-type ideal for the complement using the exact qc-open-complement node, and applies the principalization theorem to obtain a locally regular generator after blowup. The calculus states qcqs of the new base and quasi-coherence of the new module. The Cartier-ideal definition gives local generators which are nonzerodivisors. The finite subcover uses the definition of quasi-compactness. This checks the nonzerodivisor hypothesis of 0813 at its point of use; no integrality or Noetherian hypothesis is smuggled in.

Step 5 restricts affine base charts and local centres using the same blowup and strict-transform comparisons and the explicit open-immersion/composition theorem. The affine-etale/ring-etale equivalence node explicitly supplies the ring-map hypothesis. The new 0813 node has exactly the finite-generation, nonzerodivisor, containment of zero loci, and primewise neighbourhood hypotheses in the source. Applying it and taking finite subcovers preserves all original source charts through inverse images. No finite generation of the quasi-coherent module is used.

Step 6 builds the product ideal. Its generators, its unit restriction to U, and its zero-locus union are elementary finite-product calculations. Flat base change identifies its local blowup; the product theorem gives the factorization through each local centre, as a further blowup, rather than an arbitrary dominating map. The extended-centre factors and their union supports are written explicitly.

Step 7 uses the given local flatness and precisely clauses (1) and (2) of the module calculus, then the new flat-pullback comparison. The latter compares the module quotients, not merely their supports or scheme transforms. This is why the definition and the existing scheme strict-transform composition node alone would not have sufficed.

Step 8 descends flatness in two separate operations. First, on stalks, flatness over the local etale base and flatness of that local base over the global base compose by `lem-pc-module-flat-transitive`, whose statement is for an arbitrary flat module. Second, the 02JZ node detects relative flatness after the jointly surjective flat source family. Thus no converse involving the wrong base ring and no sheaf-definition node standing in for a descent theorem is used.

Step 9 expands the locality sentence in 080Y instead of leaving it implicit; the open-immersion/composition theorem also supplies flatness of the open maps used in the comparison. The existing extension construction allows arbitrary qc opens U and V, with local preservation open U intersect V; its theorem states that the extension restricts to the given blowup. I checked this rather than using the weaker sketch statement which requires V to contain U. The product comparison gives further blowups over each extended blowup, not just arbitrary morphisms. The union of centre supports permits the module-composition comparison; the already flat local solution stays flat by clause (2). Flatness is local on the base by the cited stalk definition. Step 10 uses the composite-admissible and module-composition clauses of the same calculus to return to the original S.

For the new pullback node I checked the generality explicitly: the assumptions are e:T to S flat and j:Y to X flat, with a commuting square, not a cartesian square. Flatness of e gives the identification of blowup bases; the induced j^b is the base change of j and is flat. On an affine blowup chart, supported sections are the kernel of N to N[1/a]. Flat extension preserves this kernel, and the tensor product of N[1/a] is the localization of the tensor product of N. Hence the torsion kernels and the quotient maps are identified; these canonical maps agree under restriction and glue. This is a non-elementary sheaf comparison not contained in the definition node or in Mathlib's ordinary tensor-quotient equivalence. I left it statement-only for the next split, as required, with its source places and this argument available to that worker.

For the new 02JZ node the pointwise statement is copied faithfully from the source, with the jointly-surjective-family consequence obtained by taking a preimage of every target point. The source-local flat homomorphism of local rings is faithfully flat even though no global quasi-compactness hypothesis is present. Mathlib's `Module.Flat.iff_flat_tensorProduct` is ordinary base-ring flatness of a module after extension of that base ring; it is not the relative flatness over a third base ring plus the geometric stalk identifications of 02JZ. The retrieved scheme `FlatDescent` results concern flat morphisms rather than arbitrary quasi-coherent modules, so this is not a one-line Mathlib leaf.

Small cases checked: identity e and j, the unit centre, and the zero centre (empty blowup) give the expected comparison for the pullback node. Over k[t], the strict transform of k[t] direct sum k[t]/(t) along (t) kills the second summand; flat base extension preserves that kernel, while dropping flatness need not, so flatness was retained on j. For 0813, A=B and g=1 give I=J and J'=B; a a unit forces J=B; the zero ring has no prime to check. For 02JZ, identity maps give a tautology and an empty jointly surjective family forces the target to be empty. For the item, U=S permits only unit centres and the conclusion follows from source flatness descent; U empty may give an empty blowup and entails no density assumption. Zero modules and empty source schemes cause no problem. No claim assumes a nonempty chart or nonzero rank.

All new nodes are unsplit statements with empty proof and proof_deps. All mathlib_searches entries reproduce actual tool/query text and results saved by msearch.py; each concept was tried in two semantic phrasings, with LeanSearch, Loogle and grep also run. Existing project declarations were inspected read-only. No Lean was written and no compiler or local DAG-validation script was run. Every proof step is below 2000 characters, so there is no long inline step hiding a subsidiary lemma. The three new nodes are independent generic facts, not clauses of the desired existence theorem. Nothing remains unfinished in this split; the new statements deliberately remain queued for later splits.

## Validation

The standalone server checks returned `review_split: PASS` and `check_dag OK: no finding introduced by the sandbox or on its nodes`. The first complete dry run detected combined bracket citations in the new ideal statement; I changed them to individual node brackets and regenerated exact quotations, without changing any mathematical assertion or recorded query.

The full dry run then passed at 3bde16d96b. A final citation audit added the existing open-immersion/etale-composition node explicitly in Steps 1, 5 and 9, so those facts are cited as theorems rather than attributed to the etale definition alone; the final dry run checks this revision.


### NX report (verbatim)

## Worker report

The module `Sheaf.TraceFormula.EtaleFlatteningDescent` states the Stacks Project Tag 0814 etale-local flattening descent lemma. It introduces schemes `S`, `X`, a morphism `f`, a quasi-coherent module `F`, a quasi-compact open `U`, a finite index type `ι`, the diagrams `Xi i ⟶ Si i ⟶ S` and `Xi i ⟶ X`, and the commuting equations `g i ≫ e i = j i ≫ f`. The hypotheses render quasi-compactness and etaleness of each `e i`, etaleness of each `j i`, and joint surjectivity of the two finite families by pointwise existential cover clauses. For every index, `B i : IsAdmissible (Si i) ((e i) ⁻¹ᵁ U)` is the local admissible blowup. Its local flatness clause uses the strict transform of the canonical pullback `(Scheme.Modules.pullback (j i)).obj F`, over the canonical pullback projection `pullback.snd (g i) (B i).I.blowupMap`. The conclusion is an admissible `B' : IsAdmissible S U` and flatness of the strict transform of `F` over `pullback.snd f B'.I.blowupMap`.

The recorded dependency declarations used are: `AlgebraicGeometry.Scheme` / `Scheme.Hom` from Mathlib (`Mathlib.AlgebraicGeometry.Scheme`), `AlgebraicGeometry.RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent` for the quasi-coherent module context, `AlgebraicGeometry.Scheme.Modules.IsFlatOver` from `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`, `AlgebraicGeometry.IsAdmissible` from `WeilConjectures.Blowup.AdmissibleBlowup`, `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform` from `Sheaf.AlgebraicGeometry.ModuleStrictTransform`, `AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `CategoryTheory.Limits.pullback` from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, and `AlgebraicGeometry.Scheme.Modules.pullback` from `Mathlib.AlgebraicGeometry.Modules.Sheaf`. The module also imports the project tensor-pullback interface because it is the project’s recorded module-pullback dependency; the statement uses Mathlib’s canonical pullback functor, which is the same pullback notion characterized by the recorded interface.

Edge cases checked: empty `S` and `X` make the covering clauses vacuous and the conclusion is still meaningful; an empty finite index type is therefore allowed only when the schemes are empty. A singleton cover reduces to the ordinary local flattening statement. Taking `U = ⊤` makes admissibility the unit-centre case. The strict-transform structure map is the pullback projection `pullback.snd`; the blowup map is already the second argument used to form that pullback.

Searches made: `msearch.py leanfinder` for “Local admissible blowups flattening a quasi coherent module on finite etale covers descend to one blowup of the base” and “etale descent of Raynaud Gruson flatification” (hits only generic flatness/etale declarations; no match); `msearch.py leansearch` for “Local admissible blowups flattening a quasi coherent module on finite etale covers descend to one blowup of the base” (generic flatness/descent hits; no match); `msearch.py loogle` for `strictTransform` (0 hits); grep over Mathlib and `WeilConjectures` for `flatten.*etale|etale.*flatten` (no existing declaration). Searches over `lean/Sheaf` found the existing strict-transform module and no declaration of this theorem.

The theorem proof is intentionally `sorry` at stage 2. No statement correction or `STATEMENT-DISPUTED` applies.


## Repair notes

The returned review identified that both flatness clauses had incorrectly composed the pullback projection with the blow-up map. They now use exactly `pullback.snd (g i) (B i).I.blowupMap` in the local hypothesis and `pullback.snd f B'.I.blowupMap` in the conclusion, matching Tag 0814 and the node statement. The unused `Mathlib.AlgebraicGeometry.Modules.Tilde` import was removed. The theorem docstring now records all ten proof steps from the node proof, including affine refinement, base-change stability, product-centre domination, relative flatness descent, gluing, composition, and the empty/unit edge cases.

The corrected Lean signature is:

```lean
theorem exists_admissibleBlowup_moduleStrictTransform_isFlatOver_of_finite_etale_cover
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    {ι : Type v} [Finite ι]
    (Si : ι → Scheme.{u}) (Xi : ι → Scheme.{u})
    (g : ∀ i, Xi i ⟶ Si i) (j : ∀ i, Xi i ⟶ X) (e : ∀ i, Si i ⟶ S)
    (hcomm : ∀ i, g i ≫ e i = j i ≫ f)
    (he_qc : ∀ i, QuasiCompact (e i)) (he_etale : ∀ i, Etale (e i))
    (hj_etale : ∀ i, Etale (j i))
    (he_cover : ∀ s : S, ∃ i : ι, ∃ x : Si i, e i x = s)
    (hj_cover : ∀ x : X, ∃ i : ι, ∃ y : Xi i, j i y = x)
    (B : ∀ i, IsAdmissible (Si i) ((e i) ⁻¹ᵁ U))
    (hB_flat : ∀ i,
      letI : (B i).I.toModules.IsFiniteType :=
        (B i).I.isFiniteType_toModules_sheaf (B i).finiteType
      Scheme.Modules.IsFlatOver
        (@Scheme.Modules.moduleStrictTransform (Xi i) (Si i) (g i) (B i).I
          inferInstance ((Scheme.Modules.pullback (j i)).obj F) inferInstance)
        (pullback.snd (g i) (B i).I.blowupMap)) :
    ∃ B' : IsAdmissible S U,
      letI : B'.I.toModules.IsFiniteType :=
        B'.I.isFiniteType_toModules_sheaf B'.finiteType
      Scheme.Modules.IsFlatOver
        (@Scheme.Modules.moduleStrictTransform X S f B'.I inferInstance F inferInstance)
        (pullback.snd f B'.I.blowupMap)
```

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.


