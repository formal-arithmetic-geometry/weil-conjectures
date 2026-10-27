# Q142: lem-trf-module-flatification-zariski-gluing

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-module-flatification-zariski-gluing.json`: statement; split into six steps using existing nodes. Retained the statement, statement dependencies, source, creation record and blueprint ancestry. Retained the inherited searches and added the searches actually run for Q142.
- `citations.json`: thirteen entries, one for each citation occurrence, quoting the cited statements verbatim.
- No new nodes; zero new Mathlib leaves. `searches.jsonl` is the actual command log. `write_split.py` is sandbox-only preparation, not a project file.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the item id, flatification, flattening, module-flat and Zariski-gluing notions; the blowup extension/product code and ordinary flatness results do not state this full module-flatification result. The module-strict-transform comparisons are indispensable; scheme-only statements do not suffice.

## WANTED

None. The sources used are present locally.

## Corrections and source alignment

The first delivery dry run flagged the phrase "the item's hypothesis" as non-self-contained. Replaced it by the explicit given flatness hypothesis on the blowup of V_alpha in J_alpha; the mathematical argument is unchanged.

The live item was unsplit, with no proof. Its mathematical statement is correct as written. I have not changed it. In particular, no flatness of the scheme morphism X -> S, finite presentation of F, density of U, noetherianity or affineness of overlaps was added.

Read `flat.tex` Tag 080Y (`remark-successive-blowups`), especially its last paragraph, and Tag 0814 (`lemma-flatten-module-etale-localize`); read `divisors.tex` Tags 080M (`lemma-extend-admissible-blowups`), 080N (`lemma-dominate-admissible-blowups`), 080A (`lemma-blowing-up-two-ideals`), 080I (`lemma-strict-transform-composition-blowups`, module clause (1) and kernel comparison proof), and 080F (`lemma-strict-transform-flat`, module clause (2)); read `properties.tex` Tag 01PF (`lemma-extend`). These are the specified extension/product route. Also read the corresponding existing blueprint ideal-extension, two-open ideal-gluing and product-blowup statements/proofs.

The nearest blueprint ancestor is `lem-trf-local-term-locality`, as reported by `tools/blueprint_refs.py ancestor`. Its current main-20261015 proof quotes Varshavsky and the normal-cone theorem rather than a flatification argument. I preserve the assigned item's recorded genealogy, explicitly describe this discrepancy in `split_report.blueprint`, and split its already-seeded Stacks subproblem without inventing a new alteration route or changing the chapter or unit. This item is not the unit's key statement, so no unit realization fields are written.

## Not duplicates

No new nodes. DAG/blueprint searches for flatification, strict transform, admissible, extension and ideals found the existing two-open gluing, finite-type ideal extension, product-blowup and factorized-centres transform lemmas. The last is more general than the local comparison needed here and is cited rather than cloned. It does not supply the local-to-global extension construction or the final gluing of flatness; those are explicit steps of this item. The scheme-only common-blowup node is not used for module transforms.

## Mathlib searches

Ran the required command for LeanFinder (two phrasings), LeanSearch, Loogle and grep. The query strings in the appended `mathlib_searches` agree exactly with `searches.jsonl`. Both LeanFinder results and LeanSearch return scheme-flatness/descent/ideal-chart tools rather than the admissible module-strict-transform gluing assertion; Loogle and grep return zero hits. Read the flat-morphism source, including the affine definition, stalk criterion and restriction/open-immersion instances. None supplies the full item. The inherited Q25 searches are preserved as inherited records, not claimed as new Q142 executions.

## Review by Q142

I checked delivery-errors B--E against the actual node and sources. There are no new unsplit nodes, so no proof hidden inside a new statement, elementary-node inflation, unsearched fresh node or duplicate-tag pair. Each proof step is under 1000 characters; none reaches the long-step threshold. All citations use statements rather than proof internals, and a dependency traversal found no path from any cited node back to the item.

Step 1 uses `lemma-nagata-glue-finite-type-ideals` for exactly an equality of restrictions on U intersect V_alpha. The equality follows from the given unit-ideal hypothesis. Its statement produces the ideal on U union V_alpha, with no affine-overlap requirement. Then `lemma-nagata-finite-type-ideal-extension-exists` supplies an actual ideal extension, not just an isomorphism of blowups. Its hypotheses hold because S is qcqs and the union of the two quasi-compact opens is quasi-compact. This is precisely the construction in 080M's proof using 01PF. Each alpha is treated independently; no agreement of the original centres on different V_alpha is needed.

Step 2 is the explicit elementary product computation: products of finitely many local generators generate the ideal product, commute with localization, and restrict to 1 on U. The cited `def-nagata-admissible-blowup` says exactly that a finite-type quasi-coherent ideal equal to 1 on U, with its specified blowup, is an admissible datum. This proves admissibility without density of U.

Step 3 uses `thm-nagata-blowup-product-ideal`, whose statement identifies the iterated and product blowups, together with `def-nagata-blowup-product-comparison`, whose statement specifies the second centre as the extension of the other factor. I opened both statements; the latter is used to interpret the former's explicitly named constructed maps, not as a substitute for the theorem. With L = L_alpha times M_alpha the theorem supplies the global factorization. The second ideal is finitely generated locally by images of generators and equals 1 above U, so the admissibility definition applies again. This is 080A/080N.

Step 4 instantiates the existing `lem-trf-factorized-centres-product-transform` with T_alpha = V_alpha, Y_alpha = X times_S V_alpha, I_alpha = L_alpha and J'_alpha = 1. I read its entire statement: it requires a qcqs T_alpha, quasi-compact flat e_alpha, flat j_alpha, a commuting square and equality I_alpha O_T_alpha = J_alpha J'_alpha. The opens V_alpha are qcqs because S is quasi-separated and they are quasi-compact. The open inclusions have identical local rings by `def-weil-open-immersion`, making them flat under `def-weil-flat-morphism`. `lem-weil-pbc-qcqs-morphism-permanence` (1) supplies quasi-compactness of e_alpha; it does not impose quasi-compactness on j_alpha or X. The square uses only the fibre-product projections. The ideal equality and first-transform flatness are exactly the given hypotheses after Step 1. The generic permanence node is an off-unit tool, declared in split_report, rather than a substitute for the unit's geometric route.

Step 5 takes precisely the product-transform lemma's stated two-step comparison, module quotient compatibility, ordinary-pullback identification for the flat first transform, and resulting relative flatness. Substituting J'_alpha = 1 makes its K_alpha the restriction of the global complementary product. Its statement gives the desired module comparison, unlike the existing `lem-trf-strict-transform-composition`, whose statement only concerns schemes. This avoids a C4 misuse of that scheme-only node. The source module statements are 080I (1) and 080F (2); no unsupported inference that tensor preserves injections is needed here.

Step 6 uses the stalk equivalence explicitly stated in `def-pc-scheme-module-flat-over`. For any point choose an open b inverse V_alpha containing its image; restriction preserves the module stalk and base local ring, so the flatness already proved is exactly the global stalk condition. This elementary argument, not an unproved generic gluing claim, carries the final conclusion. It also makes clear why no finiteness or quasi-compactness hypothesis on X is being smuggled in.

Tested small cases: an empty index set forces S empty and then X empty; empty individual charts impose vacuous conditions; a singleton cover has complementary product 1; U = S forces every global extension to be the unit ideal and the hypothesis already gives local flatness; U empty allows nondense centres and even the zero ideal without a density argument. F = 0 is immediate for every centre. Arbitrary nonseparated X causes no issue, since only open restriction and stalks are used. No test refutes the statement. None of the cited statements asks for noetherianity, finite presentation, or affineness of the opens.

## Unfinished work

None within the stage-1 split. Existing cited unsplit nodes remain their own items; this delivery does not claim they have Lean proofs. Required server checks and direct delivery are run after this report.
