## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-space-infinitesimal-lifting.json: item, split into three steps; statement unchanged; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-formally-etale-space-chart-locality.json: statement, unsplit, Mathlib no match. One new node, zero new Mathlib leaves.
- citations.json: verbatim statement quotes for every step/dependency pair.

Attachments: none. The exact blueprint tag and lifting/concept searches throughout lean/WeilConjectures found no project declaration stating the algebraic-space result. AlgebraicGeometry.flat_unramified_formally_etale in AlgebraicGeometry/FlatUnramifiedFormallyEtale.lean:65 treats schemes and is already attached to the existing scheme input. Its declaration and proof were read; no claim about its transitive closure is needed here.

WANTED: none.

The item was statement-only, with no proof and no Lean audit attachment. I retained its full statement, source, created record and historical blueprint lineage, and added the proof. Stacks 0616 reduces to the scheme case by 04GD; the scheme implication 02HM uses flat unramified lifting 04FF. I reused the existing node for 04FF, rather than duplicating the scheme case. I did not create a new node for an etale scheme morphism being flat and unramified: this is literally the cited definition.

Nothing mathematical remains unfinished in the item's one-level split. The new chart-locality theorem is deliberately statement-only and remains queued for its own split. The latest blueprint direct-images proof (3) gives compactification/direct-image assembly; the item's historical alteration prerequisite is farther below that assembly. The ancestor command reports None for the live item, so the existing null from.node and complete via chain are retained, and the new node prepends this item to that chain. No chapter or unit record was changed.

## Searches

I searched the full DAG by the source tags 0616, 04GC, 04GD, 02HM, by lemma-formally-etale and lemma-etale-on-top, and by formal-etaleness/chart/lifting keywords, reading the candidate statements. In particular lem-sfb-unramified-etale-compatible-charts recognizes etaleness and produces compatible charts but does not identify formal lifting properties; lem-sfb-smooth-space-affine-infinitesimal-lift gives existence for smooth maps, without uniqueness. Neither supplies the new locality statement. The two lfp-unique-infinitesimal-lifts-etale nodes prove the reverse scheme implication and cannot be used for this direction.

Whole-blueprint searches with tools/blueprint_refs.py used 'infinitesimal lifting', 'formally', '04GD', and 'etale'. The precise formal-etaleness/tag searches found no matching blueprint theorem. The broad etale output contains general etale notions, not the locality statement. Both same_as lists are empty.

All new Mathlib queries ran through batch2/msearch.py; searches.jsonl preserves the actual tool/query/digest records. Two natural-language phrasings were used for the item and two for the locality node, with LeanSearch, LeanFinder, Loogle and source grep. The node records the actual query text and returned names; all services answered. The grep restricted to AlgebraicGeometry for 'AlgebraicSpace|FormallyEtale' returned zero hits. I read Mathlib/AlgebraicGeometry/Morphisms/Etale.lean (scheme Etale, its flat/formally-unramified characterization) and RingTheory/Etale/Basic.lean (Algebra.FormallyEtale.iff_comp_bijective). These statements concern schemes or rings and do not supply formal-etale descent for algebraic spaces. Scheme IsEtale names in the search index are deprecated aliases in the pinned source. No Mathlib leaf was claimed.

## Not duplicates

lem-sfb-formally-etale-space-chart-locality vs lem-sfb-etale-space-infinitesimal-lifting: the new theorem is locality of the unique-lifting property for arbitrary morphisms, without an etaleness or finite-presentation hypothesis; it does not assert that etale morphisms satisfy that property. The item's argument establishes the property on every chart using flat unramified scheme lifting, before applying locality.

lem-sfb-formally-etale-space-chart-locality vs lem-sfb-unramified-etale-compatible-charts: the existing theorem recognizes scheme etaleness/unramifiedness on compatible charts; the new theorem transfers the square-zero lifting property itself.

No existing node has source Tag 04GD. No dependency was created for an elementary step or a clause of the item.

## Review by NV

I read spaces-more-morphisms.tex Tag 0616 (lemma-etale-formally-etale), its cited Tag 04GD (lemma-formally-etale), and the definition-formally-smooth-etale-unramified together with 04GC. These explicitly use affine scheme tests and square-zero ideals. The item has exactly these tests. I read more-morphisms.tex 02HM, implication (1) to (2): its argument is etale implies flat and unramified, then 04FF. That is the scheme route used in this split. The new node states precisely the (1)/(2) equivalence of 04GD with the unique-lifting predicate expanded; it adds no etaleness hypothesis on the arbitrary map f, no separation and no finiteness. It is a structural locality result, not a replacement name for the item.

Step 1 cites def-weil-etale-morphism. I opened its statement, which defines etale as locally of finite presentation, flat and unramified; hence extracting flatness and unramifiedness is elementary. The existence of a chosen chart is not silently assumed: the proof quantifies over every compatible diagram, matching condition (2) in 04GD. Thus no separate chart-existence or fibre-product representability lemma is consumed by this step.

Step 2 cites lem-weil-pbc-flat-unramified-formally-etale. Its statement supplies exactly one lift for a first order thickening of affine schemes over the target scheme. Here that target is V, the lower arrow d makes the test a V-scheme, and the equation h c_0=dj makes c_0 a V-morphism. Flatness and unramifiedness were extracted for that same h in step 1. All test schemes remain affine. A resulting V-morphism is an S-morphism by composition with V to S, so the predicate P(h) is exactly the one in the new node, also cited in this step for its explicit meaning. This does not require representability of the original E to Y or affine charts U,V. The cited scheme theorem permits arbitrary source and target schemes.

Step 3 uses the new node's reverse implication, not anything from its unrecorded proof. The hypothesis is P(h) for every compatible chart, proved in step 2; its conclusion P(p) is substituted into the given test diagram. The two resulting equations and uniqueness are literally the item. Every statement quoted in citations.json was copied verbatim from the actual cited node. No non-elementary assertion is justified only by a tag or by a definition node.

For small cases, an identity thickening has its prescribed lift, and the zero square-zero ideal creates no extra choice. For an empty test T, also T_0 is empty, and the unique empty map works; an empty T_0 with nonempty T cannot be a square-zero thickening, since such immersions are surjective on points. Empty chart sources give vacuous lifting unless the test is empty. The new locality statement requires every compatible diagram, not one possibly empty/non-surjective chart, avoiding the false assertion that an arbitrary single chart detects the property. Non-separated or non-quasi-compact spaces are allowed in 04GD and in the item, and no affine intersection or finite covering is assumed. The argument never substitutes an I^N-adic henselian hypothesis or changes coefficient categories.

I checked B1--B10: statement-only new node, all objects introduced, notions supplied by four definition dependencies, single TeX escapes, correct source label/tag, truthful Mathlib records, and preserved blueprint fields. I checked C1--C8 by opening each of the three cited statements; the scheme input is declared as a generic tool use in split_report (not in a maintainer-owned tool_uses field). I checked D1--D5: the item carries the actual chartwise scheme argument, the new node has a different arbitrary-map locality statement, and no circular citation or induction is present. The locality node's future proof will handle the non-elementary descent argument; it is not pretended elementary here. I checked E1--E7 against the square-zero test, the chosen base V, and the two triangle equations. No statement correction or source error was needed. No proof step exceeds 2000 characters. This is a direct worker delivery; I performed this reading myself, with no second worker or subagent.

## Validation

The server check_dag and review_split checks passed. The required deliver.py --no-push passed preflight at 4c55354762b. A final line-number check corrected the scheme input location in this report from 71 to 65; the final dry run below revalidates the report before pushing.
