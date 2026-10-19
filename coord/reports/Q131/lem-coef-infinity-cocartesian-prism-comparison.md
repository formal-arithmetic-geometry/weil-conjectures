# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-cocartesian-prism-comparison.json`: existing statement node, now split. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for all twelve step citations.
- `report.md`: retained work and source/search review, updated for the repaired five-step proof.

## Attachments

None. The read-only slopmaster2 search for the exact blueprint tag, cocartesian terminology and mapping-simplex terminology finds no project declaration proving either comparison. Upstream sorry declarations are not treated as completed proofs.

## WANTED

- WANTED: archival copy of Lurie, Higher Algebra, Lemma 2.4.4.6 proof, printed p. 308 (PDF page index 307), for this item.
- WANTED: archival copy of Lurie, Higher Topos Theory, section 3.2.2, especially the mapping-simplex construction on printed p. 179 and Definition 3.2.2.6 / Proposition 3.2.2.7 on printed p. 180, for this item.

Both official PDFs were read online on 2026-10-17. The source URLs are https://people.math.harvard.edu/~lurie/papers/HA.pdf and https://people.math.harvard.edu/~lurie/papers/HTT.pdf . Nothing was downloaded into the project. No Stacks tag states this quasicategorical assertion. The expanded lifting and degreewise-identification argument is explicitly marked agent-written, pending archival sources.

## Corrections and retained work

The earlier sandbox already held a split, citations, this report and logged Mathlib searches. Its required initial dry run completed successfully at d5daebb1a2. I retained that work rather than restarting the item. I read the saved search results and searches.jsonl; no search was repeated. The node retains its inherited search entries and now also records the previously executed sandbox searches, with their actual result summaries. The hits concern ordinary-category cocartesian arrows, model-category cylinders, base horns, simplices and opposite simplicial sets; none gives either prism equivalence. The Loogle query containing the unknown identifier `cocartesian` is inconclusive on its own; the valid second query and semantic searches supply the other checks.

The statement is unchanged: the source's two pushouts are exactly A and B, the map h is given, p is only an inner fibration, and no lifts over 1→2 or 0→2 are added. I corrected proof omissions: saying merely that the collapsed map has the chosen lifts did not establish its inner-fibration or cocartesian-edge conditions; the new Step 1 checks the actual horn problems. I corrected the reversed chains to use opposite fibers, added an explicit citation for degenerate edges, and wrote the simplicial-operator formula for each pushout instead of merely asserting an identification. I also corrected references to printed p. 307: the displayed HA maps are on printed p. 308. The inherited source field already gives p. 308; maintainer-owned metadata is not changed by this delivery.

The DAG searches for prism, cocartesian transport and mapping simplices found existing tools, so nothing new was created. Whole-blueprint searches for `prism` and `mapping simplex` returned zero matches. The exact source section is realized through the inherited operadic inner-horn branch. The chapter and unit records were read and are unmodified. The generic mapping-simplex theorem, its construction formula, and the degenerate-edge clause are declared in split_report.tool_uses where appropriate; none replaces the inherited proof route.

## What remains unfinished

No mathematical part of the split remains open. The two requested archival copies are still WANTED. Only stage 1 was performed: no Lean files, compiler, Lake or build tools, live project changes, or subagents.

## Review by Q131

I read the two displayed maps after the choice of h in HA Lemma 2.4.4.6, printed p. 308, and the construction, marking, quasi-equivalence hypotheses and categorical-equivalence conclusion in HTT section 3.2.2, printed pp. 179–180. In particular HTT requires a cartesian fibration and marked-edge preservation, not just identity maps on fibers. I opened the current statements of all six cited DAG nodes and checked the actual hypotheses below. No new node needs a separate source or duplicate audit.

Step 1 uses the standard-simplex vertex description from def-cbc-enhanced-diagrams-cones and the inner/outer horn definitions from def-coef-infinity-fibrations. For cp, the projected inner horn extends uniquely by its monotone list of vertices in [2], then p lifts it. For the first outer horn with the chosen edge, the only low-dimensional difficulty is the missing edge between domain vertices 1 and 2; their p-values are 1 and either 1 or 2 because of the prescribed collapsed base simplex. That makes the missing edge available. In higher dimensions every edge is present. Thus the original p-cocartesian hypothesis supplies exactly the filler needed for cp. This is a direct verification for the particular collapse, not an unproved general composition theorem.

Step 2 uses the same definition nodes to pair lifts with a restricted base simplex. This proves the inner-fibration and chosen-edge claims for the 0–1 restriction and that its total space and all relevant fibers are quasicategories. The statement of lem-coef-infinity-cocartesian-composition-initiality explicitly says every degenerate edge is p-cocartesian; only that sentence is used to supply lifts of degenerate base edges. For either interval projection, the only remaining base edge starts at 0 and has the stipulated h-lift. Reversing the simplicial operators interchanges the first and last horns and sources and targets, so these give the required cartesian fibrations. The fiber orders are C1^op, C0^op and D^op, C0^op, respectively; no additional transports are assumed.

Step 3 uses only the construction/marking part of lem-coef-cartesian-mapping-simplex-presentation, not its existence result or its proof. Its statement specifies the pairs (alpha,a), their last-vertex coordinate, the transition after restriction, and the degenerate-second-coordinate marking. I matched these in every degree with the reversed pushouts: the 0-end is glued to P, while other simplices have their coordinate in Q. Dropping the last 1-vertex applies the prescribed transition F^op or (iota F)^op. Constant-base marked edges go to degenerate edges, justified by the same degenerate-edge sentence from the composition/initiality node; nonconstant marked edges are reversals of the already checked vertical h-edges. The vertex maps are identities. This checks every marked edge, including constant ones.

Step 4 uses the statement, not the proof, of lem-cbc-mapping-simplex-universal-equivalence. Its hypotheses are satisfied by Steps 2–3 with n=1 and identity T→Delta^1. Every object is small by the original hypothesis and degreewise construction. The identity fiber maps are categorical equivalences directly by the definition in lem-coef-joyal-model-structure. The cited theorem therefore gives both reversed categorical equivalences, not merely a marked equivalence or a fiber comparison.

Step 5 uses the functor-test definition in lem-coef-joyal-model-structure and the functor simplicial sets in def-cbc-enhanced-diagrams-cones. Reversal identifies the tests with opposite ordinary categories; reversing the generating triangle relations proves this directly. Quasicategories stay quasicategories by the horn reversal already checked. Thus the two equivalences reverse to exactly the original maps. For C0 empty, no simplex can have a vertex over 0, so both maps are isomorphisms. For p=id on Delta^2, A→C01 is an isomorphism and B→C is the inner-horn inclusion, consistent with categorical equivalence. If C1 is empty, the existence of h forces C0 empty; this case is included too. D may have vertices only over 2 and requires no 1→2 lifts. Every proof step is below 2000 characters; the operator and horn checks are direct calculations for these fixed constructions and hide no separate standard lemma.

The initial passing dry run alone did not certify these mathematical details; I repaired them before the final dry run and delivery. All citation quotes were copied from the current node statements and checked literally. There is no statement dispute and no change of the higher-level route.
