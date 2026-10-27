# Stage-1 report: lem-sfb-space-lft-cancellation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-lft-cancellation.json — statement, now split; not a Mathlib leaf because its objects are algebraic spaces. Four proof steps, five reused dependency nodes, no new nodes and no new Mathlib leaves.
- citations.json — verbatim statement excerpts for every step/node pair.
- report.md — this report. searches.jsonl is the unmodified search-command log.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag, algebraic-space vocabulary, and locallyOfFiniteType_of_comp found scheme-level applications only. In particular the occurrences in Compactification/CategoryBaseChange.lean and SixFunctors/Etale/Derived/Finiteness/DirectImage.lean apply the Mathlib scheme theorem; they do not state the algebraic-space conclusion. No sorry declaration is treated as completed work.

## WANTED

None. All mathematical sources needed for this split are available locally.

## Problems and corrections

The imported statement is correct and is preserved verbatim, including the absence of any hypothesis on the second arrow. Its proof was empty. The split follows spaces-morphisms.tex Tag 0462, lemma-permanence-finite-type, whose proof cites compatible presentations (spaces.tex Tag 02X1), the local finite-type chart criterion (Tag 040Y), and scheme cancellation (morphisms.tex Tag 01T8). Rather than add nodes for these already represented facts, it reuses the atlas definition, the existing fibre-product and etale-cover calculus, the existing chart criterion and clause (a) of the existing scheme cancellation Mathlib leaf.

I expanded the chart construction instead of treating an arbitrary commutative diagram of atlases as cartesian. Choose W over Z, V over Y_W, and U over X_V. For the composite, U must cover X_W, not just X; step 2 proves this by the explicit identification X_V = X_W times_{Y_W} V. For the final application, U covers X times_Y V by its construction, and V covers Y by pullback and composition. This addresses the chart criterion's actual hypotheses.

The historical blueprint ancestor is null in the live node and blueprint_refs.py ancestor confirms it remains null. I retained its complete inherited from.place and via chain, with same_as empty after searches. I read only literature/blueprint/latest for the current source: sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially paragraph (3). These now express direct-image preservation by the open/proper route; the item's inherited alteration/moduli helper remains a generic prerequisite already in the DAG. This delivery neither modifies a unit nor replaces one of its arguments.

## Not duplicates

No new nodes. Searches of the whole DAG by 0462, 040Y, 02X1 and the labels permanence-finite-type, finite-type-local, lift-morphism-presentations, and by compatible chart/cancellation vocabulary were read. blueprint_refs.py searches for finite type, presentations, lift-morphism-presentations, cancellation, 0462 and algebraic spaces were also read. The full results include existing scheme cancellation lemma-nagata-finite-type-to-separated-target, compatible-chart existence lem-sfb-unramified-etale-compatible-charts, general property extension lem-sfb-space-etale-presentation-property-criterion, and the local chart test actually used. None is a duplicate statement of this algebraic-space cancellation lemma. Reusing the fibre-product calculus makes another compatible-atlas node unnecessary.

## Mathlib searches

The live item's older 2026-10-22 search records were retained. I additionally ran the prescribed logged search command in all four modes for this item, including two different semantic formulations. LeanFinder, Loogle and LeanSearch returned scheme cancellation and stability lemmas. The logged grep found AlgebraicGeometry.locallyOfFiniteType_of_comp at Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:72. I read lines 60-80, including its complete declaration and proof at 72-74: all three objects are Scheme. It is exactly the scheme input, already recorded by the existing Mathlib leaf, but does not state the algebraic-space assertion. All services answered successfully. The five new entries in mathlib_searches are derived from the actual searches.jsonl entries, with precisely the same tools and query texts.

## Unfinished work

Nothing in this item's stage-1 split. Existing unsplit dependencies remain their own tasks. No Lean was written, and no compiler, Lake, local DAG checker, or git command was run.

## Review by Q104

I read the statement and proof of spaces-morphisms.tex Tag 0462, the full chart equivalences in Tag 040Y, the construction in spaces.tex Tag 02X1, scheme cancellation in morphisms.tex Tag 01T8, and the etale-cover pullback/composition clauses in spaces-topologies.tex Tag 041F and spaces-properties.tex Tags 03FT and 03FU. There are no new node sources to review. I also read each cited node's statement in the current repository, not merely its proof or its label.

Step 1 takes atlas existence precisely from def-trf-algebraic-space: its definition includes a representable surjective etale scheme atlas. lem-trf-space-fibre-products-etale-covers says the two sheaf fibre products are algebraic spaces and categorical fibre products. Therefore the definition applies to each. The compatible maps to V and W are the product projections. No unramifiedness, finite presentation, or scheme-representability of a or b is being inserted.

Step 2 uses lem-trf-space-fibre-products-etale-covers for pullback of etale coverings, first for Y_W to Y and then for X_V to X_W. The latter identification is justified on test schemes by a pair of explicit inverse maps; it is only the universal property of a fibre product, not a separate comparison lemma. lem-trf-space-chartwise-etale-permanence explicitly states that composites of etale coverings are coverings and equates chartwise with representable etaleness for scheme sources. It supplies the surjective etale composites V to Y and U to X_W. Both have scheme sources. Neither conclusion is taken from the fibre-product node's proof instead of its statement.

Step 3 uses lem-sfb-space-local-properties-chart-test only after verifying exactly its target atlas and source atlas hypotheses. Its choice P = locally of finite type is one of its three stated alternatives, and the iff goes from the assumed property of b composed with a to that of U to W. Clause (a), not clause (b), of lemma-nagata-finite-type-to-separated-target says that local finite type of a scheme composite implies local finite type of its first arrow. Its hypotheses require no separatedness on V to W. This is the complete Mathlib theorem read at FiniteType.lean:72-74.

Step 4 applies the same chart test with target atlas V to Y and source atlas U to X times_Y V; these are exactly the maps established earlier, not an arbitrary source cover. The locally finite-type map U to V gives the conclusion for a. All non-elementary facts used in all four steps occur in the cited statements. citations.json contains a literal excerpt for every citation.

The two sec-trace-formula dependencies are declared generic tool uses in split_report.tool_uses. Their statements concern only algebraic-space fibre products and etale coverings; no trace or cohomological theorem is used, and the unit has no replacement for this elementary geometric infrastructure. The scheme input is already a Mathlib leaf. I checked that the local chart-test statement does not depend on this cancellation item, and the required server checks will check the complete dependency closure for cycles.

For small cases I checked X empty (the empty source atlas works), all three spaces empty, a or b an identity, and the scheme case (identity target charts recover the scheme theorem). Taking Y non-quasi-compact or b non-separated changes none of the chart-existence or cover hypotheses; no finite-type or separation claim is made for b. The important direction is cancellation of postcomposition, not descent along an arbitrary source map. Each step is below 2000 characters, and the full argument is about 2000 characters; no long step hides a separate assertion. I checked the delivery-errors B-E issues against the files: no new-node packaging or duplicate-clause problem, no unsupported tag citation, no use of a cited proof as a statement, no hidden separation or Noetherian assumption, and no SGA source. The correction made during this review was to explicitly verify the U to X_W cover, which a loose compatible-chart proof could miss.
