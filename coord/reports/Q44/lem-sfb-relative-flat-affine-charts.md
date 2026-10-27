# Worker report: lem-sfb-relative-flat-affine-charts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-flat-affine-charts.json: item split into five complete steps, unchanged statement, no new nodes and no new Mathlib leaves.
- citations.json: twelve verbatim statement quotations covering every step citation.
- searches.jsonl: the required search command's own records, retained without alteration.
- report.md: this report.

## Attachments

None for the item. The project search for the exact blueprint tag and related flat-locus/chart terminology did not find a declaration stating all its clauses. In particular, PolynomialChartStalkFlatComparisonForward.lean has private affine flat-locus lemmas but no theorem constructing the compatible triple of charts. The already attached AlgebraicGeometry.locallyOfFinitePresentation_of_comp belongs to lem-a1-map-over-base-finite-presentation, not to this item; I read its theorem at WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:53.

## WANTED

None.

## Corrections and route

The imported item is true and needs no statement change. It previously had no proof. I retained its statement, citations and recorded searches, added only searches actually run by msearch.py, and wrote the proof from existing DAG lemmas. The local sandbox had no previous item or report. There is no released repair note for the item.

Read GOAL.md, the chapter and unit records, the three-level rules of SETUP.md, stages/1-dag.md, worker brief and delivery-errors B–E in full. I also read the current latest blueprint direct-images proof: clause (3) provides the surrounding unit context. The inherited detailed route passes through the relative flat locus and Stacks 05VJ. blueprint_refs.py ancestor reports the inherited nearest ancestor as None; I preserve that inherited null rather than invent an ancestry. No chapter/unit route or target has been changed. No SGA source is used.

Whole-DAG statement and title searches found all the needed existing nodes. In particular, 02FV is already lem-a1-map-over-base-finite-presentation; 00RC is lem-weil-pbc-openness-of-flatness; 00HT(2) is lem-weil-pbc-flat-over-localization; all-affine-pair finiteness and affine-open stalk localizations also already have nodes. No duplicate nodes are introduced. Whole-blueprint searches for flat locus and stalk localization gave no matching blueprint node; the broader flat search was also read. There is no need to create a clause of the item as a separate node.

Mathlib searches used leanfinder, loogle, grep and leansearch, then a second natural-language phrasing. All returned successfully. I read the relevant affine-pair finite-presentation and finite-type declarations in Mathlib. They supply parts of the proof, while UniversallyOpen.of_flat assumes an everywhere-flat map and proves a different openness assertion. None gives the whole item's compatible charts, localized stalk map and pointwise flat locus. The original searches are preserved; the new records are exactly the successful command log entries.

## Not duplicates

No new nodes. The split reuses existing nodes instead of introducing equivalent statements or special cases.

## Review by Q44

I read more-morphisms.tex Tag 05VJ (lemma-base-change-criterion-flatness-fibre), especially the first two proof sentences: finite-presentation cancellation and openness are independent of the later relative-flatness/base-change argument. Its source assumes flatness over S for the base-change clause, which this item does not assert. I verified separately the facts actually needed: morphisms.tex Tag 02FV(1), 01T2 and 01TQ; schemes.tex 01IT and 01HV; algebra.tex 00RC and 00HT(2). No new node requires a source review.

Step 1 uses the statement of lem-weil-pbc-affine-opens-basis three times, each inside an open containing the specified point. It never assumes an intersection of affine opens is affine. def-weil-affine-spectrum supplies the affine coordinate dictionary; def-weil-locally-ringed-space-morphism supplies restriction compatibility and composition. The equation q f = p identifies the composite ring map. These are direct instances of the cited statements and definitions.

Step 2 uses lem-a1-map-over-base-finite-presentation with exactly the item's lfp source and lft target hypotheses. It then uses lem-weil-pbc-lft-affine-pairs for q on (V,W) and lem-weil-pbc-lfp-affine-opens-finite-presentation for p on (Z,W) and f on (Z,V). I opened each node and verified that its statement applies to every affine pair with the image containment, so no unsupported strengthening from an existence chart definition is being made. No Noetherian, separatedness or quasi-compactness hypothesis is inserted.

Step 3 uses lem-weil-pbc-affine-open-stalk-localization for both chosen affine opens. Its statement gives the fraction-to-germ isomorphism and open-immersion compatibility. The sheaf-morphism definition gives the image of each germ; the proof explicitly calculates b/t mapping to phi(b)/phi(t), rather than claiming an unproved transport. The inverse-image prime comes from the spectrum map, and denominators remain outside the source prime. This is a short fraction calculation using the cited statements, not a new comparison lemma.

Step 4 uses exactly the statement of lem-weil-pbc-openness-of-flatness with base B, algebra C and module C. Step 2 gives finite presentation of the algebra. The module is free of rank one over C, with its finite presentation written out in the step. The theorem's locus is precisely the defined E, with flatness over B, so it does not secretly require p flat.

Step 5 uses lem-weil-pbc-flat-over-localization, whose statement explicitly gives equivalence of flatness over a localized base and over the original base. Here C_r is a B_b-module because each element of B outside b maps outside r and hence to a unit. Its restricted B-action is the action in E. def-weil-flat-morphism defines flatness at z using the two stalks already identified in step 3. This proves both directions of the locus equality without confusing B-flatness with flatness over an unrelated ring.

I tested the statement with X empty (the pointwise existence clause is vacuous), with p=q=f the identity, and with the nonflat closed immersion Spec(Z/2) -> Spec Z (S=Y=Spec Z, q identity). In the last case all charts may be the whole affines, C is finitely presented over A=B=Z, and E is empty and open; this checks that p need not be flat. The proof allows arbitrary non-Noetherian bases and makes no assumption that a prime is maximal. Denominator calculations work for every prime, including generic points. No statement dispute was found.

I checked delivery-errors B–E against the final node and sources: there are no new unsplit nodes, no uncited non-elementary inputs, no circular reference, no item-clause relabelling, and no hidden long step. Every step is below 2000 characters. Every quote in citations.json is a verbatim substring of the corresponding current node statement. The openness theorem is recorded as an off-unit generic tool in split_report.tool_uses; the other off-unit facts are Mathlib leaves or Lean-closed nodes. There is no claim that a definition node proves a theorem.

## Unfinished work

None in this stage-1 split. Stage 2 and Lean proofs are outside the authorized task. Required server dry run and delivery follow this signed self-review.
