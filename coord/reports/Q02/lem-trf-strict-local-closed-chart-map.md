# Worker report: lem-trf-strict-local-closed-chart-map

## Files written

- dag/nodes/sec-trace-formula/lem-trf-strict-local-closed-chart-map.json: statement, split into four steps; no Mathlib match.
- citations.json: verbatim excerpts for every cited node at every step.
- report.md: this report. searches.jsonl is the unmodified search-command log.

New nodes: 0. Mathlib leaves: 0. No unit record is changed: the item is not the unit key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, strict-local closed-chart terminology and strict-henselization comparisons. The existing strict-henselization structural-map and functoriality declarations cover tools, not this entire simultaneous closed-quotient-chart statement; no exact project declaration was found. Nothing was compiled or written in the source trees.

## WANTED

None. All sources used are present.

## Findings and changes

The imported statement is retained verbatim. Its canonical map is the already specified map of lem-weil-pbc-strict-henselization-functoriality(3); no arbitrary map between independently chosen strict henselizations is substituted. The proof now establishes the chart square for that actual map before making the quotient. The quotient is only proved local here; its being an isomorphism with D is deliberately the parent's subsequent argument.

Existing nodes supply all non-elementary facts. In particular, lem-exc-affine-strict-local-ring-comparison supplies both the structure-map equation and agreement with geometric evaluation, whereas lem-sbc-geometric-strict-henselization-local-presentation supplies only an existential residue closure and would not by itself give the prescribed K. The more general affine comparison is reused, not duplicated. No source error or statement dispute was found.

Read the latest blueprint's lem-trf-local-term-locality.md and .proof.md, and sk-i-curve-zero/_section.md, together with the DAG chapter and unit records. The current proof follows the normal-cone/Varshavsky route. This item is a generic chart tool below the existing closed-image reduction chain, and does not replace a unit step or change the chapter route. Its inherited exact blueprint origin and via chain are retained; same_as remains empty after the whole-blueprint searches.

The search command was run for this item with LeanFinder (two different formulations), Loogle, grep and LeanSearch. The actual results are appended to the existing historical searches and match searches.jsonl. Closed-immersion quotient spectra, ordinary localizations and residue-map naturality are not the asserted comparison of geometric and algebraic strict henselizations. The strict-henselization grep had no Mathlib hits. The two semantic formulations gave no match; no service was unavailable in this run. DAG searches included tags 04HX and 04GU and strict-henselization/chart keywords; blueprint_refs ancestor and searches for strict henselization, quotient and local ring were read.

## Not duplicates

No new nodes are created. The existing lem-exc-affine-strict-local-ring-comparison is used twice with different scheme/chart inputs, not copied into another node. Existing triples, functoriality, localization and unit-criterion nodes are reused.

## Review by Q02

I read etale-cohomology.tex Tag 04HX (lemma-describe-etale-local-ring) including its affine-neighbourhood/triples proof, and the canonical functorial square after Tag 03PS. I read algebra.tex Tag 04GU (lemma-strictly-henselian-functorial), Tag 04GW (lemma-strict-henselization-different), Tag 04GP (lemma-strict-henselization), Tag 00CP (proposition-universal-property-localization) and Tag 00E9 (lemma-characterize-local-ring), checking tags against tags/tags. These sources give the specified separable closure, not all of Omega; Omega may contain transcendental or inseparable elements over the residue field.

Step 1 uses the statement of lem-weil-pbc-strict-henselization-triples for existence of algebraic strict henselizations relative to the chosen K. I checked its hypotheses with the local rings R and S and their maximal ideals, and used the already specified common residue field. The statement of lem-exc-affine-strict-local-ring-comparison was opened: it explicitly gives the chart-algebra isomorphism, structural-map equation, strict henselian locality and compatibility of the residue map with geometric evaluation. These are exactly what is needed at both W and Z. The closed immersion hypothesis makes the second open chart affine of the stipulated quotient form, with the given point in it. The statement of def-sc-ring-strict-henselization describes an algebraic strict henselization as an isomorphic colimit vertex, so transporting its universal cocone along that comparison suffices. Locality of R-to-C and S-to-D follows by taking kernels of their explicit composites to K; no extra finite-type or Noetherian hypothesis is used.

Step 2 uses precisely clause (3) of lem-weil-pbc-strict-henselization-functoriality: the structural square for the specified u, locality and the inclusion of the prescribed residue subfields. The two subfields are the same K for this closed immersion. I opened def-weil-open-immersion and def-weil-affine-spectrum: factorization into an open subscheme is unique and affine morphisms have unique corresponding ring maps. These statements turn that square into equality on A. The statement of lem-weil-pbc-ring-localization-universal-property explicitly gives uniqueness after precomposition from A. All denominators outside p are units in both chart-local structures from Step 1. The written fraction formula therefore proves equality on R, including its compatibility with the quotient S structure; it is not an unsupported claim of naturality.

Step 3 uses only the equality from Step 2 and elementary ideal/quotient arithmetic. I checked annihilation on finite sums of generators, wrote the formula for the induced S action, and checked both independence of representatives and the algebra equation for bar-u. Surjectivity of q gives uniqueness directly. This is two elementary ideal calculations, not a new non-elementary theorem to queue.

Step 4 uses the statement of lem-weil-pbc-local-ring-unit-criterion only for the implication from outside the maximal ideal to a unit. All other assertions are proved in the text: locality of u gives its maximal-ideal inverse image, IC is proper, the proposed quotient maximal ideal has field quotient, elements outside it are units, and the final inverse-image equality is checked on a representative q(c). Thus no theorem about quotients of strict henselizations or their isomorphism to D is being used circularly. Citations.json contains literal excerpts of the statement of every node used; no step relies on a cited node's internal proof.

For the B--E review, there are no new node statements or unsearched leaves, no duplicate or clause moved into a new node, and no hidden long comparison step: the four step texts are each below 2000 characters. The retained statement was tested at I=0 (the identity closed immersion), for a nonzero nilpotent closed thickening, for a field chart, and at a nonclosed prime. It needs neither radical I nor a closed point of W. I also checked a non-Noetherian ring: no finite generation is used in the ideal calculations, since membership in an ideal generated by I always means a finite sum. I=A would contradict the chosen geometric point of Z and is not an omitted case. For Omega larger than K the evaluation clauses still identify the image with K, so no unjustified identification with all of Omega enters. I corrected no statement; the work replaced an empty proof by this assembly and explicit calculations. Off-unit general results are declared as tool uses in split_report for independent review.

## Unfinished work

None for this one-level split. Existing dependencies keep their own stage statuses; no proof of those items is claimed here. Required server dry run and push results follow below.
