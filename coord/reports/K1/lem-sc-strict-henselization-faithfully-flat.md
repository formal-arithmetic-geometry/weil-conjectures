Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-faithfully-flat.json`: item split into three proof steps; no new nodes; existing Mathlib leaves reused through their DAG nodes.
- `citations.json`: verbatim statement excerpts for every cited node and step.

Attachments: none.

WANTED: none.

The item was unsplit and had no exact declaration in the slopmaster2 source. Its statement agrees with More on Algebra, Tag 07QM, part (1), including the local-ring and separable-closure setup. The proof uses the existing strict-henselization triples node rather than restating its construction. No new node was created because each remaining fact is already stated by an existing DAG node: étale algebras are flat, filtered colimits of flat modules are flat, and flat local maps are faithfully flat.

## Review by K1

I read the item and its neighbouring strict-henselization nodes, especially `lem-sc-strict-henselization-dvr` and `lem-sc-strict-henselization-noetherian`, and checked their cited statements. Step 1 uses the triples statement that the filtered colimit is the strict henselization of the localization; because the item assumes that `R` is local, its maximal ideal is the prime used in that statement, so the localization is `R` itself. Step 2 uses exactly the triples statement's filtered colimit of etale `R`-algebras, the existing etale-flatness leaf, and the existing filtered-colimit-flatness lemma. Step 3 uses the triples statement's locality and maximal-ideal contraction, followed by the existing flat-local-faithfully-flat leaf; all hypotheses are present after Step 2. I checked the small case of a field `R`, where the strict henselization is a separable closure and the map is a field extension, hence faithfully flat. The Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder found only the generic local-flat criterion, Loogle and grep found no strict-henselization declaration, and LeanSearch was unavailable. No duplicate node or source error was found.

What could not be finished: none.

## Second reading by K1

- Item statement: checked against More on Algebra Tag 07QM, part (1), including the local-ring, residue-field, separable-closure, and canonical-map hypotheses; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against the statement of `lem-weil-pbc-strict-henselization-triples` and Algebra Tags 04GP/04GW; the maximal ideal of a local ring is the chosen prime, so the colimit and canonical map are identified; verdict: valid.
- Step 2: checked against the statements of `lem-weil-pbc-strict-henselization-triples`, `lem-weil-pbc-etale-algebra-flat`, and `lem-weil-pbc-filtered-colimit-flat-modules`; every diagram object is etale over R and the colimit is the stated filtered module colimit; verdict: valid.
- Step 3: checked against the triples node's locality and contraction clause and `lem-pc-local-flat-faithful-flat-reflects-surjective`; flatness from Step 2 and localness of both rings meet the criterion; verdict: valid.
- New nodes: none; all auxiliary facts are existing DAG statements, with no duplicate or Mathlib omission.
- Small cases: a field gives a separable field extension, and the identity map for a separably closed residue field is faithfully flat; the zero ring is excluded by the field/residue-field hypotheses.
- Changes: corrected the 07QM source label from the erroneous “lemma-dumb-properties-henselization” to “lemma-henselization-properties” and corrected `created.item` to this delivered item.
