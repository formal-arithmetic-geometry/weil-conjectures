# Q124: lem-sfb-space-module-flat-arbitrary-charts

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-module-flat-arbitrary-charts.json`: item, statement; split into four proof steps, not a Mathlib leaf.
- `citations.json`: eleven verbatim statement excerpts for all proof-step citations.
- No new nodes; no new Mathlib leaves. `searches.jsonl` contains the actual searches; `prepare.py` is a sandbox-only preparation helper.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, flatness/chart words, and geometric-stalk flatness. No declaration states this arbitrary-algebraic-space, quasi-coherent-module result. The scheme morphism declarations returned by the searches concern the structure sheaf and do not cover the item's general module or algebraic-space target.

## WANTED

None. All mathematical sources used below are present locally.

## Corrections and provenance

The statement is unchanged and is faithful to Stacks Tag 05VU (`spaces-morphisms.tex`, `lemma-flat-at-point`). Its proof begins with an arbitrary compatible diagram, so its ordinary-stalk condition is equivalent to one fixed geometric-stalk condition for every diagram, even when the source chart is not surjective. The imported node had no proof. Its existing Mathlib searches were retained in substance by running their applicable queries under Q124; the JSON records only the searches actually run in this sandbox, using their logged queries and results. LeanFinder was tried with two phrasings. LeanSearch and Loogle were available. Read the returned Flat.iff_flat_stalkMap and stalkMap in Mathlib/AlgebraicGeometry/Morphisms/Flat.lean, and the etale/flat characterization in Morphisms/Etale.lean; these concern scheme morphisms, not this statement.

Whole-DAG tag and keyword searches found the existing scheme-target chart-independence and atlas-test nodes, and all the ring and stalk tools needed here. Their scheme-target hypotheses do not cover an arbitrary algebraic-space Y; I reused their supporting nodes, not their conclusions. No new node is necessary. Whole-blueprint searches `05VU`, `chart flat` and `flatness` found no exact duplicate; `ancestor` reports None, matching the item's inherited null `from.node`. I retained that maintainer-owned provenance and its specified `from.place`, and explained it in split_report.blueprint. Read the newest `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, as well as the recorded unit and chapter. This auxiliary chart comparison does not alter their route. No unit realization fields belong to this non-key item.

Two off-unit ring facts are declared as generic tools in split_report.tool_uses: `lem-sc-strict-henselization-faithfully-flat` and `lem-trf-flatness-faithfully-flat-extension`. They implement exactly the source's local-ring argument; no same-unit statement replaces them. No maintainer `tool_uses` field was set.

## Not duplicates

No new nodes were created. The scheme-target result `lem-sfb-space-module-flat-point-chart-independence` assumes T is a scheme, while this item allows an algebraic-space target and varying etale target charts. The atlas-wide result `lem-sfb-space-module-flat-chart-test` likewise assumes a scheme target and tests all points of one surjective atlas. Neither can replace this item's full arbitrary-target statement directly.

## Review by Q124

I read the entire statement and proof of 05VU in spaces-morphisms.tex. I also read its actual inputs: spaces-properties.tex Tag 05VN (`lemma-geometric-lift-to-usual`), Tag 04KF (`lemma-describe-etale-local-ring`), Tag 05VP (`lemma-stalk-quasi-coherent`); algebra.tex Tag 0584 (`lemma-flatness-descends-more-general`), part (2); more-algebra.tex Tag 07QM (`lemma-dumb-properties-henselization`), part (1); and flat.tex Tag 05VL (`lemma-flat-up-down-henselization`), including the equivalence (1) and (3). The compatible-atlas existence clause was checked against spaces.tex Tag 02X1 (`lemma-lift-morphism-presentations`). There are no new-node sources to audit.

For step 1 I opened each cited node. `def-trf-algebraic-space` supplies the target atlas and defines scheme-test surjectivity. The exact final existence sentence of `lem-sfb-unramified-etale-compatible-charts` supplies a compatible surjective source atlas for the prescribed target atlas; its unramifiedness/etaleness test is not being applied to f. `def-a1-space-point-topology` supplies field-valued representatives. Base changing the source atlas by one gives a nonempty scheme by the stated definition of surjectivity, hence an ordinary point over x. `def-weil-algebraic-closure` explicitly asserts existence of an algebraic closure, and `def-weil-geometric-point` identifies the residue-field embedding with a geometric point. Thus both the compatible chart witness and a fixed geometric representative are actually available; neither is inferred merely from a vacuous universal condition.

For step 2 the statement of `lem-sfb-etale-geometric-point-specified-lift` explicitly lifts the fixed geometric point at the specified u over x, over the same algebraically closed field. The hypotheses hold because a is representable etale. `lem-sfb-space-strict-local-flatness` explicitly identifies each chart stalk with the appropriate strict henselization; I use only that clause for a and b, not its morphism-flatness equivalence. `lem-sfb-space-quasicoherent-geometric-stalk-tensor` states precisely the tensor isomorphism for the Zariski module corresponding to a^*M. Its quasi-coherence and scheme-chart hypotheses are present. I wrote out why its scalar action through R agrees with the one through the fixed geometric target stalk: fa=bh identifies pulled-back germs, and the stated tensor map multiplies those germs. There is no unexplained comparison or assumed flatness of f.

For step 3 the strict henselizations are those with residue embeddings furnished by the chosen geometric points, as required by the faithful-flatness node. `lem-trf-flatness-faithfully-flat-extension` explicitly allows any chain R to B to C with C faithfully flat over B and any B-module N, so it applies without R to B flat. It reflects flatness over the original R, not automatically over a new base ring. The subsequent change from R to R^sh uses the separate precise equivalence in `lem-sfb-strict-henselization-module-flatness`, valid for every module already carrying an R^sh-action. This action is provided by step 2. Tensor symmetry is given by its explicit inverse formula. Consequently the criterion on the right refers to the same fixed geometric points for every source and target chart.

Step 4 is only the quantifier argument using steps 1 and 3. I checked the zero module (both flatness tests hold), a chart missing x (no contribution to the universal quantifier), the empty source (no x), non-surjective charts containing x (05VN still applies), and arbitrary non-Noetherian local rings (0584, 07QM and 05VL require no Noetherian or finiteness assumptions). If the arbitrary module is nonflat, step 3 makes every chart test fail, so neither direction accidentally assumes flatness. No new statements need small-case testing. All step lengths are under 2000 characters; no sublemma has been hidden in a long step.

I checked delivery-errors B1--B10, C1--C8, D1--D5 and E1--E7 against the node and sources: statements and notions are introduced, citations quote statements rather than proofs, every non-elementary input is a node, no new restatement/elementary/duplicate nodes were made, and no statement/source repair was needed. `citations.json` was checked by exact substring comparisons against the live cited statements. Only the final quantifier step is marked elementary. The item proof dependencies are exactly the union of step uses. No Lean was written or compiled and no repository file was modified.

## Unfinished work

None in this stage-1 split. The reused dependency statements remain separate items wherever they are not yet proved in Lean. Required server dry-run validation and direct delivery are performed after this report is written.
