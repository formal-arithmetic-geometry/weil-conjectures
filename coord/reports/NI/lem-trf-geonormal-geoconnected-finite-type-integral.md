# Stage-1 delivery: lem-trf-geonormal-geoconnected-finite-type-integral

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geonormal-geoconnected-finite-type-integral.json`: statement, now split; no Mathlib match for the complete geometric implication. The statement and its statement dependencies are unchanged.
- No new nodes and no new Mathlib leaves. `citations.json` supplies seven exact statement excerpts for the three proof steps.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and geometric normality/connected-normal combinations. No declaration states the complete item. The existing noetherian normal decomposition is already carried by `rem-pc-regular-normal`; the smooth-dimension declarations in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` do not state this item.

## WANTED

None. All sources used are available locally.

## Corrections and route

The unsplit item was mathematically correct. Its source really gives the component argument: Stacks `properties.tex`, Tag 033M, `lemma-normal-Noetherian`; the use after every extension is exactly the final geometric-irreducibility argument in `more-morphisms.tex`, Tag 057K, `lemma-local-local-structure-finite-type`. No statement correction or route departure was needed. The extra reducedness needed for integral rather than irreducible is already in the conclusion of the normal decomposition, so no separate reducedness lemma is hidden.

I read the chapter and unit records and the newest blueprint `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. This item serves the recorded downstream 057K ingredient of the inherited flatification route, not a replacement for any of the contracting-correspondence arguments of the ancestor. The generic 033M tool is declared in `split_report.tool_uses`.

## Searches and reuse

There was no earlier sandbox item, report or search log to preserve. I retained the item's inherited Mathlib-search records and appended the actual new searches logged by msearch.py. LeanFinder was run with two different phrasings; Loogle, LeanSearch and grep were also run. Hits give `IsIntegral`, the reduced-plus-irreducible criterion, and integral affine schemes, not the connected-normal implication. Read the candidate source context in the existing project and the exact statements recorded in the hits; none supplies the missing connected-to-irreducible step by a one-line specialization.

Before considering any new node, searched the whole DAG by source tag and connected/normal/Noetherian/component concepts, and the whole imported blueprint using `blueprint_refs.py search 033M`, `search 'normal connected'`, and `search 'normal scheme'`. This found the existing decomposition in clause (2) of `rem-pc-regular-normal`, so no decomposition node was created. It also found the weaker-topology node `lem-trf-normal-topologically-noetherian-components` and the etale component variants, all unnecessary here. The ancestor command confirms `lem-trf-local-term-locality`; the existing precise `blueprint.from.place` and via chain are retained, with `same_as: []`.

## Not duplicates

No new nodes. The Noetherian normal decomposition is reused as `rem-pc-regular-normal`, rather than restated. The item is not equivalent to the regular connected special case (clause (3)): it assumes geometric normality, not regularity, and must prove integrality for every extension.

## Review by NI

I read Stacks Tag 033M (`properties.tex`, `lemma-normal-Noetherian`) including its reduction to the locally finite irreducible-component statement, and the full connected-normal passage of Tag 057K in `more-morphisms.tex`. I also read the two finite-type lemmas in `morphisms.tex`: Tag 01T4 (`lemma-base-change-finite-type`) and Tag 01T6 (`lemma-finite-type-noetherian`), and the current blueprint statement/proof of `rem-pc-regular-normal` under `literature/blueprint/latest/`. There are no new-node sources to check.

Step 1 uses precisely clause (2) of `lem-sfb-finite-type-composition-base-change`: arbitrary base change preserves finite type, without any restriction on the extension degree or separatedness. `def-weil-finite-type-morphism` supplies local finite type and quasi-compactness of the whole source over an affine target. `pqf-def-locnoeth` supplies the one-affine-chart criterion for Spec K; its Noetherian ring hypothesis is proved inline because a field has only the two ideals. `pqf-lem-locnoeth-lft` then gives local Noetherianity of the source. Quasi-compact plus locally Noetherian is exactly the hypothesis used in clause (2) of the next citation. No stronger conclusion is taken from the local-only node.

Step 2 uses the normal-domain local rings supplied by the item's own hypothesis for this very extension K/k, and the Noetherianity just established, to meet every hypothesis of clause (2) of `rem-pc-regular-normal`. That clause explicitly states integral clopen components, not merely normality or irreducibility. The finite disjoint-union conclusion covers the whole scheme. `def-weil-connected-scheme` explicitly includes nonemptiness. Choosing one point selects a nonempty component, and its complement is clopen; the written two-piece connectedness argument forces that complement to be empty. This final argument is elementary, while the step is marked non-elementary because it applies the decomposition theorem. It never uses regularity from the other clauses of the cited node.

Step 3 uses the exact universal-field-extension definition in `def-pc-geometrically-irreducible`, whose statement defines geometric integrality as well as geometric irreducibility. Universal introduction over the arbitrary K is the entire elementary step. Every node citation has a verbatim excerpt in citations.json; I checked each excerpt against the actual node statement rather than its proof. No theorem is cited only as a document or definition.

For B1--B9 there are no new nodes to carry proof sketches, incomplete object introductions, missing notion dependencies, erroneous tags, or duplicate statements. For C1--C8 every non-elementary ingredient is an existing cited statement; the only off-unit non-leaf tool is declared. For D1--D5 the assembly proof contains the actual arbitrary-extension, Noetherianity and connected-component arguments; no clause is moved to a fresh node and no induction or circular dependency is used. Each proof step is below 2000 characters (732, 599, 192), so none conceals an extended inline lemma.

For E1--E7 I checked fields K of arbitrary characteristic and arbitrary transcendence degree: all are Noetherian, and 01T4 has no finite-extension hypothesis. The identity extension is included. Spec k, a normal connected zero-dimensional scheme, satisfies the conclusion. A disjoint pair of field spectra fails connectedness as required; a connected nodal union fails normal-domain stalks at the intersection. The empty scheme is excluded both by the explicit nonempty premise and by the connectedness convention, so choosing a point is justified. Purely inseparable extensions cause no exception because normality is assumed after every extension, not merely over k. No affine intersection, separatedness, smoothness, regularity or rational-point hypothesis is used.

The original item's proof was empty; I supplied the three steps and exact proof-dependency union, retained its metadata, and reused the existing nodes instead of creating a duplicate 033M lemma. No Lean was written or compiled, and the shared repository was only read.

## Unfinished work

None in the authorized one-level split. Existing cited non-leaf nodes remain their own stage-1 items; they were not edited.
