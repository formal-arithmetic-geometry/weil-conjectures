# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-rf-perfect-base-change.json`: statement item, split; no new nodes.
- `citations.json`: verbatim quotes for the cited statements in step 1.
- `report.md`: this report.

2. Attachments: none. No project declaration in `WeilConjectures/` states this item exactly; the source checkout search also found no declaration tagged `lem-pc-rf-perfect-base-change`.

3. WANTED: none. The cited Stacks source is present in the local literature index as `literature/stacks-tags-cited.tsv` entries 0A1H and 0B91; the full theorem is treated as the classical input recorded by the blueprint.

4. What was wrong or incomplete in the imported node: the item had no proof and its `blueprint.same_as` was null. I filled the proof and metadata. I did not create a child node: the only general perfectness fact is the item’s own Tag 0B91 conclusion, so a child for it would restate a clause of the item. The imported specialized projective-Noetherian lemma is not needed for the general proper finite-presentation statement.

## Review by H1

I read the target node, the unit record `dag/units/sk-thm-picard-semicon.json`, the blueprint proof text, and the Stacks tags recorded for 0A1H and 0B91. I also searched both project source checkouts for the item id and the relevant derived pushforward/perfectness terminology; no sorry-free exact declaration exists. Step 1 uses `def-weil-proper-morphism` only for the clauses it states, namely separatedness and finite type; finite type gives quasi-compactness in the morphism convention used by the existing base-change lemma. The sheaf hypotheses in the item give the quasi-coherent and relative-flat hypotheses of `lem-pc-rf-base-change-flat-module`, whose statement explicitly supplies the canonical arbitrary-base-change isomorphism. Step 2 records the remaining perfectness assertion as the classical theorem Tag 0B91, clause (2), with the same proper finite-presentation and finite-presentation/flat sheaf hypotheses. I checked small boundary cases conceptually: for an identity morphism the result reduces to the perfectness of a finite-presentation flat module and identity base change; for a proper family over a field it is the usual bounded finite-dimensional cohomology statement. Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; the first three found no derived direct-image perfectness theorem, and LeanSearch was unavailable, recorded as such.

5. What I could not finish: no independent decomposition of the classical Tag 0B91 perfectness proof was possible from the available blueprint without introducing a node that merely restates the target clause. The dry run is the remaining verification step.

## Second reading by H1

- Item statement: checked word for word against `perfect.tex` Tag 0B91, clause (2); the proper finite-presentation and finitely presented, relatively flat hypotheses agree. The zero sheaf, identity morphism, and proper scheme over a field satisfy the expected specializations.
- Step 1: checked `def-weil-proper-morphism` and the full statement of `lem-pc-rf-base-change-flat-module` against the hypotheses; valid. Proper implies separated and quasi-compact, and finite presentation of the sheaf gives quasi-coherence.
- Step 2: checked against the proof of Tag 0B91 and the statement of Tag 0A1H; repaired. Taking the perfect tensor factor to be the structure sheaf and the flat complex to be the sheaf in degree zero gives perfectness. Its support is closed by the existing finite-type support node and proper over the base by the closed-subset node. This step is not elementary.
- New node `lem-pc-proper-support-perfect-direct-image`: checked every hypothesis and conclusion against `perfect.tex` Tag 0A1H, label `lemma-base-change-tensor-perfect`; exact match. It is a genuine broader theorem, not a clause of the item; the cases of zero complex, empty scheme, and degree-zero complex agree. DAG, blueprint, Lean source and independent Mathlib searches found no duplicate or closed declaration.

Changes: added the unsplit Tag 0A1H node; replaced step 2's uncited assertion of the target by its explicit specialization; corrected `proof_deps`, source place, and the full verbatim citation quotes. The first reader's statement that no smaller auxiliary theorem exists is superseded by this Tag 0A1H node. The cross-unit support nodes are generic tools: they supply closed support and stability of proper support under passing to a closed subset, and no node of this unit states those facts.

## Not duplicates

lem-pc-proper-support-perfect-direct-image vs lem-pc-rf-perfect-base-change: the former is Tag 0A1H for arbitrary perfect $E$, bounded complexes of finitely presented modules and a finite-presentation morphism with proper support; the latter is Tag 0B91(2) for $E=\\mathcal O_X$, a single module in degree zero and a proper morphism. The former implies the perfectness clause only after the support argument in step 2; step 1 independently supplies the canonical base-change isomorphism.
