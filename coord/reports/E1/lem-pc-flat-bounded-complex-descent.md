1. Files written:
   - `dag/nodes/sec-picard-framework/lem-pc-flat-bounded-complex-descent.json`: split item with three proof steps.
   - `dag/nodes/sec-picard-framework/lem-pc-fp-complex-descent.json`: statement-only prerequisite; Mathlib no-match.
   - `dag/nodes/sec-picard-framework/lem-pc-flat-module-descent.json`: statement-only prerequisite; Mathlib no-match.
   - `citations.json`: exact statement quotations for every cited step.
2. Attachments: none. A search of the project Lean source by item id and by the relevant geometric keywords found no exact sorry-free declaration.
3. WANTED: none.
4. The imported item had no proof. I checked `lem-pc-noetherian-approximation-data` and the combined finite-flat-proper-support node to confirm that this item is the bounded flat-complex component. I avoided duplicating the combined node by introducing two strictly narrower statement-only prerequisites: finite-presentation descent for the finite complex data without flatness, and eventual flatness descent for one finitely presented module. The item proof applies the first to all terms, maps, and relations, applies the second termwise, and then uses directedness to take a common stage; base change preserves the differentials and the identification. Each cited node was read in full and its quoted clause supplies exactly what the corresponding step uses. Zero and one-term complexes are valid edge cases; the finite-term common-stage argument still applies.
5. What I could not finish: no Lean proof is written at stage 1; the two prerequisite nodes are intentionally unsplit statement inputs.

## Review by E1
I read the target node, its parent `lem-pc-noetherian-approximation-data`, and the neighboring combined finite-flat-proper-support node. I verified that the target hypotheses provide the directed affine inverse system, the finitely presented scheme, and a bounded finite-presentation complex. Step 1 cites `lem-pc-fp-complex-descent`, whose statement explicitly gives a bounded finitely presented complex and a base-change isomorphism. Step 2 cites `lem-pc-flat-module-descent`, whose statement explicitly gives eventual flatness and the base-change isomorphism for one finitely presented term; I checked that boundedness makes the set of terms finite, so one directed upper bound exists. Step 3 uses only the two quoted preservation clauses and the elementary fact that base change preserves the complex maps and finite range. I searched the DAG and blueprint for both narrower assertions and found no duplicate. The Mathlib searches were run for each new node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. The item and both new nodes carry the required blueprint references.

## Not duplicates
lem-pc-fp-complex-descent vs lem-pc-flat-bounded-complex-descent: the new node omits every flatness hypothesis and conclusion and only descends finite complex data.
lem-pc-flat-module-descent vs lem-pc-flat-bounded-complex-descent: the new node concerns one finitely presented module and omits bounded complexes, differentials, and simultaneous descent.
lem-pc-fp-complex-descent vs lem-pc-finite-flat-proper-support-descent: the new node omits flatness and proper-support conclusions and is only the finite-complex component.
lem-pc-flat-module-descent vs lem-pc-finite-flat-proper-support-descent: the new node concerns a single term and omits proper support and the complex structure.

## Second reading by E1
Checked the item statement against the Noetherian approximation route in Stacks Limits, Lemmas 32.10.2 and 32.10.4 (Tags 01ZR and 05LY): the directed affine inverse system, finitely presented scheme, bounded finitely presented complex, termwise flatness, and common later stage agree; zero and one-term complexes remain covered.
Checked node `lem-pc-fp-complex-descent` against the finite-presentation descent clause of Tags 01ZR and 05LY: its inverse-system, `X`, and `X_j` hypotheses are now stated explicitly and its conclusion is strictly narrower than the item.
Checked node `lem-pc-flat-module-descent` against the eventual-flatness clause of Tag 05LY: its inverse-system, `X`, and `X_j` hypotheses are now stated explicitly and its conclusion concerns one finitely presented module only.
Checked step 1: the cited finite-complex node supplies the bounded finitely presented model and base-change identification; no uncited geometric fact is used.
Checked step 2: the cited flat-module node supplies each term's eventual flatness; finite bounded degree range and directed common-stage selection are explicit, with zero terms handled.
Checked step 3: preservation of maps, boundedness, finite presentation, and the identification under base change is the elementary functoriality of the construction and matches the two cited clauses.
Checked B1--B7 and C1--C5 mechanically with `review_split.py`, including exact citation quotations, blueprint references, and recorded Mathlib searches; no Mathlib declaration states either prerequisite or the item.

Changes made: expanded both prerequisite statements to be self-contained (B2), corrected the item node's `created.item` ownership metadata (A4), updated the flat-module citation to quote its revised statement verbatim (Citations C1), and clarified zero terms in the finite-degree flatness step (E5).
