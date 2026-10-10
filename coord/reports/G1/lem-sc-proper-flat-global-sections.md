1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-proper-flat-global-sections.json`: statement, split proof, 0 Mathlib leaves.
- `dag/nodes/sec-abelian-varieties/lem-sc-proper-flat-global-sections-criterion.json`: statement-only child, no Mathlib leaf.
- `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. The item was not already stated by a sorry-free Lean declaration. The source proof is a direct reduction to the preceding Stacks criterion (Tag 36.32.5/0E0K), followed by the field fibre calculation (Varieties Tag 33.9.3). I searched the whole DAG for 0E0L, the fibrewise global-sections statement, and pushforward terminology; the existing `lem-pc-h0-geom-connected` is the field-case result and is not a duplicate of this relative item. The new criterion node is strictly smaller: it assumes the residue-field H^0 condition and supplies universal pushforward, without any geometric-fibre hypothesis.

## Review by G1

I read the item source at Stacks Tag 0E0L and the existing field-case node `lem-pc-h0-geom-connected`. Step 1 cites the criterion for exactly its conclusion and cites the field-case statement for the fibre map; the hypotheses are checked by identifying each fibre as proper over its residue field and translating reduced and connected geometric fibres into geometric reducedness and geometric connectedness. That field-case node is declared as a generic off-unit tool use because this unit has no replacement for the fibre calculation. Step 2 takes only the criterion's stated pushforward and universal-base-change conclusion. I also read the new criterion statement and verified that it introduces the morphism, finite-presentation, fibre H^0 condition, and base-change conclusion independently. Required LeanFinder, Loogle, grep, and LeanSearch searches were run for both the item and the new node; LeanSearch was recorded unavailable, and no Mathlib declaration matched. Small cases checked: identity morphisms and a proper geometrically connected reduced scheme over a field reduce to the expected identity and $H^0=k$ statements.

5. Nothing remains unfinished; the sandbox is ready for the dry run.

## Second reading by G1

- Item statement: checked against Stacks Tag 0E0L, label `perfect-lemma-proper-flat-geom-red-connected`, hypothesis by hypothesis; proper, flat, finite presentation, geometrically reduced and connected fibres, and universal base change agree.
- Criterion node: checked against Stacks Tag 0E62, label `perfect-lemma-proper-flat-h0`; proper, flat, finite presentation, residue-field global-sections isomorphisms, and arbitrary base change agree.
- Item step 1: checked the criterion conclusion and the field-fibre calculation; the cited statements supply the pushforward, geometric-reduced/connected translation, and residue-field $H^0$ isomorphism.
- Item step 2: checked that it uses only the criterion's stated pushforward and arbitrary-base-change conclusion; no unstated proof detail is used.
- New-node form: both nodes are statement-only, self-contained, use definition-node references, and have tag-and-label sources; no Mathlib leaf matches the searches recorded in `searches.jsonl`.
- Small cases: identity morphisms and proper geometrically connected reduced schemes over a field give the expected identity and $H^0=k$; the empty scheme is excluded because geometric connectedness is defined to include nonemptiness; field and zero-section cases introduce no exception.

Changes made:

- Corrected the criterion source from the unrelated Tag 0E0K to Tag 0E62 (`perfect-lemma-proper-flat-h0`) in the node metadata.
- Corrected item proof and origin metadata to use Tag 0E0L's label rather than unstable lemma-number references.
- Added `def-pc-geometrically-irreducible` to the item statement and fibre-verification dependencies, and cited it verbatim in `citations.json`.
