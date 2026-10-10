Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-completion-flat.json`: split item; no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-sc-etale-triple-to-sh-completion-flat.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: verbatim proof-step citations.

Attachments: none.

WANTED: `literature/stacks-project/more-algebra.tex`, Tag 06LJ proof text is not present in this checkout; the source location is recorded from the imported node and existing Tag 06LJ splits.

The item had no matching sorry-free declaration in the Lean source. The existing completion-Noetherian node depends on this item, so citing it would create a cycle. I instead isolated the per-triple flatness assertion used by Tag 06LJ(c). The generic Noetherian-completion flatness result is already an existing Mathlib leaf node, while the strict-henselization-specific per-triple assertion is not in Mathlib.

## Review by E1

I read the item and its neighboring Tag 06LJ-derived nodes, especially `lem-sc-strict-henselization-completion-noetherian` and `lem-sc-strict-henselization-noetherian`, and checked the strict-henselization triple statement. Step 1 uses exactly the triple node's filtered-colimit, locality, and residue-field clauses. Step 2 uses the existing affine finite-presentation and finite-type-Noetherian statements; the hypotheses are that the triple map is etale and the base ring R is Noetherian. Step 3 cites the new supporting statement, whose conclusion is precisely flatness of each triple algebra into the completion. Step 4 uses the same filtered-colimit statement and the existing filtered-colimit flatness theorem to conclude flatness of C to its completion. I checked the dependency direction and removed the tempting citation to the completion-Noetherian sibling because that sibling cites this item. The Mathlib searches were run for the item and child with LeanFinder, Loogle, grep, and unavailable LeanSearch recorded as such; only ordinary `AdicCompletion.flat_of_isNoetherian` appeared, which does not state the strict-henselization result without an additional Noetherian hypothesis on C.

## Not duplicates

`lem-sc-etale-triple-to-sh-completion-flat` vs `lem-sc-strict-henselization-noetherian`: the former states flatness of each individual etale triple algebra into the strict-henselization completion, while the latter states the equivalence of Noetherianity of the base and the strict henselization.

`lem-sc-etale-triple-to-sh-completion-flat` vs `lem-sc-strict-henselization-completion-noetherian`: the former is the per-triple flatness input, while the latter concludes Noetherianity and faithful flatness of the completed strict henselization and depends on the delivered item.

`lem-sc-etale-triple-to-sh-completion-flat` vs `lem-weil-pbc-noetherian-completion-flat`: the former maps each etale triple algebra into the completion of a strict henselization, while the latter maps a ring to its own adic completion.

`lem-sc-etale-triple-to-sh-completion-flat` vs `lem-sc-strict-henselization-completion-flat`: the former is per triple algebra and strictly smaller; the latter concludes flatness for the colimit strict henselization.

## Second reading by E1

- Item statement: checked against Stacks Tag 06LJ, parts (a) and (c), including the Noetherian local hypothesis, maximal-ideal completion, and flatness conclusion; verdict: agrees.
- Supporting node `lem-sc-etale-triple-to-sh-completion-flat`: checked against Tag 06LJ(c), paragraph beginning “To finish the proof of (c)”; verdict: the per-triple auxiliary flatness assertion is the intended smaller fact and is self-contained through the strict-henselization triples node.
- Item step 1: checked against the filtered-colimit, local, maximal-ideal, and residue-field clauses of `lem-weil-pbc-strict-henselization-triples`; verdict: cited statement supplies each fact.
- Item step 2: checked against the etale finite-presentation and finite-type-Noetherian nodes, with R Noetherian and each triple algebra etale over R; verdict: hypotheses and conclusion match.
- Item step 3: checked against the supporting node and Tag 06LJ(c); verdict: repaired wording to use the auxiliary assertion directly and removed an unsupported derivation through an ordinary completion of S.
- Item step 4: checked against the filtered-colimit flatness node and the filtered-colimit clause of the triples node; verdict: every composite is supplied by the supporting node and the colimit criterion applies.
- Edge cases: the zero ring is excluded by the local-ring/maximal-ideal and residue-field hypotheses; for a field, m=0 and the completion is C, so the map is the identity; n=0 and n=1 completion quotients are consistent with the inverse-limit definition.
- Searches and duplication: searched existing nodes for strict-henselization completion and ordinary completion flatness; the generic Noetherian completion leaf is not the strict-henselization assertion, and no duplicate of the supporting node was found. Mathlib searches are recorded in `searches.jsonl`; no exact strict-henselization declaration was found.

Changes: rewrote item step 3 so it no longer claims the per-triple result follows from an unrecorded ordinary-completion identification; the source-specific identification remains packaged in the supporting node, exactly as used by Tag 06LJ.
