# def-pc-compact-object

Files written: `dag/nodes/sec-picard-framework/def-pc-compact-object.json` (definition, split; no new nodes), `citations.json` (empty because a definition has no proof steps).

Attachments: none. No project declaration under `WeilConjectures/` states this definition.

WANTED: `literature/stacks-project/derived.tex`, Tag 07LS, for `def-pc-compact-object`; the repository's literature checkout contains only its lists and import tools. I read the Stacks Project online at https://stacks.math.columbia.edu/tag/07LS.

The imported node incorrectly required a triangulated category, although Tag 07LS requires only an additive category. Its `stmt_deps` also cited the triangulated definition. I changed the hypothesis and cited the existing additive-category node, `def-weil-additive-category`. The imported TeX had doubled backslashes; the sandbox JSON has single TeX backslashes after JSON decoding. No other part of the definition changed.

No work remains for this split. There are no new nodes and no Mathlib leaves created.

## Review by H1

Stacks Definition 13.37.1, Tag 07LS, says that C is additive with arbitrary direct sums and that K is compact precisely when the canonical map from the direct sum of Hom groups to Hom into the direct sum is bijective for every indexed family. The sandbox statement carries each of these hypotheses and the full conclusion. I opened `def-weil-additive-category`: its statement defines the additive category used here, so the sole statement dependency says what the node needs. Arbitrary coproducts are an explicit hypothesis, not inferred from additivity.

There are no proof steps in a definition and therefore no step citations to audit under C1-C4. I checked the parent unit `sk-thm-picard-duality`, the blueprint search for `compact object`, the DAG's compact-object nodes, and the source checkout for an exact project declaration. No existing blueprint node or project declaration states this definition; the nearby compact-generation nodes use it. Searches through the required Mathlib command, in two phrasings, found finite-coproduct results and finitely presentable objects but no matching definition; LeanSearch returned an Internal Server Error and is recorded as unavailable. The empty and singleton index cases are consistent: the canonical map is respectively between zero groups and between one Hom group and itself. The correction was the additive-category hypothesis and its dependency; no new statement needed a small-case test.
## Second reading by H1

- Item statement: checked against Stacks Tag 07LS, Definition 13.37.1, hypothesis by hypothesis; verdict: agrees after replacing the triangulated-category dependency by the additive-category dependency.
- New nodes: none; there are no additional node statements or proof steps to audit.
- Mathlib searches: checked the recorded `leanfinder`, `loogle`, and `grep` searches and their unavailable/no-match verdicts; verdict: no exact Mathlib compact-object definition was found.
- Blueprint and DAG: searched the imported blueprint and existing DAG nodes; verdict: no duplicate blueprint or existing compact-object definition states this notion.
- Edge cases: checked empty and singleton index sets, plus zero and one-object families; verdict: the canonical map has the expected zero or identity form.
- Changed the statement dependency from `def-weil-triangulated-category` to `def-weil-additive-category` and removed the corresponding extra hypothesis because Tag 07LS assumes only an additive category with arbitrary direct sums.
- Kept `citations.json` empty because this is a definition node with no proof steps; the dry-run delivery preflight passes.
