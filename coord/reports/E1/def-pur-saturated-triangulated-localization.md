# Stage 1 report: def-pur-saturated-triangulated-localization

## Files written

- `dag/nodes/sec-smooth-purity/def-pur-saturated-triangulated-localization.json`: existing definition marked `split`; no new nodes.
- `citations.json`: empty because the item is a definition and has no proof steps.

## Attachments

None. I searched the project source for the item id, its blueprint tag, and the relevant notions; no sorry-free project declaration states this definition exactly.

## WANTED

None.

## Review by E1

I read the item's source in `literature/stacks-project/categories.tex` and `derived.tex` at Categories Definition Tags 04VC (multiplicative systems) and 05Q8 (saturated multiplicative systems), Derived Categories Definition Tag 05R2, Situation Tag 05S8, and Definition Tag 05S9. The statement includes the MS1--MS3 multiplicative-system axioms, MS4 saturation, MS5--MS6 compatibility with the triangulated structure, the localization universal property, and the definition of pointwise existence of the left derived functor. The two external notions used by the statement are covered by the existing nodes `def-weil-triangulated-category` and `def-pc-essentially-constant-pro-diagram`; no new node was introduced and therefore there are no proof-step citations to quote.

I searched the whole DAG and blueprint for multiplicative systems, the cited Stacks tags, and essentially constant pro-diagrams. The only matching reusable notions were the two statement dependencies already present. I also searched the Lean source for the item id, blueprint tag, and relevant terms and found no exact declaration. The mandated Mathlib searches were run: LeanFinder returned triangulated-localization APIs but no MS1--MS6 definition, Loogle returned no hit and was unavailable for the requested identifier, grep returned no relevant declaration, and LeanSearch was unavailable; these results are recorded in the node. The definition is therefore split with no child nodes.

## Not duplicates

None: no existing node states the MS1--MS6/saturation/localization definition.

## What was wrong or corrected

Nothing in the statement required correction. The imported status was `unsplit`; I marked it `split`, filled the split report, and preserved its existing blueprint references and dependencies.

## What remains unfinished

Nothing.

## Second reading by E1

- Item statement: checked against Categories Definition Tags 04VC and 05Q8 and Derived Categories Tags 05R2, 05S8, and 05S9, hypothesis by hypothesis; verdict: correct after source-tag repair.
- New nodes: none; the definition has no child nodes to audit, and its two notion dependencies define the cited triangulated category and essentially constant pro-diagram.
- Proof steps: none; `proof` is empty and `citations.json` is correctly empty.
- Mathlib search metadata: the recorded LeanFinder, Loogle, grep, and LeanSearch searches are present in `searches.jsonl`; no exact Mathlib definition was found.
- Small cases: MS1--MS6 and the localization universal property are vacuous or reduce to the identity localization for the zero category; the pointwise derived-functor clause reduces to essential constancy of the singleton pro-diagram. No contradiction found.

Changed the source metadata and the corresponding review paragraph because the first reading cited 04VB and 04VD for definitions they do not contain: 04VB is the localization section and 04VD is the left-localization lemma. The correct definition tags are 04VC and 05Q8. The mathematical statement and dependency list were otherwise unchanged.
