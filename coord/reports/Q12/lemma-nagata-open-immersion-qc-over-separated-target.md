## Worker report

Files written:
- `dag/nodes/sec-nagata-compactification/lemma-nagata-open-immersion-qc-over-separated-target.json`: statement, now a Mathlib leaf; `AlgebraicGeometry.QuasiCompact.of_comp`, `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:250–252`.
- `citations.json`: empty list, because a Mathlib leaf has no proof steps.
- `report.md`: this report.

New nodes: 0. Mathlib leaves delivered: 1 (the item).

Attachments: none. I searched the project `lean/WeilConjectures/` for the exact blueprint id and for quasi-compactness/open-immersion/separated-target terms and `QuasiCompact.of_comp`. `Compactification/EliminationOfIndeterminacy.lean:74–81` explicitly says this helper is in Mathlib and is not restated in the project. Other hits apply the Mathlib lemma to particular situations and do not state the general item. Therefore this is a Mathlib delivery, not an ATTACH claim.

WANTED: none.

The imported node still had the old finite-type/separated/open-immersion statement, despite its `blueprint_update` carrying the current quasi-compact/quasi-separated cancellation statement. Its old proof used `lemma-nagata-finite-type-to-separated-target`; that dependency is unnecessary for the updated exact Mathlib match. The imported search had no recorded verdict and its Lean metadata had line 0; the verified Mathlib match now records lines 250–252. I retained the historical `lean` metadata and all blueprint/import fields.

Nothing remains unfinished for stage 1. No Lean was written, compiled, or built. Only the authorized sandbox was written.

## Statement corrected

This is adoption of the already recorded `blueprint_update`, not a disputed assertion. The main-20261015 node says that a quasi-compact composite with quasi-separated second leg forces the first leg quasi-compact; open immersion is only an optional final clause. I read `literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-closure/lemma-nagata-open-immersion-qc-over-separated-target.md` and both graph-factorization paragraphs recorded in `blueprint_update`. The new statement agrees verbatim in mathematical content, adding only definition-node references and making schemes explicit. The older assertion remains a special case. Both are true, so no counterexample or STATEMENT-DISPUTED is warranted.

The source is Stacks Tag 03GI, `literature/stacks-project/schemes.tex`, label `lemma-quasi-compact-permanence`. Its statement has exactly these two hypotheses, and its proof is the same graph/base-change factorization. No SGA source is used. The chapter and unit records were read; the unit is scheme-theoretic closure and compactification, and this helper supplies the needed quasi-compactness without changing that route.

## Searches and match

All four searches were executed through the required `msearch.py Q12 lemma-nagata-open-immersion-qc-over-separated-target` command and their returned hits were read. The exact queries and verdicts are in `mathlib_searches`, matching `searches.jsonl`. LeanFinder, Loogle, and LeanSearch all return `AlgebraicGeometry.QuasiCompact.of_comp`. The logged grep searched `AlgebraicGeometry/Morphisms/QuasiSeparated.lean` for `lemma of_comp|QuasiCompact.of_comp` and found line 250. I then read local source lines 246–252: the declaration quantifies arbitrary schemes X,Y,Z and morphisms f,g, assumes precisely `[QuasiCompact (f ≫ g)] [QuasiSeparated g]`, and concludes `QuasiCompact f`. Its proof is `MorphismProperty.of_postcomp`; no project-level sorry is involved. No second no-match search is needed because the first searches found an exact match.

I searched the whole DAG for `QuasiCompact.of_comp` and Tag 03GI, and the whole blueprint using `tools/blueprint_refs.py search 'quasi-compact'`, `'quasi-compact.*quasi-separated'`, `'quasi-compactness of an open'`, and `'finite-type to a separated'`. The broad search was read for relevant candidates; the item is the blueprint node stating this cancellation assertion. The regexp-like query is literal to that tool and returned none; it is not used as evidence of absence. `tools/blueprint_refs.py ancestor` returns the item itself. No new node was created, and `blueprint.same_as` is empty.

## Not duplicates

No new nodes were created. Existing nodes that use Tag 03GI or the same Mathlib declaration remain untouched; this delivery recognizes the assigned blueprint item as an existing Mathlib fact rather than introducing another copy.

## Review by Q12

I checked the current blueprint statement, its recorded updated graph proof, and Stacks Tag 03GI (`schemes.tex`, `lemma-quasi-compact-permanence`) against the item. For f:T→Y and g:Y→B, the triangle identifies the assumed T→B with f≫g. The two hypotheses of the Mathlib declaration at lines 250–252 are exactly quasi-compactness of that composite and quasi-separatedness of g. In particular, the proof needs neither a quasi-compact base B nor separatedness of g nor finite type of f. The final clause retains the supplied open immersion and adds the established quasi-compactness; it introduces no extra geometric fact. Thus every clause is an exact match or its one-line specialization, and the item has the required empty proof and proof_deps of a Mathlib leaf. There are no step citations or long proof steps to audit; `citations.json` is consequently empty.

I opened and read each of the four definition statements used in stmt_deps. `def-pc-scheme` supplies schemes and morphisms; `def-weil-finite-type-morphism` explicitly defines quasi-compact morphisms by inverse images of affine opens (I use that clause only, not finite type); `def-weil-quasi-separated-morphism` defines quasi-separatedness by the quasi-compact diagonal; `def-weil-open-immersion` defines identification with an open subscheme. These are existing notions, not claims extracted from the proof of another node. No new statement-only node, duplicate, elementary-lemma node, or restatement of a clause was introduced. The non-elementary graph argument is already the matched Mathlib theorem; it is not hidden in an elementary step.

For edge cases I checked the empty source, identity second leg, and the absence of any open-immersion assumption in the main assertion. Empty sources cause no nonemptiness requirement; g=id gives the same quasi-compactness hypothesis and conclusion; f need not be an immersion. The exact signature likewise allows arbitrary schemes with none of these excluded. The current statement and Stacks agree on all these cases. I corrected the stale imported statement and removed its obsolete finite-type route, as explicitly directed by blueprint_update, while retaining that update for the independent reviewer. The B–E review found no new-node source/definition fault, no uncited proof fact, no relabelled split, and no missing hypothesis. The only content change is the authorized current-blueprint update followed by recognition as a Mathlib leaf.

## Dry-run repairs

The first dry run rejected an empty proof_origin, including for this Mathlib leaf. I supplied the actual literature source: Stacks Tag 03GI, `schemes.tex`, label `lemma-quasi-compact-permanence`. This records the already read source; proof and proof_deps stay empty because the declaration is an exact match.
