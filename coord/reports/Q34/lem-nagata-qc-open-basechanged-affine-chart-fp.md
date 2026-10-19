# Q34 stage-1 delivery: lem-nagata-qc-open-basechanged-affine-chart-fp

## Files written

- `dag/nodes/sec-nagata-compactification/lem-nagata-qc-open-basechanged-affine-chart-fp.json`: existing statement, now split into five proof steps. The statement and all nine statement dependencies are retained. Mathlib verdict: no exact or one-line match for the whole assertion; its generic ingredients are already Mathlib leaves in the DAG.
- `citations.json`: fourteen verbatim statement quotations, one for every node used in every proof step.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. `searches.jsonl` contains the actual command-generated search records; `write_split.py` is a sandbox-only preparation script.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id/blueprint tag, basechanged affine chart names, and finite-presentation/quasi-compact-open concepts. I read the relevant project extensions in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/{FinitePresentation,QuasiSeparated,QuasiCompact}.lean`. They provide cancellation, diagonal, topology and other generic ingredients, not this full assertion. No upstream sorry declaration is treated as a finished proof.

## WANTED

None: the source material needed here is present locally.

## Findings and changes

The imported statement is correct; there is no statement dispute or unit-route change. The empty proof has been replaced with the finite-presentation argument. The original source lists Tag 01TQ; for the affine chart, the pointwise definition 01TP already suffices, since the entire source and target are affine. The proof additionally spells out the local-isomorphism argument of 01TT. For quasi-compactness of the inclusion of W, it first proves that X_T is quasi-separated. Quasi-compactness of an open subset alone does not imply that its inclusion into an arbitrary scheme is quasi-compact.

I read `dag/chapters/sec-nagata-compactification.json`, `dag/units/sk-prop-nagata-sketch-approximation.json`, the ancestor node `lemma-nagata-relative-gluing-datum-descends`, and its current main-20261015 blueprint file. This item supplies precisely the ancestor's finite-presentation hypothesis for descending overlap maps; it does not replace the approximation route. It is not the unit's key node, so no unit realization record is changed. The existing blueprint ancestry and exact place are retained, `same_as` is checked and remains empty, and the split report identifies the ancestor proof input.

## Unfinished work

No mathematical gap remains in this one-level split. The delivery awaits the normal independent maintainer review. The first server dry run exited with a preflight failure on an unrelated, undelivered DAG file: `dag/nodes/sec-six-functors/lem-coef-terminal-local-kan-corepresentability.json` does not parse (`Extra data: line 261 column 2 (char 29703)`). The same parse error was confirmed by a read-only JSON parse of the shared reference file. That file is outside Q34's authorized write scope, so it was not modified. A second dry run also exited with exactly that unrelated parse failure. Both invocations exited before any push; no delivery invocation remains active. The completed five-step split and citations are retained here for resumption once the shared DAG JSON is repaired. Delivery status: BLOCKED by server preflight input corruption.

## Not duplicates

No new node was created, so there are no new/existing same-tag pairs. I searched the entire DAG by Tags 01TQ, 01TR, 01TS, 01TU, 01TT and 01L7 and by affine/qcqs/open-immersion/presentation statements. I ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for `finite presentation`, `open immersion`, `quasi-separated`, `01TT`, `01L3`, `01L7`, `open immersion is locally`, `basechanged`, `affine chart`, and `01TS`. Existing general results are cited, rather than specialized into new nodes. In particular, the separatedness of an open immersion comes from `lem-weil-pbc-separated-cancellation`, and separated implies quasi-separated from `lem-pc-separated-quasi-separated`.

## Mathlib searches

I retained the inherited NC searches and appended the genuine Q34 searches, with their exact query strings, from `searches.jsonl`. Q34 used LeanFinder twice with different formulations, Loogle, LeanSearch and grep. The returned local-finite-presentation statements do not alone prove the compact-open inclusion is quasi-compact or give the full base-changed chart assertion. I read Mathlib `Morphisms/FinitePresentation.lean:45-100`, `Morphisms/QuasiSeparated.lean:50-168,233-258` and `Morphisms/Separated.lean:45-119`, including the open-immersion, composition and pullback instances. No new leaf is needed. The wrapper's two single-file grep calls parsed rg line prefixes as file names; their records are preserved literally, and a subsequent directory grep gave proper file paths and lines for the relevant declarations. No unavailable service has been labelled a negative search result.

## Review by Q34

I read the local Stacks source `morphisms.tex`, labels `definition-finite-presentation` (01TP), `lemma-locally-finite-presentation-characterize` (01TQ), `lemma-composition-finite-presentation` (01TR), `lemma-base-change-finite-presentation` (01TS), `lemma-open-immersion-locally-finite-presentation` (01TT), and `lemma-quasi-compact-open-immersion-finite-presentation` (01TU). I also read `schemes.tex`, labels `lemma-basis-affine-opens` (01IT), `lemma-immersions-monomorphisms` (01L7), `lemma-compose-after-separated` (01KV), and `lemma-quasi-compact-permanence` (03GI). No SGA route or source is used. There are no new nodes needing separate source verification.

For Step 1 I opened the statements of `def-weil-open-immersion`, `lem-weil-pbc-affine-opens-basis`, `def-weil-pbc-finitely-presented-algebra`, and `def-sbc-locally-finite-presentation`. The first identifies an open immersion with its open image and restricted structure sheaf; the basis theorem supplies an affine neighbourhood inside that image. On it the restricted morphism is the identity. The two definitions then give the zero-variable, zero-relation finite presentation at the chosen point. This is the complete elementary argument underlying the local-isomorphism proof in 01TT; it introduces no additional lemma node.

For Step 2 I read `lem-weil-pbc-affine-scheme-qcqs`, `def-weil-affine-spectrum`, the local-finite-presentation definition and clause (1) of `lem-weil-pbc-qcqs-morphism-permanence`. The spectrum definition specifies global sections, the source/target are exactly Spec B and Spec A, and the given algebra map has precisely the presentation needed by the pointwise definition. The cited affine-qcqs statement gives both compactness and quasi-separatedness. The last cited statement explicitly says that an affine-source, locally finitely presented morphism to a quasi-separated target is finitely presented, with no Noetherian hypothesis.

For Step 3 I read every clause used in `lem-weil-pbc-qcqs-morphism-permanence` and clause (d) of `lem-weil-pbc-proper-fp-permanence`. Clause (1) applies to V -> S because V is qcqs and S is quasi-separated. Clause (d) then composes the two finitely presented maps. Clause (3) permits base change along any t, so no affineness or finite-type hypothesis on t is introduced. Clause (2) makes X_T quasi-separated because its projection is quasi-separated and T is quasi-separated. The hypotheses S,T qcqs from the item are sufficient at each application.

For Step 4 I read clause (a) of `lem-weil-pbc-separated-cancellation`, the full statement of `lem-pc-separated-quasi-separated`, and clause (1) of the qcqs-permanence node. They respectively give separatedness of the open immersion, quasi-separatedness from separatedness, and quasi-compactness from the compact source W and the now quasi-separated target X_T. All three finite-presentation conditions have therefore been proved for i. For Step 5 I again checked that clause (d) of the proper/fp permanence node states finite-presentation composition itself, including quasi-separatedness. Thus its conclusion is exactly the map and all three clauses requested by the item. Every used node is a Mathlib leaf or definition; none is a definition cited in place of a theorem, and no off-route unfinished theorem is used as a tool.

I checked delivery-errors B--E against the actual JSON and sources. The statement is unchanged and introduces all its objects; statement dependencies still define the notions it uses. No new statement-only node is needed, no clause is renamed into a node, and no proof argument is hidden behind a citation to a proof rather than a statement. All fourteen quotes are literal substrings of the statements read, and proof_deps is the exact union of uses. The ancestor is not cited as a proof dependency, so this does not create a back edge. All five steps are shorter than 2000 characters (maximum 821), and Step 1 is a routine local identity calculation, not a concealed non-elementary claim.

I tested the empty cases: W may be empty and its finite-presentation condition is vacuous locally; the compactness and separatedness lemmas still apply. B may be the zero algebra, with Spec B empty. The presentation allows zero generators and zero relations; no nonzero-ring convention is used. For W=X_T the same proof applies whenever the stated compactness hypothesis holds. Arbitrary t, non-affine T, non-Noetherian bases, and non-separated but quasi-separated S,T are all allowed; neither an intersection of affine opens being affine nor an open subset being affine is assumed. No correction to the item's statement was necessary.
