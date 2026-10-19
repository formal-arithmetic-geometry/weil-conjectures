# Stage 1 report: lem-coef-algebroid-equivalence-arrow-descent

## Files written

- `dag/nodes/sec-six-functors/lem-coef-algebroid-equivalence-arrow-descent.json`: existing statement completed with a four-step split; no new nodes; Mathlib searches found no match.
- `citations.json`: verbatim citations for every node used by every proof step.
- `searches.jsonl`: retained interrupted-turn searches and the completed second phrasings.

## Attachments

None. No finished declaration in the read-only slopmaster2 source states this item.

## WANTED

- WANTED: Gepner–Haugseng, arXiv:1312.3178v4, Theorem 5.6.2 and Lemmas 5.3.4–5.3.5, for the equivalence-arrow descent argument (the URL source was read but is not archived in `literature/`).
- WANTED: Lurie, *Higher Topos Theory*, Theorem 6.1.3.9, for cartesian geometric realization and fiberwise detection (the PDF source was read but is not archived in `literature/`).

## Problems and corrections

The repository node was unsplit and had an empty proof. I retained its statement, hypotheses, source, dependencies, and blueprint ancestry, then supplied the missing argument. The original node metadata recorded the creating item as `lem-coef-algebroid-completion`/Q40; I left that historical field unchanged. The proof uses only existing DAG statements: the algebroid definition, equivalence-nerve fiber and essential-surjectivity facts, and space geometric descent. No new node was needed and no duplicate was created. The required Mathlib searches returned only ordinary nerves, simplicial objects, and categorical pullbacks; none states this infinity-algebroid result.

## What remains unfinished

Nothing in the stage-1 split. No Lean files were written and no compiler, Lake, or build tool was run.

## Review by Q06

I read the item node, `def-coef-complete-algebroid`, `lem-coef-algebroid-equivalence-nerve`, and `lem-coef-space-geometric-descent` in the shared DAG. Step 1 uses the definition for the endpoint/object-space setup, the equivalence-nerve statement for the fiber equivalences supplied by each fully faithful structure map, and the descent statement's fiberwise comparison criterion; these are exactly the hypotheses used. Step 2 uses the descent statement's clauses that realization commutes with finite products and that pullback naturality squares realize to pullbacks. Step 3 checks the unique degree-zero structure maps are fully faithful and essentially surjective, then uses the cited equivalence-nerve clauses that essential surjectivity gives object representatives and that object equivalences preserve enriched mapping objects. Step 4 uses the degree-zero realization pullback, full faithfulness of `j_0`, the descent statement's component-surjectivity and finite-product clauses, and its final fiberwise comparison criterion to prove the comparison with `I_1(B)` is an equivalence. I checked that the base comparison is the assumed equivalence `|U(C_\bullet)|\to U(B)` and that all endpoint maps and compatibility homotopies come from the coherent cocone. The citations file was checked against the exact statement text; no citation quotes a proof or an unstated hypothesis. Empty spaces are covered by the same fiberwise criterion. No statement correction was required.
