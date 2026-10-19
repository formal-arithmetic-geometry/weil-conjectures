# Stage-1 report: sk-lem-pe-derived-nakayama

## Files written

- `dag/nodes/sec-proetale-coefficients/sk-lem-pe-derived-nakayama.json`: split into three steps using existing nodes; seven actual Mathlib searches recorded; no new nodes, no Mathlib leaves.
- `dag/units/sk-lem-pe-derived-nakayama.json`: only `realized` and `realized_by` changed, identifying the item as the carrier of the unit statement and its one proof paragraph.
- `citations.json`: four verbatim excerpts covering every step/node pair.
- `report.md`: this report.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its exact blueprint tag, derived Nakayama, reduction, and completeness found no declaration stating the whole item. `AlgebraicGeometry.Etale.isIso_of_derivedComplete_of_isIso_reductionModIdeal` (`WeilConjectures/SixFunctors/Etale/Derived/ReductionConservative.lean:117`) concerns the small etale site with ordinary constant coefficients. It does not state this pro-etale pulled-back coefficient result, nor both the finite-resolution and zero-object clauses. The generic principal-completion files likewise concern sheaves of modules over an ordinary ring and are not silently identified with these module objects. No upstream-master sorry declaration was treated as a proof.

## WANTED:

None. All sources needed for this one-level split are available locally. No SGA source is used.

## What was wrong

The imported one-paragraph proof mixed the actual first-reduction criterion with an unnecessary reference to `lem-weil-pbc-levelwise-isomorphism-cones`, which assumes every reduction is invertible. I removed that comparison and separated the three clauses. Existing blueprint detail nodes already state the two key inputs, so inventing replacements would duplicate them. The item statement, statement dependencies, import flags, and blueprint metadata are preserved; `blueprint.same_as` is filled after whole-blueprint searches.

The earlier sandbox attempt omitted its searches from the item and supplied quotes with formatting differing from the current nodes. I refreshed the searches through the mandated command and regenerated excerpts directly from the cited statements. All seven refreshed searches succeeded; there is no unavailable-service claim in the new records. I also made explicit why the pulled-back resolution is perfect: it is bounded with two rank-one free terms. Ordinary ring-module perfectness alone is not being used to identify coefficient sheaf categories.

The coefficient algebra lemma `lem-weil-pbc-standard-quotients-perfect` is a generic tool explicitly named in the unit proof. This off-unit use is declared in `split_report.tool_uses`; the unit's own resolution and Nakayama route is retained.

## What could not be finished

Nothing remains for this one-level split. The existing detail nodes remain downstream obligations; no claim about their Lean closure is made. This worker runs only the dry run and leaves delivery to the second reader.

## Review by Q24

I read the worker brief, stage-1 rules, SETUP's three levels and tool rule, GOAL, DAG synchronization rules, worker role, delivery-errors B through E, this chapter and unit records, and the current main-20261015 unit statement and its three proof/detail files. I opened the current DAG statements of both statement dependencies and every proof dependency. The source for the item is its blueprint proof paragraph; its two detail files explicitly provide the two-term resolution, vanishing, and conservativity assertions. The ordinary algebra source is the blueprint's `lem-weil-pbc-standard-quotients-perfect.md`, with the current DAG statement distinguishing ordinary coefficient modules from coefficient sheaves. Its Stacks reference is Tag 0657, the perfect-complex definition. No new lemma was created, so there is no new-node source or duplicate pair to audit.

For Step 1, `lem-weil-pbc-standard-quotients-perfect` supplies exactly the finite free resolution over the integers of a finite extension of Q_l, with n at least 1. I identify its chosen uniformizer varpi with pi_E. `det-pe-derived-nakayama-resolution` supplies the exact sequence on the pro-etale site for every scheme X and its natural cone identification for arbitrary K. The bounded rank-one description establishes the adjective perfect directly. I do not infer sheaf exactness merely from ordinary module exactness. The two excerpts in citations.json contain both actual assertions used.

For Step 2, `det-pe-derived-nakayama-first-reduction` explicitly states that derived completeness in the sense of `sk-def-pe-derived-completion`, together with K_1=0, implies all K_n=0 and K=0. Step 3 uses that same node's explicit morphism criterion. These are existing blueprint nodes, not newly created clauses replacing an argument. Their internal induction and cone-closure arguments are downstream work; this item does not claim to supply them using only a definition. Each cited statement says exactly what its step takes, and every non-elementary input is cited. The completeness definition uses the same pulled-back coefficient sheaves and reductions, so no boundedness, constructibility, or alternate coefficient convention was inserted.

I checked n=1, the zero complex, and the identity of any complete complex. The resolution is in degrees -1 and 0 with augmentation to the quotient, so the cone has no missing shift. Completeness is essential: on the profinite point the nonzero coefficient object E has invertible uniformizer and zero finite reductions but is not the limit of those zero reductions. This confirms that the hypothesis cannot be dropped. No new statement needed correction, and there is no statement dispute.

Whole-DAG and whole-blueprint searches for derived Nakayama and the two-term resolution located the existing detail nodes; no other node states the whole conjunction. Mathlib searches used two semantic phrasings, two Loogle queries, and correctly rooted source greps. The semantic hits are ordinary quotient tensor products, ordinary adic completion, or t-structure vanishing statements; their types do not give this result. The ordinary/derived distinction prevents a false leaf classification. Searches are recorded with the query text and dates actually logged by msearch.py (UTC dates may differ from the local report date).

Against delivery-errors B-E, I checked that no new unsplit node hides a proof, no elementary observation became a node, no existing clause was duplicated, and no citation takes information only from a proof. The unit realization changes only its permitted fields. Source paths exist, all proof uses equal proof_deps as a set, excerpts are literal statement substrings, and the dependency overlay is submitted to the mandatory delivery preflight for cycle, route, and schema checks.

## Second reading by Q24

- Item statement: checked against `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-derived-nakayama/_section.md`; the three clauses, the (n\geq1) coefficient resolution, derived reductions, derived-completeness hypothesis, and morphism criterion agree. Verdict: pass.
- Step 1: checked against the blueprint proof paragraph and the statements of `lem-weil-pbc-standard-quotients-perfect` and `det-pe-derived-nakayama-resolution`; the ordinary finite-free resolution, pulled-back exact sequence, rank-one terms, cone identification, and naturality are all supplied. Verdict: pass.
- Step 2: checked against the `Vanishing` clause of `det-pe-derived-nakayama-first-reduction`; its hypotheses and all three conclusions used by the step agree exactly. Verdict: pass.
- Step 3: checked against the `Isomorphisms`/cone-closure clause of `det-pe-derived-nakayama-first-reduction`; the first-reduction isomorphism criterion applies to precisely the stated derived-complete source and target. Verdict: pass.
- New nodes: none were created, so B1-B7 and new-node duplicate/source checks are vacuous. Whole-DAG and whole-blueprint searches found the existing resolution and first-reduction nodes; no Mathlib declaration matches the pro-etale derived statement.
- Edge cases: checked (n=1), the zero complex, the identity morphism, and an empty scheme; the resolution and criteria remain well-typed, and no hypothesis is silently dropped.

Changes made: none to node or unit JSON; this section records the second reading only. The worker's removal of the unnecessary `lem-weil-pbc-levelwise-isomorphism-cones` citation and its three-step expansion were retained because the cited first-reduction node already supplies the needed cone argument and criterion. The existing seven Mathlib searches and verbatim citation excerpts were re-read and remain accurate.
