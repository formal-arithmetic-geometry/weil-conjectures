# Stage 1 report: def-nagata-qc-open-descent

## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-qc-open-descent.json`: repaired definition; no new child nodes.

## Attachments

None. I searched `WeilConjectures/` in both source checkouts for the item id, its title, and the quasi-compact-open construction; no project declaration states it.

## WANTED

None.

## What was wrong in the returned node

The returned statement did not state the directed inverse-system setting, the affine transition maps, or the meaning of the base-changed system. It selected affine opens merely meeting the image of `W`, which need not cover `Y_{lambda_0}` (and can leave part of `W` out), and it did not state why the chart intersections are quasi-compact or why their section rings are filtered colimits. It also referred vaguely to stages at which data lift and did not name the finite-data construction or the separately proved upper-bound property.

## Review by J1

I read the sibling repaired source node `def-nagata-qc-open-equality-stage` and copied its setting sentence word for word: the base-changed system, directed `I`, `S = lim S_lambda`, affine transitions, and `Y_{lambda_0}` quasi-compact and quasi-separated as a scheme. I read the statements of `def-nagata-basechanged-system`, `def-nagata-directed-finite-upper-bound`, `lemma-nagata-directed-finite-upper-bound`, `lemma-nagata-filtered-colimit-finite-data`, `lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-limit-global-sections-colimit`, and `pqf-lem-limit-qc-open-descends` before citing them.

The repaired statement now chooses a finite affine cover `Y_{lambda_0} = union U_a`, defines `U_{a,lambda}` and `U_a^infty`, and states that `W cap U_a^infty` is quasi-compact because `Y -> Y_{lambda_0}` is affine and `Y_{lambda_0}` is quasi-separated. It then uses the two limit nodes for `Gamma(U_a^infty,O) = colim Gamma(U_{a,lambda},O)`. For each chart, the finite-data node is applied to the finitely many functions with no equalities, producing a named stage `lambda_a` and lifts. The upper-bound definition and its lemma are both cited: the former supplies `u`, while the latter supplies `lambda_a <= lambda_W`, allowing the lifts to be transported. The final choice is the explicitly defined union of basic opens at `lambda_W`; the compact-open descent node's clause (2) records that different choices agree later.

This is a definition, so it has no proof steps and `citations.json` remains the empty list. The dependency list contains every node used by the statement. I preserved the imported bypass metadata and blueprint identity. I also ran the required Mathlib searches: LeanFinder returned only more general affine-transition-limit declarations, Loogle rejected the supplied pattern with zero hits, grep found no matching source declaration, and LeanSearch was unavailable; these are recorded verbatim in `mathlib_searches`.

## What could not be finished

Nothing remains for this split. The stage-by-stage construction is recorded even though the unit's formalized route bypasses it.

## Second reading by J1

- Item statement: checked against blueprint node `def-nagata-qc-open-descent` (order 347), with the base-changed-system setting aligned word-for-word with `def-nagata-qc-open-equality-stage`; verdict: hypotheses and finite-stage witness construction are explicit and consistent.
- Definition construction: checked the finite affine cover, chart inverse images, quasi-compactness argument, and basic-open presentations; verdict: the former "affines meeting the image" gap is repaired, and the cover cannot omit part of `W`.
- Limit-ring step: checked against `lem-weil-pbc-limit-affine-transition` and `lem-weil-pbc-limit-global-sections-colimit` (Stacks Tags 01YW/01Z0); verdict: the directed colimit of chart section rings is stated with its hypotheses and cited dependencies.
- Finite-data step: checked against `lemma-nagata-filtered-colimit-finite-data`; verdict: each finite family of functions has a named stage and lifts, with no hidden equalities or unspecified later stage.
- Common-stage step: checked against `def-nagata-directed-finite-upper-bound` and `lemma-nagata-directed-finite-upper-bound`; verdict: `lambda_W` is explicitly selected from the finite set and all lifts are transported using the proved upper-bound property.
- Choice-independence clause: checked against clause (2) of `pqf-lem-limit-qc-open-descends`; verdict: later-stage agreement is cited from the existing statement rather than asserted informally.
- New node `def-nagata-qc-open-descent`: B1 statement-only definition with no proof fields; B2 self-contained directed-system and qcqs setting; B3 every non-elementary notion is linked in `stmt_deps`; B4 TeX is escaped once; B5 source is the exact blueprint node (the imported definition has no separate Stacks tag); B6 not a Mathlib leaf; B7 searches are recorded verbatim in the node and `searches.jsonl`.
- Edge cases: the construction permits the empty open (empty basic-open family), works for a field and affine schemes, and uses only finite nonempty covers when `Y_{lambda_0}` is nonempty; no claim depends on a positive number of generators.

Changes made: retained the worker's four repairs, added this second-reading audit, and made no further mathematical changes.
