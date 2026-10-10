# Stage 1 report: lemma-nagata-qc-open-descends

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-qc-open-descends.json`: item split; no new nodes.
- `citations.json`: verbatim statement quotes for every proof citation.
- `report.md`: this report.

## Attachments

None. No declaration tagged `lemma-nagata-qc-open-descends` or equivalent was found under `WeilConjectures/` in the Lean source, and the item is not stated by a sorry-free declaration.

## WANTED

WANTED: `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/lemma-nagata-qc-open-descends.md`, for the source proof; the referenced file is absent from this checkout. The split follows the proof text retained in the imported node and its source metadata.

## What was wrong or incomplete

The imported item had `status: imported`, a null elementary flag, an empty `uses` list, and omitted `def-nagata-qc-open-descent` from `proof_deps` despite using that construction. I replaced this with two explicit proof steps. The first is elementary once the finite basic-open presentation in the definition is cited. The second cites the finite-upper-bound statement and the existing generic basic-open pullback lemma. The blueprint's `uses_not_cited` field remains unchanged as historical metadata.

## Review by H1

The worker review below records the source and dependency checks performed before this second reading. It identifies the imported definition, the finite-upper-bound lemma, and the basic-open pullback lemma as the cited dependencies. It also records the finite-union argument, the stage hypotheses, the Mathlib searches, and the principal-open edge cases checked by the worker.

## Second reading by H1

- Item statement: checked against the imported blueprint node and its definition dependency; the two clauses match, with no new node statements.
- Step 1: checked against def-nagata-qc-open-descent; the finite basic-open union is stated there, and finite-union quasi-compactness is elementary.
- Step 2: checked against lemma-nagata-directed-finite-upper-bound and lem-weil-pbc-basic-open-pullback; the former supplies the common-stage inequalities and the latter supplies the basic-open inverse-image equality, while inverse images distribute over finite unions elementarily.
- New nodes: none; therefore B1-B7 and duplicate/Mathlib-node checks introduce no new node. Existing cited nodes were searched in dag/nodes/, and the Mathlib search log is retained above.
- Edge cases: the empty finite union, one principal open, and a two-open union give the stated quasi-compactness and pullback equality; the argument does not require nonzero functions or a positive index.

Changes made in this second reading:

- Corrected the step-2 citation quote to reproduce the complete verbatim statement of lemma-nagata-directed-finite-upper-bound, because the prior quote was only a sentence fragment.

I read the item node, its unit `sk-prop-nagata-sketch-approximation`, the chapter record, and the statements of `def-nagata-qc-open-descent`, `lemma-nagata-directed-finite-upper-bound`, and `lem-weil-pbc-basic-open-pullback`. Step 1 takes exactly the finite union of basic opens from the definition; the remaining assertion is the elementary finite-union closure of quasi-compactness. Step 2 takes exactly the upper-bound conclusion `i ≤ u(F)` from the directed-finite-upper-bound node, and exactly the inverse-image formula for a basic open from the pullback node; finite unions commute with inverse images. The hypotheses are checked at the construction level: the finite set of lift stages is the set bounded by `u(F)`, and the canonical map `Y → Y_{lambda_W}` is the scheme morphism to which the pullback statement applies. I searched the Lean source for the blueprint tag and its concepts and found no matching project declaration. Mathlib searches found general basic-open compactness and pullback lemmas but no declaration for this custom finite-stage descent equality; the existing pullback node records the Mathlib match. I tested the argument on a one-chart principal open and on a finite union of two principal opens; both reduce to the stated pullback and finite-union identities. No new node was created because all non-elementary facts used by the steps are already represented by cited nodes.
