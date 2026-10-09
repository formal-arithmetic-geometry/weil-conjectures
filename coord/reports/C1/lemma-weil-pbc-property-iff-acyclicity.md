# Stage 1 report: `lemma-weil-pbc-property-iff-acyclicity`

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-property-iff-acyclicity.json`: split the equivalence, replacing the imported PBC-to-IA paragraph by a reusable cited node, adding source locations, the full proof dependency union, and the recorded search audit.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-property-implies-acyclicity.json`: new unsplit statement node for the PBC-to-injective-acyclicity direction; Mathlib verdict is no match after LeanSearch, Loogle, LeanFinder, and source grep.
- `dag/units/sk-thm-iff.json`: realized the unit statement and its single proof step with the assigned node.

## Attachments

- `AlgebraicGeometry.Etale.hasTorsionBaseChange.hasInjectiveAcyclicity` is a related source declaration in `BaseChangeProperty.lean` (lines 198-221), but it is not an exact attachment because it is module-valued and requires the coefficient-forgetting comparison.
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` is already attached to `lemma-weil-pbc-injective-acyclicity-bounded-below`; the assigned node does not duplicate that attachment.

## WANTED

WANTED: none. The Stacks Project source is listed in `literature/LIST.md` and was inspected in the fetched checkout.

## What was wrong or incomplete

The imported first implication hid the distinction between an injective module sheaf and an injective abelian sheaf. It now uses the existing module-direct-image acyclicity and exact inverse-image nodes through a dedicated reusable statement. The converse remains on the unit route through Leray acyclicity, proper underived exchange, injective resolutions, prime-factor dévissage, the five-lemma transfer, torsion filtered unions, and filtered-colimit direct images. No statement or blueprint error was found.

## What could not be finished

The new implication node is intentionally unsplit and joins the Stage 1 queue. No Lean was written or compiled, as required.

## Review by C1

I independently checked the revised equivalence against unit `sk-thm-iff` and Stacks Project Lemma 0A4B. The new first-direction node states the arbitrary-base-change vanishing and expands the module-to-abelian acyclicity step; the parent proof cites it directly. The converse proof names every existing route node used by its two proof paragraphs, and `proof_deps` is their exact union. The unit realization maps its statement and sole step to the parent node. `python3 tools/review_split.py lemma-weil-pbc-property-iff-acyclicity` passes, and `python3 tools/check_dag.py` reports zero cycles and no structural errors; the seven reachability warnings are pre-existing unrelated nodes. No Lean compilation was run.
