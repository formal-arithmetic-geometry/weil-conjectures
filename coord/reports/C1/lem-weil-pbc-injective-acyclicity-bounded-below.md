# Delivery: `lem-weil-pbc-injective-acyclicity-bounded-below`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-injective-acyclicity-bounded-below.json`: statement split into resolution, acyclicity, termwise exchange, and derived-conclusion steps; Mathlib search verdict is no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-torsion-injective-resolution.json`: new unsplit coefficient-resolution dependency; Mathlib search verdict is no match.

## Attachments

- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` belongs to `lem-weil-pbc-injective-acyclicity-bounded-below`; its slopmaster2 declaration remains `sorry` in `BaseChangeProperty.lean` lines 309-323.

## WANTED:

WANTED: a source or proof for torsion-preserving injective resolutions of torsion sheaves of modules over an arbitrary commutative ring, for `lem-weil-pbc-torsion-injective-resolution`.

## What was wrong

The node's Lean declaration is an arbitrary-`Lambda` generalization, but the proved Lean predecessor immediately above it assumes `IsAddTorsion Lambda`. Stacks Lemma 0A4B proves the converse only for prime coefficients and obtains general torsion abelian sheaves by prime-factor dévissage and filtered colimits; it does not supply the arbitrary-ring torsion-injective-resolution step. The new node records that missing reusable statement instead of treating it as an implicit private lemma. The proof dependency route was kept within `sk-thm-iff`; an initially considered split node from `sk-thm-reduction` was removed to satisfy the route check.

## What could not be finished

The new coefficient-resolution node is intentionally unsplit. Without it, the arbitrary-`Lambda` theorem cannot be audited as a complete proof from the available literature or Mathlib declarations. No Lean files were written and no compilation was run.

## Review by C1

- Independent source audit over the remote `slopmaster2` checkout confirms the target declaration is `sorry` and that the preceding proved theorem requires `hLambda : IsAddTorsion Lambda`.
- Stacks lines 18360-18445 were checked directly: the injective-resolution argument is for `Z/l` coefficients, with separate n-torsion and filtered-colimit dévissage; no arbitrary-`Lambda` torsion-injective resolution is stated.
- Recorded LeanSearch, LeanFinder, and Mathlib-source searches return only unrestricted enough-injectives/right-derived facts, so the new dependency is not a Mathlib leaf.
- `python3 tools/review_split.py lem-weil-pbc-injective-acyclicity-bounded-below` passes. `python3 tools/check_dag.py` reaches the item but reports seven pre-existing unreachable nodes and one unrelated missing chapter; those errors were not modified by this delivery.
- C1 verdict: accept the DAG split as an audited open dependency; keep the assigned item open until `lem-weil-pbc-torsion-injective-resolution` is proved or the arbitrary-coefficient statement is corrected by project review.
