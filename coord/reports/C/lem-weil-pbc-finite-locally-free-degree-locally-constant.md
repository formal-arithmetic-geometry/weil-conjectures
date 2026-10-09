# Delivery report: `lem-weil-pbc-finite-locally-free-degree-locally-constant`

## Review by C

The node is split into three proof steps. The first applies the reviewed Mathlib-backed node `lem-weil-pbc-finite-flat-rank-iso` to identify the fibre dimension with the finite locally constant rank. The second forms the open-and-closed rank decomposition and restricts the finite locally free morphism to each component. The third records the equivalence with the stated `delta_f` formulation.

The node records LeanSearch, Loogle/LeanFinder, and grep searches. Mathlib has the generic finite-flat rank API, but no declaration directly stating the scheme fibre-degree formulation; therefore `mathlib_match` remains null. No Lean was written or compiled.

Validation: `python3 tools/review_split.py lem-weil-pbc-finite-locally-free-degree-locally-constant` passed; `python3 tools/check_dag.py --cycles` reported zero cycles.
