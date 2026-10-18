## What changed

Replaced the nine compatibility proofs in `Sheaf.CategoryTheory.RingedKoszulSystem`
by direct categorical arguments. The two-term factors use Mathlib's differential
formulas; projection compatibility uses `NatTrans.ofSequence` and induction on the
number of factors. The tensor-tower laws follow by evaluation at each index and
degree. Dualizing the projection compatibility produces the unit cone; the limit
unit is a chain map by joint monicity of limit projections.

The existing statements and constructions are preserved, including the empty
list, exponent `m + 1`, slice restrictions, and derived-limit presentation.
Private, proved bifunctor and limit-lift helpers support the tensor induction
and the chain-map argument. Two canonical local proposition-instance caches
and local transparency controls reduce elaboration overhead.

## Proved and sorry left

Closed all 9 original holes, by declaration name (namespace `CategoryTheory`):

- `ringedKoszulFactorStepF_comm`
- `ringedKoszulFactorProjectionF_comm`
- `ringedKoszulProjection_naturality`
- `ringedKoszulTensorTower_d_comp`
- `ringedKoszulTensorTowerComplexMapF_comm`
- `ringedKoszulTensorTowerComplexMap_id`
- `ringedKoszulTensorTowerComplexMap_comp`
- `ringedKoszulTensorUnitComponent_naturality`
- `ringedKoszulLimitUnitF_comm`

Sorry left: none. Holes added: 0. Split-offs: 0. All declarations belong to
`def-weil-pbc-ringed-koszul-system`. The diagnostic compile checked all nine
proofs; the final full compile and delivery validation are recorded below.

## No longer needed

None. All existing public imports supply definitions or statement types of this
module. The node has no proof dependencies to prune. No additional ringed-site
results are needed for these categorical compatibility proofs.

## Where the brief, the DAG or earlier work was wrong

The assigned definition node has an empty `proof` list. The natural-language
proofs in the existing declaration docstrings give the compatibility arguments.
No mathematical statement repair was needed. The original file is close to the
60-second compile limit; elaboration controls prevent expansion of the total
tensor construction while proving abstract functorial identities.

Elaboration-only changes are recorded in
`coord/changes/H2-ringed-koszul-elaboration.md`. There are no new nodes and no
forced adaptations.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
