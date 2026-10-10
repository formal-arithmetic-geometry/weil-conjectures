# Stage 1 Delivery Report

Item: `lem-weil-pbc-etale-stratification-local-gluing`

## Files Written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-stratification-local-gluing.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-constructible-in-retrocompact-open.json`
- `coord/reports/F1/lem-weil-pbc-etale-stratification-local-gluing.md`

The repair adds one statement-only support node for Stacks Topology Tag 09YJ,
because Mathlib has no ambient-locality theorem for constructibility on a
retrocompact open. No Lean code was written or compiled.

## Review by F1

I checked the repaired three-step proof against Stacks Project Etale
Cohomology, Lemma Tag 03S9, and the cited DAG nodes. An affine chart in a
qcqs scheme is quasi-compact; the qcqs spectral and retrocompact-open nodes
therefore make it retrocompact, so both its closed complement and each local
constructible piece are constructible in the ambient X. The new 09YJ support
node now states the required basis hypothesis exactly: X has a basis of
quasi-compact opens, E is constructible in X, and F is constructible in E.
Iterating the existing common-refinement theorem gives a finite disjoint
partition whose strata lie in local pieces because the charts cover X. For a
chosen piece, the proof no longer assumes a scheme-theoretic factorization
from set containment: it defines the actual stratum scheme
Z_i = X_i fibre-product over X with W_{a,b}, records its projections, and
uses its induced immersion and image. Finite-morphism base-change permanence
gives finiteness and the etale base-change leaf gives etaleness; fibre-product
associativity identifies the source with the desired pullback. The proof
dependencies match every fact used by the steps.

Mechanical checks to run before delivery:

- `python3 tools/review_split.py lem-weil-pbc-etale-stratification-local-gluing`
- `python3 tools/check_dag.py`
- `python3 tools/preflight_delivery.py F1 lem-weil-pbc-etale-stratification-local-gluing`
