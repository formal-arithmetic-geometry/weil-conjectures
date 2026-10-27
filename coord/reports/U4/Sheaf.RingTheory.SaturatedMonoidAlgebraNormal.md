## What changed

Replaced the sole `sorry` in
`MonoidAlgebra.saturated_monoid_algebra_normal` by the existing three-step DAG argument.
Apply `MonoidAlgebra.support_subset_saturation_of_isIntegral` to `Q`, rewrite saturation
membership using `hsat`, and construct the preimage with `MonoidAlgebra.comapDomain`.
Mathlib's `MonoidAlgebra.mapDomain_comapDomain` proves that its image is `x`.
The construction also covers zero and empty support without a case split.
The theorem signature and all imports are unchanged. No other module is changed.

LeanFinder found finite-type and generic integral-closure facts, but no direct normality
result. Loogle and the Mathlib grep identified `mapDomain_comapDomain` for the final step.
The node's existing support-saturation dependency supplies exactly the needed support fact.

## Proved and sorry left

Closed 1 of 1 holes: `MonoidAlgebra.saturated_monoid_algebra_normal`
(node `lem-trf-saturated-monoid-algebra-normal`).
There are zero holes left in the item and zero holes added; no statements were split off.
The proof uses the already stated theorem
`MonoidAlgebra.support_subset_saturation_of_isIntegral`
(node `lem-trf-integral-support-saturation`), whose existing hole is unchanged.

## No longer needed

None. All three public imports support the unchanged statement; the private import
`Sheaf.RingTheory.IntegralSupportSaturation` supplies the proof dependency.
Both existing proof-dependency nodes are used. No module or node is withdrawn, and the
unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No obstruction. The ambient-group definition of saturation makes the canonical-completion
hypothesis unnecessary for this argument; it remains in the unchanged statement.
DAG step 2 can therefore use `hsat` directly, and step 3 is precisely Mathlib's existing
coefficient-restriction identity. No change to the mathematical route or new node is needed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
