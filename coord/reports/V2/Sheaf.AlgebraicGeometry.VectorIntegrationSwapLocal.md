## What changed

Replaced the hole in `AlgebraicGeometry.Etale.vectorIntegration_swap_local` by
naturality of the derived identity comparison, restriction of the supplied map,
the chart-source comparison, and the existing affine linear trace invariance.
The original statement is unchanged. Added proof-only imports of the two new modules.
A proved private categorical lemma handles composition without unfolding bundle data.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.vectorIntegration_swap_local`.
This is a decomposition, not a net proof: two strictly smaller obligations are added:

- `AlgebraicGeometry.Etale.vectorIntegration_swap_chart_prefix`
  (`lem-pur-vector-integration-swap-chart-prefix`): the exchange comparison before
  applying the affine counit, with no projective-line data, map k, or normalization.
- `AlgebraicGeometry.Etale.vectorIntegration_identity_unit`
  (`lem-pur-vector-integration-identity-unit`): the identity inverse-image comparison
  at the constant unit, without finite-ring or Noetherian hypotheses.

There are no holes inside the item's proof, private helpers, or definitions.

## No longer needed

No existing module is withdrawn. The geometric swap construction, chart comparisons,
Tate transport, and compact-support comparisons remain needed through the new chart
lemma. The unit route and the parent geometric-descent dependency are preserved.
The exploratory proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor`
is not required in the item; its identity coherence work is isolated in the new node.
No original public import is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The old plan combines a geometric chart-source
calculation with counit invariance and identity-unit coherence in one step. The packet
separates those assertions and writes the combination in Lean. Both new statements
include empty schemes and opens, rank zero and the zero coefficient ring. Neither
selects data in a definition from an unproved existence theorem.

## New nodes

`lem-pur-vector-integration-swap-chart-prefix` records the pre-counit exchange
calculation. Its matrix is used only within the proof of the item; no public
construction is defined by choosing it. The supplied exchange and coefficient
comparison are unchanged. The source is the simultaneous-frame calculation in
paragraph 2 of the vector-bundle purity proof.

`lem-pur-vector-integration-identity-unit` records the constant-unit identity
comparison, a consequence of adjunction uniqueness and exact derived single-functor
coherence. Its source and complete argument are in the docstring and node.
No definition or statement was changed, and no change record is required.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
