## What changed

Filled the proof of
`AlgebraicGeometry.effectiveCartierDivisor_finite_over_field` in
`Sheaf.AlgebraicGeometry.CartierDivisorFinite`, with its signature unchanged.
The proof follows all four existing DAG steps: use `hJ.compl_support_dense`,
identify the closed immersion's range with `J.support`, apply
`dim_le_zero_of_isNowhereDense`, and apply `proper_dim_zero_finite_over_field`
to the composite proper morphism. The no-nonempty-open clause follows from
`compl_support_dense`'s last clause. `FiniteDimensional` is `Module.Finite`
over the field, using exactly the composite morphism's `ΓAlgebra`.

Read Stacks Project `varieties.tex`, Lemmas
`degree-effective-Cartier-divisor` (Tag 0AYY) and
`algebraic-scheme-dim-0` (Tag 06LH), and the current blueprint's
`sk-thm-picard-rr/_section.md`. The unit route is preserved. No node changes
are needed: the existing proof and dependencies describe this proof.

Searches: launcher LeanFinder for effective Cartier finiteness on proper
schemes of dimension at most one; Loogle for `Dense, IsNowhereDense`;
launcher grep for `isFinite_subschemeι_comp|range_subschemeι|isNowhereDense_compl`;
and local searches of `lean/WeilConjectures` and `lean/Sheaf`. The upstream
relative Cartier result requires a smooth relative curve, so does not replace
this theorem. Loogle supplied `isClosed_isNowhereDense_iff_compl` for the
short topological bridge.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.effectiveCartierDivisor_finite_over_field`
(node `lem-pc-cartier-divisor-finite-over-field`).

Zero holes remain in the item; zero holes were added; zero statements were
split off. The proof uses the existing declared dependency
`AlgebraicGeometry.proper_dim_zero_finite_over_field`
(node `lem-pc-dim-zero-finite-over-field`), whose proof is still `sorry` in
the shared source. This delivery does not claim to close that dependency.

The item compiled on the server in 6.6 seconds on the first attempt; the
single redundant `change` tactic reported by the linter was then removed.
The final server delivery check verifies the cleaned file and its axioms.

## No longer needed

None. No imports were removed, and every existing proof-dependency module
is used. The Mathlib closed-immersion properness and composition instances
supply `lem-weil-pbc-closed-immersion-proper`. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The declared interfaces suffice without changes, new statements,
or adaptations. The empty divisor and empty ambient scheme are covered by
the same density, dimension-drop, and proper-dimension-zero declarations;
no nonemptiness, reducedness, integrality, or smoothness hypothesis is used.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
