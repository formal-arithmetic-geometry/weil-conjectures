## What changed

Proved `Module.exists_eq_sum_smul_of_polynomial_action` in
`Sheaf.RingTheory.PolynomialActionReduction`, preserving its signature, docstring,
and public imports. The R-span of the specified module generators is stable under
all algebra generators by the action relations. `Algebra.adjoin_induction` extends
this to all S-scalars; `Submodule.span_induction` then puts every module element in
that R-span. Mathlib's finite-span characterization supplies the coefficients.
Updated the existing DAG proof to this equivalent invariant-span argument.

## Proved and sorry left

Closed 1 of 1 holes: `Module.exists_eq_sum_smul_of_polynomial_action`
(node `lem-trf-polynomial-action-reduction`). Zero holes remain; zero holes added;
zero statements split off. The module compiled through `lcompile.py`.
The proof uses no nonemptiness or nontriviality hypotheses, and handles n = 0,
m = 0 and the zero ring through the same span induction.

## No longer needed

No existing imports, dependency nodes, or modules are pruned. Both recorded
proof dependencies describe the generation hypotheses still used. Explicit
polynomial expansions, monomial total-degree induction, and coefficient
recombination are replaced by Mathlib's adjoin/span induction and finite-span
characterization. These were elementary proof steps, not separate nodes.
No new proof import is needed: the existing Mathlib imports provide all lemmas.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG plan is valid, but explicit monomial degree
bookkeeping is unnecessary. This supporting node does not realize a unit's own
statement or proof step, and the unit route is unchanged. LeanFinder and Loogle
searches, alongside local Mathlib and source-library searches, found the general
induction and span tools but no exact theorem to apply directly.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
