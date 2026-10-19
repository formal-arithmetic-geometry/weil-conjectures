## What changed

Proved `AlgebraicGeometry.Etale.hypercohomology_convergence_statement` with its
signature and docstring unchanged. The only Lean file changed is
`Sheaf.AlgebraicGeometry.HypercohomologyConvergenceStatement`.

Used the already proved lower-bound lemmas of `HypercohomologyFiltrations`
through a proof-only `import all`, and added proof-only imports of
`WeilConjectures.CategoryTheory.HalfPlaneConvergence` and
`WeilConjectures.CategoryTheory.AbutmentImageFiltration`. The private helpers
identify the exact couple's D, E and alpha projections, construct and normalize
the actual truncation cocone, transport finite image filtrations to the specified
abutment, and propagate zero terms to every page. No definition or public
signature changed. The node's proof and dependencies now record this route.

The cocone construction adapts the equality-transport argument of the retired
`hypercohomology_convergence_of_bounds` helper to the current exact-couple API.
The two separate derived functors share this fully proved private argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.hypercohomology_convergence_statement`
(node `lemma-weil-pbc-hypercohomology-convergence`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module;
all five private helper theorems are proved. This is a proof, not a decomposition.

## No longer needed

No original import or declared proof dependency is removed. The sole original
proof dependency, `def-weil-pbc-hypercohomology-filtrations`, is used.
The obsolete `tool_uses` approval for `lem-sp-kinjective-computes` is removed:
this proof uses cohomological lower bounds and the actual truncation maps directly,
without the K-injective-computes theorem. Its module is not imported directly.

No new intermediate statement, module, or node is needed. In particular, the
commented-out `hypercohomologyFiltrations_spec` and
`hypercohomology_convergence_of_bounds` declarations need not be repaired for
this proof; the existing proved lower-bound lemmas and generic convergence
interfaces suffice. The middle base-change couple, its comparison maps,
and its filtration transport are not needed to establish this two-sequence
statement. They remain part of their own definition module's interface.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous inspection correctly found the proved lower-bound lemmas.
The old convergence helper is inside a comment marking it taken out at an
upstream sync. Its old `ofShifted_alpha` simplification does not apply to the
current explicitly constructed exact couple. The new projection helpers
eliminate the exactness witnesses and keep the resulting object equalities
explicit, so the proof works with the actual current construction.

The existing hypotheses concerning the chosen square, torsion and the
termwise bound are retained verbatim. The argument uses the supplied
cohomological bound, and therefore does not need those additional hypotheses.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
