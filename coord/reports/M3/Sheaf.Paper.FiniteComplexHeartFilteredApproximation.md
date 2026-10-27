## What changed

Proved `AlgebraicGeometry.ProEtale.finite_complex_heart_filtered_approximation` in
`Sheaf.Paper.FiniteComplexHeartFilteredApproximation` by applying the existing
`AlgebraicGeometry.ProEtale.noetherian_finite_complex_heart_filtered_closure`
from `Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure` through a private
proof import. This theorem already has exactly the six required conclusions for
the same coefficients, module category, finite-complex hearts and universe; its
Noetherian hypotheses are supplied directly. Affineness and the local cohomology
bound are unnecessary for the conclusion. No signature or definition changed.
The item compiled cleanly through `lcompile.py` in 4.2 seconds, with no warnings.
Updated the proof docstring and the node's proof, proof dependencies, proof origin
and obsolete direct tool approvals to match this specialization.

The latest blueprint's `sk-prop-ind-heart.proof.md` supplies the argument behind
the reused theorem. The item's unit record realizes its statement and steps at
`prop-compactification-coherence-detailed`; this below-unit specialization does
not bypass a unit statement or step. Empty schemes, zero coefficient rings,
empty coproducts and integral torsion coefficients are covered without new
hypotheses by the cited theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.finite_complex_heart_filtered_approximation`
(node `lem-sfb-finite-complex-heart-filtered-approximation`).
Zero holes remain in the item; zero holes were added; zero statements split off.
The proof uses the existing, still unproved declaration
`AlgebraicGeometry.ProEtale.noetherian_finite_complex_heart_filtered_closure`
(node `lem-sfb-qcqs-finite-complex-heart-filtered-closure`); that existing module
is unchanged. This is a proof from a previously stated general theorem, not an
axiom-free proof of the whole dependency closure.

## No longer needed

Removed the private imports
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` and
`Mathlib.Algebra.Category.ModuleCat.AB` from the item.

The item no longer directly uses the original planned dependencies
`lem-cbc-sieve-module-sheaves-grothendieck`, `sk-def-sfb-sheaf-tensor`,
`lem-sfb-modobj-grothendieck`, `lem-sfb-noetherian-scalar-constructible-heart`,
`lem-sfb-noetherian-scalar-constructible-fp2`, and `lem-sfb-fp2-ind-realization`.
Their four-step argument is already packaged by the existing Noetherian closure
theorem, so duplicating its proof here is unnecessary. Removed the three obsolete
direct `tool_uses` entries accordingly. These dependencies remain in that general
theorem's proof plan, so no global node or module withdrawal is claimed.
The sheaf-tensor and internal-module imports still support the statement's
ambient abelian module instances; all public imports are preserved.
No modules are pruned from the targets' closure by this delivery.

## Where the brief, the DAG or earlier work was wrong

The DAG planned to reproduce the argument of an already stated, more general
Noetherian closure theorem. The existing theorem permits a direct specialization
and eliminates that duplication. Both statements already incorporate the necessary
Noetherian repair, and neither a statement correction nor a new lemma is needed.
Searches: Lean Finder returned general complex/Grothendieck-category facts;
Loogle returned the abstract `ObjectProperty.ind` API; Mathlib grep found no
geometric closure theorem. Repository `rg` found the exact general theorem used.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
