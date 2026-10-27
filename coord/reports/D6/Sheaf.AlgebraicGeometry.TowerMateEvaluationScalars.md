## What changed

Completed `scalar_alpha` and `scalar_gamma` in
`Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars`, preserving their statements.
Private proved helpers express scalar compatibility with composition, whiskering,
associators, inverse maps and equality transport. The open-beta calculation is proved
first for abstract adjunctions and then specialized to the module operations.
The ordinary proof pastes the
compatibilities of open beta, the clopen projector and both compositors in the
six-factor definition of `singleAlpha`. The pasting calculation and its component
equation are proved for abstract functors before specialization to module functors.

The derived proof descends this ordinary equation using exact localization and
`exactSquare_comp_forward`, identifies the canonical proper scalar comparison by
`scalar_transpose`, and applies `exchangeMate_cube`. Added a private import of
`Sheaf.CategoryTheory.DerivedExactSquareComposition` and private access to existing
proved helpers in the ordinary-arrow and mate-cube modules. No public imports,
existing definitions or declaration signatures changed.

Updated the existing item's final proof step and dependency record to describe
this implementation. Named equalities identify the scalar interfaces and the
factored alpha with their existing definitions before taking components. Generic
isomorphism cancellation and local irreducibility attributes keep the large chosen
adjoint constructions folded during the new calculations. The existing
`evaluation_resolution` proof is also factored through a proved abstract
adjunction calculation to avoid unfolding its concrete module adjunctions.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars.scalar_alpha`
- `AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars.scalar_gamma`

There are zero `sorry`s left in the item and zero added elsewhere. No statements
were split off. All newly introduced private helper lemmas have complete proofs.

## No longer needed

None. No existing dependency, module or import was pruned. The proof retains the
unit's ordinary clopen-alpha route and its specified scalar comparisons.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The private pullback
composition and square lemmas in `FiniteOpenExchangeScalars` hold for arbitrary
commutative rings; their proofs can be reused here without any `Finite` instance.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
