## What changed

Proved `AlgebraicGeometry.Etale.properOpenCoefficientOpenInverse_isIso` in
`Sheaf.Paper.ProperOpenCoefficientRefinement`, with its signature and all definitions unchanged.
The proof uses composite-adjunction conjugacy of the existing exact scalar-restriction/pullback
isomorphism to show that the target is isomorphic to an open extension. The B-open adjunction
has invertible unit, so its left adjoint is fully faithful and its counit is invertible on that
target. The prescribed inverse open comparison is its counit after the open extension of an
isomorphism, hence invertible. The auxiliary conjugate is used only to establish membership
in the essential image; no equality with the chosen scalar/pullback comparison is asserted.

Updated proof step 3 of `lem-sf-proper-open-coefficient-refinement` to record this shorter
invertibility argument, preserving the representative calculation still needed by the open
refinement theorem. No new imports, definitions, statements or modules are introduced.

Validation: on 2026-10-19 the required lcompile.py compiled the retained module against the
current library in 4.9 seconds, with exit code 0. The retained module differs from the current
source only in the proof of properOpenCoefficientOpenInverse_isIso. Its proof uses only
dependencies already imported by the original module.

## Proved and sorry left

Original holes: 2. Closed: 1. Added: 0. Split off: 0.

Closed: `AlgebraicGeometry.Etale.properOpenCoefficientOpenInverse_isIso`
(node `lem-sf-proper-open-coefficient-refinement`).

Remaining: `AlgebraicGeometry.Etale.properOpenComparison_coefficient_refinement`
(node `lem-sf-proper-open-coefficient-refinement`). Its original signature, docstring and whole
sorry proof are retained. It still needs the compatibility of the chosen scalar/pullback
normalization with the clopen projection and the specified bounded-below proper/open map.
The available properOpenIdentification_unit states a useful normalization, but does not by
itself provide the coefficient compatibility of the pullback compositors. No transposed
restatement of the remaining theorem has been added as a new hole.

## No longer needed

No original imports, nodes or modules are pruned: the unresolved refinement theorem retains
its planned geometric and representative dependencies. The closed invertibility proof does
not itself require a K-flat construction, clopen decomposition, or geometric properness.
The trial proof import `Sheaf.SixFunctors.EtaleOpenTensor` is absent from the final delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original auxiliary proof plan was longer than necessary:
invertibility follows from the existing scalar adjunction, exact restriction/scalar comparison,
and the invertible open unit. It does not require proving that the auxiliary object
isomorphism has the specified K-flat normalization. That additional compatibility remains
relevant to the second theorem, which this partial delivery leaves open.

The restart brief attributed the earlier timeout to a Lean definition. That diagnosis is not
supported by the current compile: this entire module compiles in 4.9 seconds. The earlier
recorded timeout occurred in delivery worktree checkout, before Lean preflight. Consequently
no definition or consumer interface was changed to address an unreproduced Lean timeout.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
