## What changed

Filled `AlgebraicGeometry.ProEtale.SpTowerReductionTranspose.tower_reduction_transpose`
without changing its signature or any existing definition body. The proof constructs the
specified direct-image isomorphism, derives the global counit square from the actual
compact-support transition, uses finite adjunction injectivity to identify the transported
reduction with the exceptional word, and transports the identity and triple laws.
Exceptional comparison invertibility is transferred from `reductionExceptional_isIso`
to the supplied arbitrary adjoints using the unique counit-preserving right-adjoint isomorphisms.
The arithmetic clauses use the supplied base fields and principal-ideal containment.

Added the proof-only import `Sheaf.Paper.TowerIntrinsicShriekTransition`. Its sole theorem
isolates the coordinate conversion between the published generic shriek-transition theorem
and arbitrary section-normalized intrinsic evaluations in this item. It assumes no
exceptional adjoints, representing pair, counit, or smoothness and concludes only the actual
compact-support transition equation. The original node now records the formal proof.

## Proved and sorry left

Closed the original local hole in
`AlgebraicGeometry.ProEtale.SpTowerReductionTranspose.tower_reduction_transpose`.
No holes remain in the item module or any of its private helpers.

Added one hole:
`AlgebraicGeometry.ProEtale.tower_intrinsic_shriek_transition`
(node `lem-sp-intrinsic-shriek-transition`, module
`Sheaf.Paper.TowerIntrinsicShriekTransition`). Its proof is exactly `by sorry`, with a
source and a complete natural-language proof in the docstring and node.
This is a decomposition: one upper hole closed, one strictly smaller hole added; net zero.
Existing imported statements retain their existing holes; none was added or changed there.

## No longer needed

Removed redundant proof imports `Sheaf.SecSmoothPurity.ReductionDirectImage` and
`Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: their declarations remain available through
the existing public imports of `ReductionExceptional` and `CoefficientTowerShriekInterfaces`.
Their modules remain mathematical dependencies, so this removes no module from the closure.

The parent no longer directly cites `def-weil-l-adic-coefficient-extension` or
`det-sp-scalar-extension-functor` as proof dependencies: the base already supplies
finiteness and ramification, while the supplied hS gives the ctf scalar-extension property.
Their definitions remain used, and their modules are not withdrawn.

`lem-sp-shriek-normalized-transition-comparison` is now used by the coordinate-conversion
lemma rather than directly by the parent. The old parent tool approval was withdrawn with
its direct edge; the new lemma requests the same generic transition result as a tool.
No source-library declaration or module is deleted. No module is claimed globally pruned.
The smooth tower unit route, including its Levels step, is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned transposition argument is correct, but the generic transition declaration
uses sequence-site realization and different scalar/evaluation coordinates. Applying it
in the item's original tower coordinates requires an additional comparison argument.
The existing `reduction_transition_compatibility` is close but requires a global
`FiniteNormalization` record, unavailable among this theorem's arbitrary b,o,q inputs.
The new lemma isolates exactly that missing bridge, rather than assuming a global
calculus or replacing the actual reductions by selected arrows.

The finite exceptional theorem existentially supplies adjoints; the item permits arbitrary
specified adjoints. A proved categorical helper transfers invertibility while preserving
counits. The item's hrep is redundant once the supplied counit-preserving isomorphisms
are given; its binder and all other binders are retained exactly.

Edge cases checked: equal indices give unitors; all triple indices may coincide;
zero reductions are allowed; ramified E only enters the supplied ideal equation;
the quotient annihilator proof also handles the zero ring and the first positive level.
No normalization or coefficient flatness was introduced. The coordinate lemma makes
no assertion of faithfulness for derived level evaluation.

## New nodes

`lem-sp-intrinsic-shriek-transition` is the actual compact-support transition formula in
the intrinsic coordinates fixed by q and v. Its dependencies are the existing
section-normalized interfaces, tower abelianness and generic transition comparison.
It lies below the original node in the same chapter and unit. The generic
`lem-sp-shriek-normalized-transition-comparison` is requested as a tool for this node:
it concerns compact support of bounded-below strict systems and has no exceptional
representability input. No definition or statement change record is needed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
