## What changed

Proved `AlgebraicGeometry.ProEtale.supportComparisonCommonInjectives` in
`Sheaf.Paper.PuritySupportCommonInjectives`, preserving all declaration signatures and
all definitions. The proof constructs a bounded-below injective resolution using Mathlib,
proves injectivity after direct image, constructs the canonical normalization isomorphism,
and derives the augmentation quasi-isomorphism from the actual comparison unit. Evaluation,
restriction, support complexes, and kernel inclusions agree by reflexivity.

The node now records the fixed-ring normalization argument and existing generic sheaf
Grothendieck instance used by the Lean proof. No new lemmas or nodes are introduced.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.supportComparisonCommonInjectives`
(node `lem-pur-support-comparison-common-injectives`).

Holes added: zero. Holes left in the item: zero. No decomposition or new assumptions.

## No longer needed

The proof does not need `lem-pur-comparison-unit-injective-model` or its module
`Sheaf.Paper.PurityComparisonUnitInjectiveModel`: its Lean signature uses realized
ring-sheaf modules, while this item uses ordinary fixed-ring module sheaves. The generic
proved derived-adjunction formula supplies the normalization directly in the latter
presentation.

The proof does not need `lem-sf-comparison-pullback-exact` or
`Sheaf.Paper.ComparisonPullbackExact`: exactness instances already accompany
`comparisonUpperStar`. Its obsolete tool-use approval is removed from this node.

The proof does not need `lem-weil-pbc-ring-sheaves-grothendieck` or
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`: existing Grothendieck
instances for fixed-ring module sheaves already give enough injectives. The node uses
`lem-sfb-proetale-sheaves-grothendieck` instead. These three private proof imports are
removed. No module is withdrawn; other consumers can still need them.

## Where the brief, the DAG or earlier work was wrong

The planned application of `comparisonUnitInjectiveModel` does not directly typecheck:
its resolution lives in `FiniteCoefficientModules`, with inverse image followed by
coefficient realization, whereas this item's arbitrary resolution lives in ordinary
`Sheaf (Scheme.ProEt.topology T) (ModuleCat A)`. This is an interface mismatch, not a false
mathematical statement. The existing generic normalization theorem gives the same argument
without transporting resolutions or changing any statement. The unit's realized route
is unchanged; the item node is not itself a realized unit statement or step.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
