## What changed

Proved `AlgebraicGeometry.ProEtale.sfRelativeAdjointOpenOrigin` without changing any
statement, definition, public import or existing docstring. The proof establishes
quasi-compactness of the two targets, uses ordinary étale exceptional boundedness and
exact derived pullback, and proves invertibility factor by factor in the specified
comma-category natural maps. The existing witnessed-object constructor is unchanged.
Updated the node proof and dependencies to this argument. No new declarations or nodes.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.sfRelativeAdjointOpenOrigin`
(`lem-exc-relative-adjoint-open-origin`). Added 0 holes; 0 holes remain in the item.
This is a proof, not a decomposition. The source-library boundedness and comparison
lemmas are used as existing declarations. Single-file compilation passes; the delivery
probe checks the declarations and their actual remaining axiom dependencies.

## No longer needed

Removed these seven proof imports:

- `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`

The proof does not use `thm-sf-ambient-adjoint-class` or the coefficient System record:
the specified ordinary étale adjoint and its quasi-compact-target boundedness suffice.
It needs no explicit dimension choice (`lem-kun-dimension-finite-type`), finite-type
composition/base-change (`lem-sfb-finite-type-composition-base-change`), finite type of
the open immersion (`lem-weil-pbc-qc-open-immersion-finite-type`), or open-immersion
base change (`lem-weil-pbc-open-immersion-base-change`). Exact fixed-module pullback is
already available, so the separate realized-ring existence theorem
`prop-weil-pbc-inverse-image-modules-exact` is not used. The fixed canonical pullback
isomorphism is already defined by the public support-candidate module; no use of the
larger `lem-weil-pbc-comparison-pullback` coherence assertion is made, and its obsolete
tool-use entry was removed. The actual source comparison-unit theorem replaces the
bounded-below wrapper import while retaining the site-comparison proof dependency.
The definition `sfFiniteExceptionalFixed` remains necessary through its existing public
import; no claim is made that its general coefficient-system definition node is obsolete.
These are local dependency removals; other parents may still need these modules.

## Where the brief, the DAG or earlier work was wrong

The original plan was more elaborate than necessary: source-library
`Etale.hasBoundedBelowUpperShriek` already supplies boundedness over any quasi-compact
target, including both proper maps here. The class-adjunction existence package and
an explicit dimension bound are unnecessary for these particular witnesses. All unit
steps and target signatures are preserved. The existing `letI` topology choices in
`sfRelativeOriginObject` are retained, as their definitional transparency matters.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
