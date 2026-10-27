## What changed

Replaced the proof of
`AlgebraicGeometry.AlgebraicSpace.SingleComplex.coordinates_nonempty` by a complete
Lean construction from a flat-term K-flat resolution, the counit computation and
Mathlib's `DerivedCategory.left_fac`. The resolution's categorical tensor exactness
is converted to `IsFlatOnSite` using `siteSheafTensorRightIso`. The target of the
left fraction supplies the complex N and its comparison to K'; associativity and
two inverse cancellations prove the prescribed coefficient-map equation.

Added the proof-only imports of `KFlatResolutionIndependentCoefficients`,
`TensorColimitsIndependentCoefficients`, `SpaceKFlatPullbackCounit` and Mathlib's
`DerivedCategory.Fractions`. Updated the item's node to record this proof.
All existing signatures, definitions and public imports are unchanged.
Both modules compiled together through `lcompile.py --all`: the item in 21.9 s
and the new supporting module in 7.2 s. The sole line-length warning was then
fixed by wrapping the source docstring. The delivery tool performs the final
compile and preflight on that exact version. A local DAG traversal checked
418 reachable nodes with no missing dependencies or cycles. All newly added
imports are used by a statement or proof.

Added `Sheaf.AlgebraicGeometry.SpaceKFlatPullbackCounit`, with one supporting
computation theorem and its node. This is the remaining geometric computation
step, strictly smaller than coordinate existence: it concerns only a fixed
flat-term K-flat complex and the pullback counit, without K, K', a coefficient
map, resolution existence or a chain-map representative.

## Proved and sorry left

Original holes: 1. Closed body:
`AlgebraicGeometry.AlgebraicSpace.SingleComplex.coordinates_nonempty`
(node `def-sfb-space-derived-pullback-models`). No sorry remains in the item module.

Added holes: 1:
`AlgebraicGeometry.AlgebraicSpace.smallTensorPullbackComplex_counit_isIso_of_flatKFlat`
(node `lem-sfb-space-kflat-pullback-counit`, module
`Sheaf.AlgebraicGeometry.SpaceKFlatPullbackCounit`). Its proof is exactly `by sorry`;
the docstring gives the complete ringed-topos resolving-class argument.

This is a decomposition, closing one original hole and adding one strictly
smaller supporting hole; net hole reduction is zero. The coordinate construction,
including the two representative identifications and the counit equation, is
written in Lean rather than delegated to the new theorem.

## No longer needed

No existing import was removed and no existing module is withdrawn or claimed to
be globally unused. The original node had empty `proof` and `proof_deps`.

The docstring's K-injective replacement of K' and the K-injective Hom-bijection
step (Tags 079V and 070I) are unnecessary for this proof: the output N has no
K-injectivity condition, and Mathlib's `DerivedCategory.left_fac` directly
provides a chain map after changing the target representative. Consequently no
new K-injective comparison node, theorem or proof import is introduced. The
publicly imported existing `smallModules_hasKInjectiveResolutions` declaration
is preserved and may remain needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

The item's node recorded the definitions but no proof steps for its existence
obligation. The updated proof records the actual construction. The docstring's
K-injective route was valid but stronger than needed, so it now describes the
left-fraction construction instead. No statement was found false or changed.

The library already contains the general ringed-topos result
`SheafOfModules.PullbackTensorResolving.pullback_resolving_computation`
(node `lem-weil-pbc-pullback-resolving-computation`). It requires a concrete
`CategoryTheory.CochainPullback.RingedPullback` presentation. The fixed
algebraic-space pullback is instead a conjugated compatible-chart left adjoint;
its comparison with that presentation is not recorded. The new supporting
node explicitly retains this geometric transport and invokes the existing
general theorem afterward; it does not duplicate its proof. This general
resolving-computation result is used as a tool below the unit route; no unit
statement or realized step is bypassed, and no `tool_uses` approval is added.

The new assertion was checked on zero complexes, the empty algebraic space,
identity morphisms, and degree-zero flat modules. These all give the expected
counit computation. The proof makes no boundedness, quasi-coherence, flatness
of the morphism, or invertibility assumption on the coefficient map. In
particular phi=0 is allowed and its representative is supplied by the same
fraction construction.

## New nodes

`lem-sfb-space-kflat-pullback-counit`: the canonical total-left-derived counit
of `smallTensorPullbackComplex f` is invertible on any flat-term K-flat complex.
Source: Stacks `sites-cohomology.tex`, Tag 06YY, with the affine-basis comparison
of Tags 03G8 and 039Z. The node records the geometric presentation comparison
and the existing general resolving-computation theorem as the proof route.
LeanFinder, Loogle, Mathlib grep and local library/DAG searches found generic
ordinary pullback and derived-functor APIs, the general ringed-topos computation,
and scheme specializations; none supplies this algebraic-space comparison.
There are no change records because no existing statement or definition changes.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
