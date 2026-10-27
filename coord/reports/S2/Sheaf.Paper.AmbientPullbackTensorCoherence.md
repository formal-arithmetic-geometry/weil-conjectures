## What changed

Proved `WeilConjectures.AmbientPullbackTensor.pullExact` in
`Sheaf.Paper.AmbientPullbackTensorCoherence`, with its signature unchanged.
The module now privately imports `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.
The existing local irreducibility declaration is extended to `Functor.leftAdjoint`
and `Functor.mapDerivedCategory` to prevent expansion of chosen adjoint and
localization constructions while elaborating later comparisons. This is local to
this file and changes no declaration body or public attribute.

Direct image is additive sectionwise, so its left adjoint is additive and preserves
colimits. The finite case uses the existing `finitePullLimits` comparison with
`Scheme.coefficientProEtaleModulePullback_exact`. For the whole sequence site,
`sequencePullEvaluation` identifies each evaluation of pullback with the exact
finite pullback after evaluation. These composites preserve monomorphisms.
Every section of a system belongs to a vertical slice, so sectionwise injectivity
reflects monomorphisms of the pulled-back system. Mathlib's abelian criterion
then gives preservation of homology and finite limits. This proves exactness
without a restriction on horizontal module transitions.

The proof follows step 1 of the existing node; its route and dependencies are
unchanged. The finite/evaluation helpers were already present in the module.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.AmbientPullbackTensor.pullExact`.

Two holes remain, unchanged, both attached to
`lem-sf-ambient-pullback-tensor-coherence`:

- `WeilConjectures.AmbientPullbackTensor.tensorData_existsUnique`.
- `WeilConjectures.AmbientPullbackTensor.ambientPullbackTensorCoherence`.

Added zero holes and split off zero statements. This is a partial proof delivery,
not a proof of the remaining tensor construction and coherence assertions.
Server single-file compilation passed in 38.4 seconds after the local unfolding
change (the earlier version took 59.4 seconds and timed out in delivery),
including the sequence-evaluation
comparison dependency compiled by the compile service's private overlay.

## No longer needed

None. No existing imports, modules or DAG dependencies are withdrawn. In
particular the tensor dependencies remain part of the two unfinished proofs.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition was changed. Two instance details need
explicit proofs in this interface: additivity of the specified direct image is
proved sectionwise, and exactness of coefficient evaluation is installed from
`coefficientSequenceEvaluation_exact` before transporting finite-limit
preservation along `sequencePullEvaluation`.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
