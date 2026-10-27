## What changed

Proved `WeilConjectures.FrobeniusExchange.pullback_linear` in
`Sheaf.Paper.FrobeniusSquareExchange` by restricting the existing ambient theorem
`WeilConjectures.integralDerivedPullback_linear`. Both additive and scalar-linear
laws follow through `ObjectProperty.hom_ext`. Added only the private proof import
`Sheaf.Paper.IntegralDerivedPullbackLinear`; all signatures and constructions stay
identical. Updated the owning node with this explicit dependency and proof step.

Profiling identified approximately five seconds each in the existing
`modelSource_linear` and `modelTarget_linear` proofs, inferring the two unknown
factors of `inferInstanceAs (_ ⋙ _)`. Each now unfolds only its named composite
and infers instances for the specified factors. This changes only theorem proofs.
The new restriction proof itself was inexpensive in the declaration-level trace.
The final uninstrumented `lcompile.py` run passed in 55.5 seconds with no warnings
or errors. All profiler settings were removed.

The same restriction argument already appears in the proof of
`rationalDerivedPullback_existsUnique` in `DerivedPullbackTensorHom`, whose private
import does not expose the ambient theorem to this module. The direct import is
necessary here. The ambient pullback is locally irreducible in this proof section,
so extensionality does not unfold the full normalized descent. This is a local
proof setting and exports no attribute. The import-direction check accepts it.
Searches used leanfinder,
loogle, the msearch grep service, and local rg over both library roots.

## Proved and sorry left

Closed 1 of the original 5 holes:
`WeilConjectures.FrobeniusExchange.pullback_linear`.
Added 0 holes; split off 0 statements. This proof uses the existing named ambient
linearity theorem, which remains an independent proof obligation in its own module.

The following 4 original holes remain unchanged, all owned by
`def-weil-operation-exchange-coefficient-descent`:

- `WeilConjectures.FrobeniusExchange.intrinsicCompactificationCoherence`
- `WeilConjectures.FrobeniusExchange.modelScalarMap_isIso`
- `WeilConjectures.FrobeniusExchange.stageBeta_coherence`
- `WeilConjectures.FrobeniusExchange.stageExchange_compatible`

## No longer needed

None. All prior public imports and the scalar-localization proof import remain.
The proof avoids redoing the K-flat/quotient/limit linearity argument locally by
using its existing ambient theorem; that theorem is needed, not pruned. No node,
module, declaration or unit-route step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The docstring's representative-level proof of
`pullback_linear` is already packaged by `integralDerivedPullback_linear`, so only
full-subcategory extensionality is needed here. The other four holes require the
normalization of the specified comparisons; arbitrary coefficient or refinement
isomorphisms would not prove those statements. They remain unchanged in this
partial delivery, as permitted for modules with several holes.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
