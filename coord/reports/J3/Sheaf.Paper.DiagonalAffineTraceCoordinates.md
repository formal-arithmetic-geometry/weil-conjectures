## What changed

Completed `projectionIso_existsUnique` in `Sheaf.Paper.DiagonalAffineTraceCoordinates`.
The inverse isomorphism is constructed from the actual `comparedModuleProjection`,
and its inverse condition and uniqueness are proved directly. All existing public
signatures, definitions, attributes and public imports remain unchanged.

Added the proved generic theorem
`AlgebraicGeometry.ProEtale.isIso_comparisonMate_of_finiteCohomologicalDimension`
in `Sheaf.AlgebraicGeometry.ProEtaleFiniteCDComparison`. It extends the native
bounded-below comparison mate by lower truncations, a uniform étale cohomological
dimension bound, exact pro-étale countable products and left completeness.

Private helpers keep the categorical projection transport generic before specializing
its coefficient category, including compactification and coefficient-first symmetry
transport. They obtain the uniform proper module bound from the existing finite-type
fibre-dimension bound, proper torsion vanishing and higher-direct-image forgetful comparison. They transport the finite étale proper projection map, then extension by
zero, tensor symmetries and the source comparison. This proves invertibility even
without the unused finite-Tor hypothesis; the assigned signature is retained verbatim.

Updated the owning DAG proof and added the node for the generic comparison theorem.
No source-library module, statement or definition is changed. No consumer adaptations
or change records are required. Both Lean modules compiled through `lcompile.py`:
the comparison module in 28.5 seconds and the completed item in 55.1 seconds.
Profiling instrumentation was removed before delivery. The projection transport
explicitly unfolds the named wrapper before registering its categorical isomorphism
hypothesis; this avoids an expensive instance-conversion search.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.projectionIso_existsUnique`.
The item's actual remaining hole count is zero. Added zero holes. The new comparison
theorem and every private helper have complete Lean proofs. No split-off sorry theorem
is introduced. This counts as one hole closed, rather than a decomposition.

The proof uses existing project declarations in the intended stage-3 sense; no claim
is made that every transitive dependency of those declarations is already sorry-free.

## No longer needed

No original imports were removed: the module's existing definitions and the already
proved auxiliary lemmas still use them. The candidate bundled
`ModuleCohomologyConventions` proof import was dropped in favour of the smaller
`HigherDirectImageForgetComparison` interface. The explicit duplicate
`LowerShriekProjection` import was also dropped; it is already publicly available
through `FiniteSiteTensorProjection`. No existing declaration, module or node is
withdrawn. The original auxiliary proof dependencies are retained.

The projection-isomorphism argument does not use a bounded flat model of the Tate
coefficient, invertibility of its annihilating exponent on the base, or a finite-Tor
lower bound for the tensor source. It instead uses finite cohomological dimension of
the proper étale direct image. In particular no imports of field-restricted
`UnboundedDirectImageComparison`, `UnboundedDirectImageTruncationStability`,
`ProEtaleClassicalBounds`, or ambient pro-étale finite-cohomological-dimension
assertions are added. These modules are not claimed globally prunable.

## Where the brief, the DAG or earlier work was wrong

The prior docstring suggested a bounded flat coefficient model followed by the finite
projection formula. However `hS` (invertibility of the prime) is not a parameter of
`projectionIso_existsUnique`, because Lean omits unused section variables. The Tate
flatness proof needs that hypothesis, so using it here would require changing the
existing signature. The present proof works for the actual signature, over arbitrary
Noetherian bases, by a proper finite-CD argument. It does not assume a bound on higher
direct images of arbitrary pro-étale sheaves, which would be incorrect.

The existing fibre-dimension theorem was found and reused; no new geometric existence
assumption was needed. No unit statement or required unit proof step is bypassed.

## New nodes

`lem-pur-finite-cd-unbounded-comparison`, in
`dag/nodes/sec-smooth-purity/lem-pur-finite-cd-unbounded-comparison.json`, records the
fully proved generic native-mate comparison theorem. Its statement allows arbitrary
complexes and a qcqs morphism with a uniform module étale higher-image bound. The
source, full truncation argument, dependencies, searches and verbatim Lean signature
are recorded there. This is a genuine intermediate comparison result, not a renamed
projection-isomorphism statement. No change-record path applies.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
