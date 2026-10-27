## What changed

Reduced `diagonalTrace_finiteDivisorAdjoint` to two separate assertions: the finite
forget-support Chern equation on the diagonal surface, and a generic direct-image
factorization on Hom sets. The combining proof applies `congrArg` to the surface
equality and rewrites the two factorization equations. The item signature and its
public imports are unchanged.

Added `DiagonalTraceFiniteCartierChern`, containing the explicit ordinary
`completedSupportedUnit` and the surface theorem. The unit is constructed from the
actual completed coefficient map by Mathlib's `unitToPushforwardObjUnit`, rather
than chosen from an unproved existence statement. Added
`DiagonalTraceFiniteAdjunctionFactorization`, which states the common operation on
all finite unadjointed surface arrows, with separate equations for every supported
completed arrow and every geometric arrow.

All three modules compiled together through `lcompile.py --all`; the final packet
removes the profiling options used while diagnosing the ordinary map. The
ordinary map now fixes its site, functor and coefficient arguments explicitly,
avoiding expensive inference through the completed inverse image.

These are different portions of the argument. The surface assertion has no f,
presentation, supported source on the base, direct image along a projection or adjunct. The
factorization assertion has no normalized diagonal limit, finite Cartier
normalization, special Picard class or Chern equation. It constructs an operation
on an entire Hom set. Its witness is eliminated only inside a theorem proof;
no definition chooses data from that existence statement.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteDivisorAdjoint`
(node `lem-sfb-diagonal-trace-finite-divisor-adjoint`) is closed by a complete
combining proof. This is a decomposition of one hole into two, not a net proof gain.
The item itself has zero remaining holes. No other existing hole was changed.

Two holes are added, each in its own module:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteCartierChern`
  (`lem-sfb-diagonal-trace-finite-cartier-chern`).
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteAdjunction_factorization`
  (`lem-sfb-diagonal-trace-finite-adjunction-factorization`).

`completedSupportedUnit` is a real construction with no hole. Each new theorem
has its source and full proof in words in its docstring and node. Edge cases were
checked at the level of the stated argument: n=0 still means exponent one; no
coefficient projection is inverted; empty schemes use the same canonical maps.

## No longer needed

No existing public or private import was removed, and no module is claimed pruned.
The old direct proof dependencies remain needed in the two smaller arguments:
the Cartier and finite-Chern comparisons belong to the surface theorem; exact
restriction/direct-image and limit comparisons belong to the generic factorization.
The item's node now lists the two assertions it actually uses. No unit statement
or realized unit step was bypassed. No declaration in WeilConjectures was changed.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies supply generic comparisons, but none states the normalized
finite surface Chern equation or the common Hom-set factorization for the supplied
presentation. Their mathematical content must still be connected through those
normalizations. The original proof outline combined these distinct tasks inside
its prose. The delivery makes the boundary explicit and supplies the Lean proof
that combines them. No statement is disputed or weakened.

## New nodes

`def-sfb-diagonal-trace-completed-supported-unit` records the actual
constant-to-supported map induced by the completed coefficient map, in
`DiagonalTraceFiniteCartierChern`. It has no hole.

`lem-sfb-diagonal-trace-finite-cartier-chern` is the unadjointed surface calculation,
using the positive finite Cartier class, forgetting support and scalar-unit
injectivity. It has no projection model or derived direct image.

`lem-sfb-diagonal-trace-finite-adjunction-factorization` is the generic comparison
of arbitrary surface arrows with their direct images and geometric adjuncts.
It has no diagonal-limit or Cartier/Chern hypothesis. Both statement nodes are
strictly separate pieces of the original argument, and the parent combines them
by applying the same operation to equal surface arrows.

The generic tools used in the two plans are
`lem-pur-coefficient-system-derived-comparison` (evaluation and the derived unit),
`lem-weil-ringed-tower-pushforward-limit-comparison` (the normalized limit square),
`lem-asd-supported-kummer-chern-realization` and `lem-sp-cartier-reduction-existence`
(the finite supported class), and `lem-sp-scalar-unit-ext-bijective` (injectivity
on the integral adjunct). These are generic tools, not a replacement of a unit's
route. No tool-approval field was added by the worker.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
