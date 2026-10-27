## What changed

Added and proved the private helper `finitePerfectModelsOn_mono`, which widens the
fixed cohomological interval while preserving the same sieve, complexes, and
restriction isomorphisms. Reworked the zero-level part of
`residuePerfect_finite_quotient_models` to construct the original interval first
and then use this helper to pass to `[min a b, b]`. No declarations, signatures,
public imports, or definitions were changed.

The sandbox copy compiles successfully with `lcompile.py`.

## Proved and sorry left

The added private theorem `finitePerfectModelsOn_mono` is fully proved.
The existing named hole
`AlgebraicGeometry.Scheme.residuePerfect_quotient_models_succ` remains as its
original `by sorry`, with node
`lem-weil-pbc-residue-perfect-finite-quotient-models`. No new sorry was added.
The aggregate theorem `AlgebraicGeometry.Scheme.residuePerfect_finite_quotient_models`
continues to compile and now uses the proved monotonicity helper.

## No longer needed

No imports or DAG dependencies became unnecessary. The helper uses only the
existing definitions and `CochainComplex.isStrictlyGE_of_ge` /
`CochainComplex.isStrictlyLE_of_le`.

## Where the brief, the DAG or earlier work was wrong

The existing one-step theorem's proof plan requires the derived tensor exact
sequence, finite-ring local constancy, and connected etale perfect-constant
lifting. Those declarations are available as interfaces, but the required
construction and comparison glue is not present in a form that closes the
one-step conclusion directly. The prior split-off of this theorem is retained;
this delivery adds a strictly simpler, independently proved interval-monotonicity
step rather than restating the same obligation.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
