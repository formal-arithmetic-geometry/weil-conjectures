## What changed

Proved `AlgebraicGeometry.HilbertCoefficient.blockLowDerivativeRecovery` in its original module,
with its full statement unchanged. Added only proved private helpers in that module and private
proof imports of `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` and
`Mathlib.Data.List.Perm.Basic`. The public definition import is unchanged.

The proof uses strong induction on numerical degree. For a diagram derivative of a current
block generator, choose a dominated vertex and apply the induction hypothesis at that vertex's
degree. Restriction to its essential coordinates invokes `hlater`; complementary derivatives
preserve the coordinate ideal by the Leibniz rule and ideal-span induction. Coordinate partials
commute by the coefficient formula, and the list convention for iterated partials is handled by
permutation and a fold argument. Outside-diagram derivatives use the given reduction relation.

For the Jacobian step, directly write the selected derivatives as a finite matrix times the
coordinate tuple. The constant coefficient matrix is the assumed Jacobian, its determinant is a
unit, and the nonsingular inverse proves equality of the ideals. This avoids transporting the
full transverse-shift theorem along a new enumeration of the essential variables. The matrix
span argument also appears for `Fin c` in the proved source lemma
`Ideal.span_range_mulVec_of_isUnit_det`; the local proof works directly on the essential-variable
subtype. No existing module outside this item was changed. The node's proof, proof dependencies
and proof origin now describe this route.

Searches: launcher leanfinder for invertible constant Jacobians generating coordinate ideals
returned unrelated Weierstrass and submersive-presentation results; loogle for
`MvPowerSeries.pderiv, Ideal.span` returned no match; launcher grep for iterated partials,
commuting partials and Jacobian spans found only basic derivative material. Local searches of
both library roots found no existing degree-block recovery proof. Mathlib supplied the finite
ideal-span formula, determinant mapping, power-series unit criterion and nonsingular inverse.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.HilbertCoefficient.blockLowDerivativeRecovery`
(node `lem-trf-block-low-derivative-recovery`). Added zero holes and zero new nodes.
Every private helper is proved; no `sorry` remains in the delivered Lean module.
The complete module compiled cleanly through `lcompile.py` in 4.5 seconds, with no warnings.

## No longer needed

The dependency `lem-trf-formal-transverse-shift-calculus` and its module
`Sheaf.RingTheory.FormalTransverseShiftCalculus` are not needed by this proof. The direct
coordinate-ideal matrix argument proves precisely its needed zero-graph consequence without
substitution, a formal shift, auxiliary variables, coefficient extension or reindexing.
That dependency's proof import was never present in the original item, so no existing import
was removed. The dependency is removed from this node's `proof_deps` and proof-step `uses`;
this does not withdraw the shared theorem or assert that other users no longer need it.
The multivariate-power-series and partial-derivative definition dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned preceding-block enumeration is
unnecessary: any dominated vertex provides an earlier occurring degree. The graph-factorization
invocation can be replaced by the direct finite matrix proof above. The hypotheses concerning
total order, vertex incomparability and ordering are retained verbatim although this proof does
not need them. Empty coordinate tuples are covered by the finite matrix identities; an empty
generator family gives no occurring block and the last assertion is guarded by `0 < s`.
When `n = 0`, positive vertex degree forces the generator family to be empty. A one-variable
vertex `Z^d` checks the selected derivative degree `d - 1`; mixed diagram exponents are handled
by the restriction/complement decomposition. The unit's statement and realized route are kept.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
