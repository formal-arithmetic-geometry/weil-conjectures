## What changed

Replaced the sorry body of `diagonalCompleted_cyclicCartier` by a Lean proof assembling
its coefficient frame and applying the finite projection equations carried by
`IsDiagonalLimit`. The original signature and every existing definition are unchanged.

The frame uses existing finite constant-ring realizations, their direct-image square,
flat supported scalar extension, the flat integral Tate-line scalar endpoint, and the
normalized integral and finite root maps. The new cyclic root endpoint is proved:
factor the actual continuous reduction through the bottom ell-power quotient,
construct its root-normalized free projection, and prove it invertible using the
existing epic local rank-one helpers. The generic free-root endpoint constructor
then supplies its finite realization and root normalization.

The remaining coefficient-transport statement assumes the given cyclic frame and
compares its scalar reduction with the finite residue class, only after restriction
to discrete integral coefficients. It uses the normalized whole-limit equation and
the n-th finite-cycle equation in `IsDiagonalLimit`.

Cancellation of restriction is proved: compose with forgetting to abelian sheaves,
apply exact-functor composition coherence, and use the existing supported
integral-generator Ext bijection. Finally the proved relative-boundary uniqueness
identifies the finite residue class with the positive canonical Cartier class.
`Reference.delta` identifies the original completed arrow.

All four modules passed the remote combined compile with `lcompile.py --all`.
Development profiling options were then removed for delivery.

This is a decomposition, not a sorry-free proof of the original obligation.

## Proved and sorry left

Original hole closed in this module:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCompleted_cyclicCartier`.

One new hole, in its own module with a source, proof in words, and DAG node:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclicEvaluation_transport`.

There was 1 original hole and there is 1 new hole: closed 1, added 1, net 0.
The new public declarations
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclicRootEndpoint` and
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclicClass_restrict_injective`
are proved completely. The frame and residue/canonical comparison helpers and all
new root-projection helpers are private and proved completely. No definition contains
a sorry, and no axiom or unsafe implementation was introduced.

## No longer needed

No existing module or DAG node is pruned. No original import was removed,
and no existing module or node was withdrawn.
The two original coefficient-comparison dependencies remain needed by the new
transport statement. The proof reuses existing proved finite-realization,
supported-endpoint, scalar-flatness, source-comparison and root-endpoint helpers.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or interface repair. The original DAG grouped coefficient
frame construction and comparison of the completed finite evaluation into one step.
The implementation proves frame construction, including its cyclic root endpoint,
from existing declarations and isolates only the coefficient transport comparison.
The now-proved generic helpers in `DiagonalQuotientRootEndpoint` and
`DiagonalQuotientRootProjectionIso` also apply to the cyclic root argument.

The remaining transport statement assumes a cyclic frame already constructed and
asserts only equality after restriction to discrete integral coefficients, with the
finite residue class. It constructs no frame, cancels no restriction, and does not
identify that residue class with the positive canonical Cartier class. The main
proof separately performs all three steps, using the proved root endpoint, the
supported integral-generator Ext bijection, and relative-boundary uniqueness.
The unresolved work is precisely the comparison of the scalar quotient units with
the completed finite evaluation and the resulting exact-functor Ext square.
Thus the new hole is a proper part of the argument, not the original obligation
under another name.

## New nodes

- `lem-diagonal-cyclic-root-endpoint`: proved cyclic quotient of the integral root
  line, normalized by the actual root projection.
- `lem-diagonal-cyclic-evaluation-transport`: remaining equality after integral
  restriction between cyclic scalar reduction and the prescribed finite residue class.
- `lem-diagonal-cyclic-class-restriction`: proved detection of cyclic classes after
  restriction to discrete integral coefficients.

All three are parts of the coefficient-change argument in blueprint paragraph (1).
The empty scheme and n=0 are included; the latter has positive exponent one.
The root endpoint uses neither flatness of the quotient ring over the integral ring
nor a uniformizer. The class comparison retains the full supported generator; it
does not test only the global section one.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
