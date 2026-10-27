## What changed

Restored the quarantined item from its recorded archive and replaced its single
sorry by a complete Lean assembly of three strictly separate constituents:
ordinary quotient source/line pullback, the diagonal class square, and the three
trace squares. The original theorem signature and public import are unchanged.
Added the three proof-only imports and their new modules and nodes. Added
DiagonalPullbackSquares, with two proof-only proposition structures containing
exactly the existing class and trace equation fields. These keep concrete
coefficient constructions out of elaboration of the large derived equations;
they contain no sorry or chosen data and change no shared definition. Updated only
the item's proof, proof_deps and proof_origin to match the assembly.

The source lemma has no Family, diagram, class, trace, or scalar compatibility
hypotheses. The class lemma asserts only the delta equation for independently
supplied normalized endpoints. The trace lemma asserts only the three trace
comparisons and their exchange invertibility. Neither latter lemma constructs
maps or proves the other's equation. The original theorem combines all three.

## Proved and sorry left

Decomposition, not a complete proof of the mathematics: closed the original hole
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCoefficient_quotientBaseChange
(node lem-diagonal-quotient-base-change), by a compiling assembly from three
new strict constituents. Original holes: 1; closed: 1; added: 3; net holes: +2.

Every remaining sorry is a public theorem with a full argument and source in its
docstring, in a separate new module:

- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotient_sourcePullback
  (lem-diagonal-quotient-source-pullback).
- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotient_classPullback
  (lem-diagonal-quotient-class-pullback).
- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotient_tracePullback
  (lem-diagonal-quotient-trace-pullback).

The assembly contains no sorry. No data definition was added, and no data is
chosen from a mere existence theorem. It destructs existence only within the
proof of the original proposition.

## No longer needed

No existing module is withdrawn, and no existing public import is removed.
The trace component does not need
lem-diagonal-uniformizer-scalar-squares: the given scalar trace compatibilities
already supply all required comparison_iso hypotheses. The resolution argument
of the original proof plan is unnecessary for this transport step.

The original three immediate proof dependencies
sk-prop-sfb-cartesian-coefficients,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and
lem-weil-pbc-proetale-abelian-closed-support are now used in the corresponding
new constituents instead of being immediate dependencies of the assembly.
They remain needed transitively. No pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The item and its direct definition dependencies were quarantined when the session
started. The recorded archive was used intact, preserving the statement, Lean
attachment and dependencies. The published build accepted that original source;
this delivery does not withdraw the archived item or replace it by an empty module.
The shared source restored the definitions during this work.

The listed broad proof dependencies supply the general tensor and closed-support
theory but do not state the normalized quotient compositor calculations or mate
pasting in the exact internal-module API used here. The new statements separate
these missing calculations without assuming a completed reference or Cartier class.
The latest blueprint paragraph is numbered (3), rather than an explicit (3c).
The new nodes cite paragraph (3) and the original quotient-base-change refinement.

Edge cases: n=0 is exponent one. Ordinary source tensor construction imposes no
uniformizer condition and works for pi=0 or a unit; the class square uses supplied
derived endpoints and does not assert flatness of a quotient. Trace transport also works for arbitrary pi: the supplied scalar compatibility
contains comparison_iso on each line. The item's original uniformizer hypothesis
is preserved verbatim but is no longer needed by the proof. No flatness of
O_E/(pi^(n+1)) over O_E is assumed. Zero schemes and the
zero coefficient module cause the same adjunction and tensor equations to vanish.

## New nodes

lem-diagonal-quotient-source-pullback states the ordinary endpoint construction,
independent of class and trace data. Its proof uses the ordinary scalar/pullback
compositor, the defining tensor coequalizers, and closed base change.

lem-diagonal-quotient-class-pullback states only the derived class square after
pasting scalar compatibility and cancelling normalized endpoint isomorphisms.

lem-diagonal-quotient-trace-pullback states only the three trace comparisons. The given
scalar comparison_iso fields supply all scalar comparison invertibility needed
on the shifted lines; canonical right-derived units identify the pasted mates
with modelExchange.


def-diagonal-pullback-squares defines ClassPullbackSquare and TracePullbackSquares
as Prop structures with exactly the published fields of PullbackCompatibility.
This definition node supports the local performance repair: the equation types
are elaborated once with generic coefficient and line parameters.

Validation: all five delivery modules compiled together in import order. The
profiling options used to diagnose elaboration were removed before delivery.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
