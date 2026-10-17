## What changed

Marked AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso as STATEMENT-DISPUTED.
The existing declaration, attributes, imports and body are preserved. Its elaborated type
omits the section instance [SmoothOfRelativeDimension d f.left]. The blueprint statement
requires that hypothesis. Capturing it in a proof changes the elaborated type, so the
compiled smooth proof cannot fill the unchanged declaration.

The identity on Spec(F_3), with ell = 2 and d = 1, gives a counterexample. Exceptional
pullback for the identity is the identity, so the left endpoint has the nonzero coefficient
module as H^0. The right endpoint is a single complex shifted by two and has H^0 = 0.
This contradiction uses no claim about local triviality or nonvanishing of the Tate object.
An authorized correction must retain the smoothness binder explicitly, then repair the
consumers whose inferred parameters consequently change. This delivery makes no such change.
The change record is coord/changes/smoothPurityIso.md.

## Proved and sorry left

Zero of one original holes proved; zero holes added; zero split off. The existing hole in
AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso remains, attached to
nt-target-smooth-purity-qbar, and is marked disputed rather than proved with a weaker type.
No new hollow definition or theorem obligation is delivered.

Before discovering the dropped binder, the sandbox compiled a proof from right-adjoint
uniqueness and the explicitly defined pullback/tensor/shift functor. It also compiled the
local-presentation induction for all nonnegative Tate powers and the bounded-constructible
closure argument for tensor and shift. That route had two geometric obligations: local
triviality of the concrete Tate line and the smooth compact-support adjunction. All of that
work is retained under scratch/route-requiring-missing-smoothness, outside the delivery.
It is not counted as a proof or decomposition of the existing declaration.

Validation: #check of the original compiled declaration shows no smoothness argument;
#check of the reconstructed definition shows the added instance argument. The original
Poincare consumer against the reconstructed definition fails at its two omit commands:
"cannot omit referenced section variable" (lines 131 and 139 of the test copy). This
confirms a real interface change, not just a different proof term. Dualizing compiled
against that reconstructed definition in 38.6 seconds. The disputed original module
compiled in the final check; the delivery dry run checks it again with the axiom probe.

## No longer needed

No existing import, DAG node or module is pruned. No existing module is withdrawn.
The attempted TwistedPullback, TwistedAdjunction, TateLineLocalTriviality and
TateLocalPresentation modules and their four new node records are retained in scratch,
not submitted, because they only support the smooth statement whose binder is absent.
No arbitrary-isomorphism or finite-witness candidate is submitted.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the Lean declaration does not retain its advertised smoothness
hypothesis. Its written result type mentions f and d but not SmoothOfRelativeDimension;
the original sorry body also does not mention that instance. Lean therefore omits it.
The DAG statement and source docstring assume smoothness, but the actual Lean type does
not. In particular the plan proves a different elaborated type if it uses smoothness.

The Poincare source even explicitly omits the smoothness variable on its two terminal
theorems, reflecting the dropped parameter. Its current holder is B3. Changing those
inferred signatures would exceed the allowed forced adaptation with identical signatures.
The exact target statement is therefore preserved and the mismatch is reported for an
authorized statement repair. No consumer is adapted in this delivery.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
