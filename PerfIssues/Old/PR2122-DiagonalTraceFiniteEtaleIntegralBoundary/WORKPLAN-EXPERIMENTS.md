# Workplan experiments: PR #2122

Case: `P2122-value`, declaration
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteEtale_integralBoundary`.
Lean 4.35.0, master revision `1ef1fddac73e`, original module identity, one
Lean thread.

## Baseline

The old module's final stored-value check is the large Kernel component. A
fresh frame replay used 345.75 s CPU, 5:48.62 wall, and 16,321,788 KB RSS.
The value has 26 outer frames: 14 theorem binders followed by 12 lets. Its
terminal expression is `Exists.casesOn` with five arguments. The prior probe
did not instantiate the theorem binders, so one terminal argument appeared
as a dangling bound variable and could not be used as an expression pair.

## G4-B branch-local probe

Probe: [`G4B-ValueFrames.lean`](probes/wp/G4B-ValueFrames.lean). It first
introduces the theorem binders with `lambdaTelescope`, substitutes the let
values, then checks the motive and both branch lambdas under the real local
context. It records each branch body's head, binder count, and independent
`Kernel.check` time. A branch is a valid control only if replacing that branch
with a term of its instantiated expected type preserves the parent value;
the probe rejects a branch before timing when its type cannot be checked.

## Interpretation

The workplan probe establishes the exact recursor and local branch context.
Checking the motive branch (argument 1) takes 16,115 ms and checking the
stored witness-predicate branch (argument 2) takes 18,419 ms; its body check
is 2,212 ms. The final nested branch (argument 4) cannot be checked in
isolation because its expected dependent context is supplied by the recursor.
These are branch-boundary costs, not proof that `Exists.casesOn` iota
reduction is the cause. The concrete category/functor differences described
by the historical PR remain source-guided candidates only.
The corrected branch probe used 379.92 s CPU, 6:23.20 wall, and
16,327,872 KB peak RSS; it preserved the original declaration and changed
only diagnostic inspection code.

**Confidence:** branch-local cost is confirmed, but the exact inner
conversion remains unclassified.
