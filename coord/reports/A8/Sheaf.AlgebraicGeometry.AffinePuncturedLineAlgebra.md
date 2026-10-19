## What changed

Completed `Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra` without changing any existing
signature or definition. Private, fully proved helpers identify polynomial and Laurent units,
prove Laurent ideals principal, trivialize invertible sheaves on affine PIDs, construct the
specified quotient equivalence, prove its generator formula, and supply scalar roots over an
algebraically closed field. The retained earlier proof was checked against current sources.
The node now records the localization and free-generator arguments actually used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AffinePuncturedLine.affine_punctured_line_algebra`
(node `lem-pur-affine-punctured-line-algebra`). No holes remain and none were added.
No split statements or new modules. The complete module compiles cleanly through lcompile.py
in 6.0 seconds. The required deliver3.py dry run passes compilation and preflight; its review
class is CODEX because the delivery updates the node's proof route.

## No longer needed

Removed the direct proof import `Mathlib.AlgebraicGeometry.Modules.Tilde` and the corresponding
proof dependency `lem-weil-pbc-affine-tilde-gamma-adjunction`. The existing affine free-generator
API trivializes the sheaf directly from its section basis. Its own internal dependencies are
retained; this does not assert that the tilde module leaves the global closure.
All other declared dependencies remain used, including the two Mathlib PID/module leaves and
`lem-sc-affine-invertible-sections`. No blueprint unit or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox had a complete candidate proof but no report or node update. The DAG's
extreme-exponent existence argument is replaced by the localization unit criterion and
primality of X; degree and coefficient comparison still give uniqueness. The DAG's explicit
tilde/Gamma comparison is replaced by the existing free-generator API. No statement repair,
consumer adaptation, or target change is needed. The characteristic hypothesis is preserved;
the quotient computation in fact works for all N, and scalar roots use N positive, including
N = 1. The field may be arbitrary in both Picard statements.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
