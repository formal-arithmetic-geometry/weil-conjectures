## What changed

Proved `Algebra.isQuasiFiniteAtPrime_iff_topologicalKrullDimAt_eq_zero` with its exact
original signature and universes. The proof directly uses the existing, proved topological
finiteness theorem `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`.
No scheme construction is necessary: finite-type base change makes the fibre Noetherian;
a zero-dimensional open subspace is finite and T1, hence discrete. In the forward direction,
the open singleton bounds the infimum above by zero, while closures of neighbourhood
points give the lower bound zero. In the reverse direction, `iInf_lt_iff` produces a
neighbourhood with dimension less than one, equivalently at most zero.

Updated the theorem's proof docstring and its DAG proof, dependencies and proof origin.
Pruned the unused imports and obsolete top-level tool-use approvals. Added proof import
`Mathlib.RingTheory.FiniteStability` for finite-type tensor base change. Imported the source
quasi-finiteness definition directly instead of its retired Sheaf re-export.

Validation: the final module compiled without errors or warnings in 4.2 seconds; the
unchanged sole direct consumer `Sheaf.AlgebraicGeometry.DescendQuasiFiniteAffine` compiled
against it in 3.7 seconds. A temporary `#print axioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary diagnostic and consumer copy were removed.
The public-import cleanup is documented, with all ten downstream consumers and their
holders, in `coord/changes/quasi-finite-zero-fibre-dimension-imports.md`. No consumers
require adaptation, and no definition, theorem signature or target meaning changed.

## Proved and sorry left

Closed 1 original hole:
`Algebra.isQuasiFiniteAtPrime_iff_topologicalKrullDimAt_eq_zero`
(node `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension`).

Added 0 holes. Remaining holes in the delivered module: none. This is a complete proof,
not a decomposition; the axiom probe confirms no transitive `sorry` dependency.

## No longer needed

Removed imports:

- `Sheaf.RingTheory.QuasiFiniteAtPrime`: retired wrapper; its source definition is now
  imported directly through `WeilConjectures.RingTheory.QuasiFiniteAtPrime`.
- `Mathlib.AlgebraicGeometry.Scheme`: no scheme object is constructed.
- `Mathlib.AlgebraicGeometry.Noetherian`: spectrum Noetherianity is obtained directly
  from the finite-type fibre ring and `Mathlib.RingTheory.Spectrum.Prime.Noetherian`.
- `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`: replaced by the
  already proved general topological theorem from the existing public topology import.
- The redundant private import of `WeilConjectures.RingTheory.QuasiFiniteAtPrime`:
  consolidated into the direct public import needed by the theorem statement.

Removed proof dependencies (their statements remain in the DAG):

- `pqf-def-locnoeth`: no locally Noetherian scheme instance is needed.
- `def-weil-pbc-quasi-compact-scheme`: no scheme compactness construction is needed.
- `def-weil-affine-spectrum`: the proof uses the spectrum as a topological space directly;
  the statement dependency is unchanged.
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`: use inheritance of Noetherianity
  under inducing maps on topological spaces instead.
- `lem-sc-zero-dim-noetherian-finite-discrete`: use its existing proved topological
  ingredient `lem-sc-zero-dim-noetherian-closed-finite` directly on the open neighbourhood.

Removed the obsolete top-level `tool_uses` entries `pqf-def-locnoeth`,
`def-weil-pbc-quasi-compact-scheme`, and `lem-sc-zero-dim-noetherian-finite-discrete`.
The dimension definition approvals remain in order. The added dependency
`lem-sc-zero-dim-noetherian-closed-finite` is already Lean-closed and is a generic tool;
its existing module was already publicly imported. No blueprint unit statement or
realized unit step is bypassed. These are local dependency removals; no claim is made
that other parents no longer need these nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The theorem statement is correct, including arbitrary base rings and both universe
parameters. No assigned repair or mathematical error was found. The original proof plan
was longer than necessary: its scheme and open-subscheme infrastructure can be omitted
using the already proved Noetherian T0 topological result. This implements the isolated-point
argument of Stacks Properties Tag 0H7C (the local source lemma and proof were read), with
Mathlib finite-type base change supplying the fibre hypothesis. There are no new nodes,
no definition changes, no forced consumer adaptations, and no remaining proof obligations.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
