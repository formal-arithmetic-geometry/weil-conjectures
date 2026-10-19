## What changed

Completed both instance theorems in
`Sheaf.AlgebraicGeometry.EtaleSupportedSections`, keeping every existing declaration's
signature, visibility, docstring and construction unchanged.

`AlgebraicGeometry.Etale.supportedEtaleSections_additive` cancels the component of the
kernel inclusion, then uses its naturality and additivity of global sections.

`AlgebraicGeometry.Etale.supportedEtaleSections_preservesFiniteLimits` views the kernel
as the limit of the parallel pair of restriction and zero. The flipped diagram preserves
finite limits because its two evaluations are global sections and sections on the open
etale object. Mathlib's `limitIsoFlipCompLim` identifies the kernel with the composite
of this flipped diagram and the limit functor, which preserves limits.

Added the proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` for
`preservesFiniteLimits_of_evaluation`. No definition, statement, public import or DAG
route changes, and no new declarations or nodes.

Validation: compiled the complete module using the required `lcompile.py` server tool.
Both proofs work uniformly for all opens, including the empty and full open, because
they use only the universal properties of kernels and section functors.

## Proved and sorry left

Closed 2 of 2 holes:

- `AlgebraicGeometry.Etale.supportedEtaleSections_additive`.
- `AlgebraicGeometry.Etale.supportedEtaleSections_preservesFiniteLimits`.

Both belong to node `def-pur-etale-derived-supported-sections`.
Zero holes remain in the item. Zero holes added elsewhere. Zero statements split off.

## No longer needed

No declared proof dependencies, nodes or modules pruned: the node has no proof dependencies,
and the proofs follow the universal-property arguments already recorded in its Lean docstrings.
The existing public imports are retained. The only added proof import is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The node is a definition node with an empty proof plan;
the proofs in the existing instance docstrings suffice and are realized directly using
Mathlib. The current blueprint snapshot places the cited restriction triangle in
`sec-six-functors-basics/sk-prop-a1-kummer`; the older source citation uses
`sec-smooth-purity/sk-prop-a1-kummer`. The mathematical construction agrees in both.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
