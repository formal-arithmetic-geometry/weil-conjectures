## What changed

Implemented `AlgebraicGeometry.descend_affineTwoTermDeterminantData` in
`Sheaf.TraceFormula.TwoTermDeterminantAffineDescent` with private helpers.
The construction uses the explicit module `descentGlue` on the affine-open cover.
A single descent datum on all affine test maps supplies their comparisons; its
commutativity gives the cartesian composition law. Full faithfulness glues morphisms,
model and zero comparisons, evaluation, and arbitrary-pullback comparisons.
Ordinary and tensor pullback are identified through their common right adjoint.
The only added proof import is `WeilConjectures.AlgebraicGeometry.Descent`.

The complete proof passed a clean whole-file compiler check in 36.0 seconds.
Private helpers are kept outside the exposed section to avoid repeated unfolding
during elaboration. The delivery check validates the final packet and its axioms.
The module contains no `sorry`.

## Proved and sorry left

Closed the sole original hole,
`AlgebraicGeometry.descend_affineTwoTermDeterminantData` (1 of 1).
No `sorry` remains in the item. No holes are added, and no statements are split off.
All private helpers are proved.

## No longer needed

The proof does not use `lem-pc-flat-complex-derived-pullback`
(`WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback`) or
`lem-pc-affine-derived-pullback-tensor-tilde`
(`WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`).
The supplied affine cartesian system already provides the required comparisons,
and `twoTermPerfect_pullback` supplies membership. No model-level derived tensor
comparison is needed. Neither dependency is imported.
The proof also uses the existing open-cover-to-fpqc theorem directly, so it does
not separately use `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`;
that Mathlib leaf is removed from this node's proof dependencies.
No existing imports are removed; no modules or declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The third planned step unnecessarily invoked flat-model and affine tensor
comparisons after the affine cartesian data and arbitrary derived-pullback
stability had already supplied the needed structure. The node now records the
direct comparison on affine test schemes. The theorem signature is unchanged.
The retained original docstring describes the old flat-model route in its
arbitrary-pullback paragraph; the Lean proof and updated node use the shorter
cartesian comparison argument described above.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
