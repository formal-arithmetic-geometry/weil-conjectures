## What changed

Completed `AlgebraicGeometry.ProEtale.RationalP1.singleUnit_existsUnique` in
`Sheaf.Paper.ProjectiveDiagonalPullback`. Unfolding `internalMonoidal`,
`internalTensorBundle`, and `nativeTensorBundle` identifies the bundled tensor unit
with the native one. The witness is exactly
`DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)`, its normalization is
`HEq.rfl`, and uniqueness follows by `eq_of_heq`.

The existing theorem statement, definition bodies, docstrings, and imports are unchanged.
The existing docstring already gives this argument; the node has no numbered proof
steps or proof dependencies to replace. No unit step is bypassed.

Validation: the complete module compiled through `lcompile.py` in 18.1 seconds,
with exit code 0 and no Lean warnings or errors. Searches used LeanFinder, Loogle,
and Mathlib grep through `msearch.py`, plus source-library `rg`; the published
single/unit comparison supplies the needed witness directly.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.ProEtale.RationalP1.singleUnit_existsUnique`
(node `def-sfb-projective-diagonal-pullback`).

The item originally had 1 `sorry` and now has 0. Added 0 holes; split off 0 theorems.
No `sorry` remains in any delivered module.

## No longer needed

None. No imports, nodes, or modules are pruned. The existing canonical pullback
and tensor constructions remain needed, and the proof uses the already imported
native single/unit comparison without adding a dependency.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows the existing normalization argument in the theorem docstring.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
