## What changed

The upstream rework defect was the private import of
`WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec` while the exposed
`antiEquivalence` and `algebraIso` definitions use `affine_morphism_relative_spec`.
The live module already contains the required public import from the earlier repair;
this delivery preserves it and removes the redundant private import of
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
The resulting module compiles in the sandbox. The `IsIso` clause of `affineChart_spec`
is now proved from the relative-spectrum chart and affine section bijection; its two
equations are isolated in the new intermediate theorem and node.

## Proved and sorry left

This delivery includes the listed quarantine/import repair and one strict proof decomposition.
Holes closed: 1 of 3. Holes added: 1. Split off: 1. The remaining theorem holes are:

- `AlgebraicGeometry.VectorBundleZeroSection.affineChart_equations`;
- `AlgebraicGeometry.VectorBundleZeroSection.trivializationMap_spec`;
- `AlgebraicGeometry.VectorBundleZeroSection.transition_spec`.

No definition contains a hole.

## No longer needed

The private import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` was removed.
All names it supplied remain available through the module's existing public imports;
`lcompile.py` verifies this. No DAG node or declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The upstream sync left the relative-spectrum theorem imported privately in the
quarantined archive, which makes the exposed definitions fail with an unknown
identifier. The earlier F3 repair had already promoted that import in the live file;
this packet confirms the repair and removes only the redundant private import. The
DAG's three theorem holes remain untouched because they are separate mathematical
proofs and are outside the listed import repair.

## New nodes

Added `lem-asd-vector-bundle-affine-chart-equations`, a strict equation part of
`affineChart_spec`. The parent node's proof and proof dependencies record this split.
The split theorem is the only new `sorry`; it is independent of the proved chart-isomorphism
clause and retains the two equations verbatim.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
