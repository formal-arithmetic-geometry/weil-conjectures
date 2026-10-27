## What changed

Filled `AlgebraicGeometry.Scheme.Modules.relative_flat_cartier_support` with the affine
power-torsion and sheaf uniqueness argument. Relative flatness supplies the restricted-scalar
flat module on each affine pair. Mathlib's
`Module.Flat.isSMulRegular_of_nonZeroDivisors`, applied to `a ^ n`, supplies injectivity;
`map_pow` identifies the scalar with the required pulled-back power. The existing proved
`exists_pow_smul_eq_zero_of_isAffineOpen` supplies power annihilation. For arbitrary opens,
choose affine Cartier charts at each point, restrict the difference of the two sections,
identify the principal complement using `basicOpen_appLE` and `mem_support_iff_of_mem`, and
apply sheaf uniqueness on the point-indexed affine cover.

The node's second proof step records the existing Mathlib corollary implementing its tensor
argument. The mathematical dependencies and unit route stay the same. No existing statement,
definition, attribute, or public import changes.

Searches: `msearch.py` LeanFinder for flat-module regular-scalar injectivity found
`Module.Flat.isSMulRegular_of_nonZeroDivisors`; Loogle returned its exact signature; grep
confirmed the declaration in `Mathlib/RingTheory/Flat/TorsionFree.lean`. Read that proof,
the localization declaration, all stated dependency signatures, the local Cartier predicate,
the current unit blueprint, and Stacks 080F/07ZP. The Mathlib corollary is exactly the algebra
step; none of the searches supplies the complete scheme-module statement.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Modules.relative_flat_cartier_support`
(node `lem-trf-relative-flat-cartier-support`). No holes added or split off; no sorry remains
in the delivered module. No additional assumptions are introduced. The proof includes `n = 0`,
unit Cartier equations, the zero module, empty source/opens, arbitrary non-quasi-compact opens,
and morphisms whose image is contained in the divisor.

Validation: `lcompile.py` compiled the final module cleanly in 4.5 seconds, with no warnings.
The delivery command runs the required independent compilation and axiom probe.

## No longer needed

No DAG nodes or modules are pruned: the original tensor-injectivity dependency is used through
Mathlib's proved regular-scalar corollary, and the affine localization dependency remains used.
The separate tensor-unit calculation and power induction are already implemented by Mathlib
and `pow_mem`. Removed the redundant proof import `Mathlib.RingTheory.Flat.Basic`: the Cartier-ideal
public API already exposes `Mathlib.RingTheory.Flat.TorsionFree`, which provides the algebra
corollary. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned explicit tensor proof and power induction have a
shorter existing Mathlib implementation, recorded in the node's second proof step. No new
nodes or definition repairs are needed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
