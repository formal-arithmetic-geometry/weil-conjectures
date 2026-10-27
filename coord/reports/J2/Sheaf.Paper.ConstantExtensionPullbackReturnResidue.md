## What changed

Proved two existing helper theorems in
`Sheaf.Paper.ConstantExtensionPullbackReturnResidue`, preserving every declaration's
signature and every definition's body.

* `WeilConjectures.constantExtensionCoordinate_succ`: rewrite the successor exponent,
  expand automorphism multiplication, and reassociate the composite.
* `WeilConjectures.constantExtensionResidue_compatible`: apply faithfulness of `Spec.map`,
  use the geometric characterization of each base-field residue embedding and naturality
  of the canonical residue-field point, and finish with the projection's over-morphism
  equation. Added the private proof import `WeilConjectures.PointCount` for
  `Scheme.Hom.specMap_residueFieldAlgebraMap`.

The residue proof uses a declaration-local transparency option and suppresses only its
unused-section-variable warning, retaining the existing three scheme hypotheses verbatim.
No data is chosen from an existence theorem. No source-library module is changed.

## Proved and sorry left

Closed 2 of the 4 original holes:

* `WeilConjectures.constantExtensionCoordinate_succ`.
* `WeilConjectures.constantExtensionResidue_compatible`.

The following 2 original public theorem holes remain unchanged, with their existing
source and complete proof plans, both attached to
`lem-zl-constant-extension-pullback-return-residue`:

* `WeilConjectures.constantExtensionPullbackReturn`.
* `WeilConjectures.constantExtensionResidueCompositum`.

Added holes: zero. Split-off statements: zero. This is a partial proof delivery,
not a decomposition. No claim is made that the two remaining theorems are proved.

## No longer needed

Removed the following private imports, unused by the two completed proofs or any
statement or definition in this file:

* `Sheaf.CategoryTheory.CyclicReturnExactEquivalence`.
* `Sheaf.AlgebraicGeometry.ClosedPointField`.
* `WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField`.
* `Mathlib.FieldTheory.Finite.Basic`.
* `Mathlib.LinearAlgebra.Dimension.Free`.

These remain mathematical dependencies of the two untouched theorem proof plans;
this delivery does not withdraw their nodes or modules or remove their DAG edges.
In particular, no module is claimed to be globally pruned. The original DAG route
and the unit's realized statements and steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The two helper proofs require only the elementary
composition identities already described in their docstrings. The base-field embedding
naturality API is in `WeilConjectures.PointCount` and needs a direct private import
under the module system. The actual category-level automorphism multiplication is
reverse composition, accounted for explicitly by `Aut.Aut_mul_def`.

Validation: the final single-file compile through `lcompile.py` succeeded without
warnings (9.4 seconds of compiler time).

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
