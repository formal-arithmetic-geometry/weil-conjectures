## What changed

Proved `AlgebraicGeometry.ConormalGradedAlgebra.existsUnique_baseChangeMap` from
canonical comparisons of ideal powers and the presentation coproduct. The proof
uses uniqueness of left adjoints to move the ambient power comparisons to the
conormal pieces. It checks the affine formula, both normalizations, ring-sheaf
adjoint, uniqueness, epimorphism, and flat isomorphism.

Added four proved helper modules: `IdealTensorPullbackComparison`,
`ConormalAlgebraAffineGenerators`, `ConormalAlgebraHomogeneousRingMap`, and
`ConormalAlgebraRingAdjoint`.
All existing public signatures and public imports are preserved. No source-library
module, target, presentation definition, or consumer is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ConormalGradedAlgebra.existsUnique_baseChangeMap`
(node `lem-pur-conormal-algebra-flat-base-change`).

Added zero holes. The four new public helper theorems are proved:
`AlgebraicGeometry.existsUnique_idealTensorPullbackComparison`,
`AlgebraicGeometry.ConormalGradedAlgebra.affine_homogeneous_induction`,
`AlgebraicGeometry.ConormalGradedAlgebra.homogeneous_preserves_ringOperations`, and
`AlgebraicGeometry.ConormalGradedAlgebra.exists_ringAdjoint_of_homogeneousFormula`.
No declaration in the delivery contains `sorry`; no statement is split off unfinished.

## No longer needed

The explicit affine tensor-quotient and cover-gluing route is replaced by the
comparison on ideal powers, functoriality, and categorical coproduct arguments.
Removed these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackIdealQuotient`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`
- `Mathlib.Topology.Sheaves.LocallySurjective`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.TensorProduct.Quotient`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`

Removed these direct proof dependencies from the item's node:

- `lem-pc-closed-subscheme-base-change-ideal-image`
- `lem-weil-pbc-module-pullback-ideal-quotient`
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-weil-pbc-module-pullback-affine-sections`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-spec-module-tilde-sections`
- `def-pc-module-pullback`
- `lem-pur-sheaf-hom-cover-gluing`
- `def-weil-pbc-graded-sheaf-structures`
- `lem-weil-pbc-locally-surjective-iff-stalks`
- `lem-weil-pbc-flat-morphism-affine-criterion`
- `lem-weil-pbc-flat-tensor-exact`
- `lem-weil-pbc-tensor-quotient-base-change`

This records pruning from this item's direct proof route. It does not withdraw
source declarations or assert those modules are unused elsewhere or in the
transitive dependencies of the generic ideal comparison. The retained structure-
sheaf and conormal-functorial tool approvals stay in their original order.

## Where the brief, the DAG or earlier work was wrong

The original nine-step plan is valid but unnecessarily long given the existing
ideal-product image theorem and exactness of flat module pullback. In every degree,
compare the pulled-back ideal power with the extended power before applying the
closed-immersion pullback. This gives epi and flat isomorphism directly, without
constructing affine tensor-quotient identifications and gluing their inverses.
The statement is unchanged, including degree zero, degree one, arbitrary-base
epimorphism, and all-degree flat isomorphism.

Edge cases checked: zero and unit ideals, degree zero, identity base change, empty
opens and schemes, and nonflat base change. The proof never assumes nonzero rings
or flatness for epimorphism. Flatness is used only to preserve monomorphisms of the
ideal-power inclusions. The orientation unit still uses the complete graded
comparison and the prescribed degree-one normalization.

## New nodes

`lem-pur-ideal-tensor-pullback-comparison` records the image-factorization comparison
from a tensor pullback of an ideal to its extension. It is unique, epi, and iso
under flatness, with a complete proof.

`lem-pur-conormal-algebra-affine-generators` records additive induction on homogeneous
ideal-power representatives using the affine presentation chart and direct-sum and
quotient induction. It is proved, including the actual lift to the power-module section.

`lem-pur-conormal-algebra-homogeneous-ring-map` records the affine algebra-law check.
An additive map with the homogeneous ideal-power formula preserves one and products.
It is proved by lifting products and applying homogeneous induction in both variables.

`lem-pur-conormal-algebra-ring-adjoint` records descent of the ring laws of a module
map with the local homogeneous formula. The proof checks the laws on a compatible
affine cover, constructs the ring-sheaf map, and checks structure scalars by linearity.

Change record: `coord/changes/ConormalAlgebraFlatBaseChange-local-elaboration.md`.
Preflight requires this record for the added local irreducibility attribute and
backward-elaboration options. No existing statement or definition changes.


Validation: remote single-file and import-order compilation of all five modules;
final delivery preflight checks compilation, declarations, axioms, and the DAG packet.
The complete profiled import-order compile passed in 29.8 seconds; the assigned
module also passed a single-file compile in 25.3 seconds. One delivery compile
exceeded 60 seconds without pushing; profiling and a fresh complete compile
confirmed the proof compiles within the unchanged limit.

Preflight metadata repair: recorded an explicit LeanSearch query for each new
node, in addition to the Loogle/LeanFinder and source-grep searches, and added the
required record for local elaboration commands. All five modules compiled; the
first server axiom probe timed out and is rerun by delivery and landing checks.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
