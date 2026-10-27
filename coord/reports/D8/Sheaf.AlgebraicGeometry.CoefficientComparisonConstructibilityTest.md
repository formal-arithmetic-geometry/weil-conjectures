## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.coefficientComparison_constructibilityTest` by an argument
using the same finite partition on each affine open in both directions. The theorem
statement and all existing public imports and definitions are unchanged.

The forward implication uses the proved general site theorem
`CategoryTheory.coefficient_finite_local_systems_pullback` and upgrades the finite
module models to finite presentation by Noetherianity. The converse forgets finite
presentation to finite generation and uses single-stratum reflection. The record
conversions retain every stratum scheme, immersion, set, and covering property.
Isomorphism transport of local models is proved directly by restriction to slices.

Added two modules: `CoefficientComparisonFixedPullback` supplies the compatibility
between intrinsic comparison, scalar restriction, and scheme inverse image;
`CoefficientComparisonFiniteReflection` isolates reflection of finite local systems
in the independent coefficient universe. Both concern individual sheaves, without
any finite stratification or constructibility assertion. They are strictly smaller
than the item. The scalar compatibility uses equivalence of scalar restriction, its sectionwise
direct-image compatibility, and uniqueness of adjoints. Local explicit sheafification
instances keep typeclass search in the common site and coefficient universe. The direct-image
identity is checked using the actual pro-etale section module and constant-ring unit.

Updated the item's proof route and created nodes for the two new interfaces.
No upstream module, target, statement signature, or existing definition is changed.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.ProEtale.coefficientComparison_constructibilityTest`
(node `lem-pe-coefficient-comparison-constructibility-test`).

Proved the new theorem
`AlgebraicGeometry.ProEtale.coefficientComparison_fixedPullback`
(node `lem-pe-coefficient-comparison-fixed-pullback`), together with its private helpers.

Added one direct hole, in the whole proof of
`AlgebraicGeometry.ProEtale.coefficientComparison_finite_reflect`
(node `lem-pe-coefficient-comparison-finite-reflection`). Its complete argument and
source are in its docstring and node. This delivery is a decomposition: one old hole
closed and one strictly smaller hole added, net zero. The item contains zero direct
holes; the packet contains one direct hole. No definition contains a hole.

Validation: the complete sandbox compiles without warnings through lcompile.py --all:
FiniteReflection 7.3 s, FixedPullback 34.2 s, ConstructibilityTest 19.2 s. All three
files are below the 60-second limit. Temporary diagnostic options and temporary
compatibility assumptions used during development have been removed.

## No longer needed

The item no longer directly needs `sk-thm-pe-direct-image-comparison` or its module
`Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: no derived direct image
appears in the argument. Ordinary inverse-image composition is obtained by uniqueness
of adjoints to sectionwise direct images in `CoefficientComparisonFixedPullback`.

The item no longer directly imports `det-pe-finite-local-systems-twist` or
`det-pe-classical-sheaves-modules`. Their mathematical content is still needed below
the new coefficient-sized single-stratum reflection node. They are not withdrawn.

No original import line was removed: the original sole public import supplies the
statement. No existing module is withdrawn. No whole-library pruning is claimed.
The unit's finite-local-system route is retained on each stratum; the classicality,
essential-surjectivity and derived arguments of the unit remain with other modules.

## Where the brief, the DAG or earlier work was wrong

The original single proof step asserts that the existing finite-local-system theorem
can be applied to the independently sized coefficient ring. Its Lean interface uses
`Λ : Type u` and `ULift Λ`, while the item uses arbitrary `A : Type (max v (u+1))`.
The classical module theorem likewise fixes the module universe to `u+1`.
Neither can be instantiated directly with the arbitrary coefficient ring here.
The new reflection node states only the needed single-stratum extension of the same
proof; it does not repackage constructibility or assume its desired conclusion.

The planned gluing of affine-local partitions is unnecessary for this property test:
each implication retains the already supplied partition separately on every affine
open. No claim of a single global stratification is made. This does not change the
unit's classicality proof, which addresses a different assertion.

Edge cases read against the statements: empty scheme and empty partition; empty cover
members; zero coefficient ring; zero module; infinite Noetherian coefficients such as
integers; arbitrary non-quasi-compact base schemes. No point, nonzero module, finite
underlying coefficient set, or quasi-compactness assumption has been added.

## New nodes

`lem-pe-coefficient-comparison-fixed-pullback`, in
`dag/nodes/sec-proetale-coefficients/`, records the natural isomorphism of the actual
intrinsic-module and fixed-scalar inverse-image composites. Its proof verifies the
constant-section ring-map equation and takes the adjunction mate of the fibre-product
site isomorphism. It has no Noetherianity or constructibility hypothesis.

`lem-pe-coefficient-comparison-finite-reflection`, in the same directory, records only
reflection of the finite local-model condition for a fixed-scalar sheaf on a single
scheme. Its proof follows Stacks Tag 099Y and comparison full faithfulness, with
Noetherianity providing finite presentation. Neither intrinsic scalar extension nor
finite partition witnesses occur in its statement. No change record is required:
existing statements and definitions are preserved, and the item receives proof imports.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
