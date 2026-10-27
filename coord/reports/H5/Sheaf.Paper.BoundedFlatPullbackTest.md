## What changed

Proved `AlgebraicGeometry.ProEtale.BoundedFlatPullbackTest.bounded_flat_pullback_test`
without changing its statement. The test functors use a shared generic tensor-test
construction; their mathematical objects and maps are unchanged (definitionally equal). The proof obtains
termwise flatness from the existing fixed-scalar pro-etale flat-pullback instance (finite
rings are Noetherian), and K-flatness from the generic categorical bounded-above criterion.
It constructs the comparison as a natural isomorphism on the product category using the
canonical localization tensorator, then proves strict and derived cohomology vanishing.
Eight proved private helpers package tensorator naturality, K-flat invertibility, the
natural comparison and strict/derived vanishing. The public implementation helper
`tensorTestFunctor` shares the product/tensor construction, and is explicitly defined.
A symbolic-coefficient helper checks the localization tensorator before specializing
to ModuleCat. The complete module compiled with zero holes in 32.5 seconds. The definition change
and zero downstream consumers are recorded in
`coord/changes/bounded-flat-test-functors.md`.
The item's node records the actual route. All existing public imports are retained.

The comparison applies to every target-side module sheaf: only its first factor is K-flat.
The proof does not assume that the target sheaf descends to the source. The argument also
works for the zero ring, an empty scheme, and a single-degree interval; it does not use
`c ≤ d`, and an empty interval forces the original complex to be zero.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.BoundedFlatPullbackTest.bounded_flat_pullback_test`
(node `lem-exc-bounded-flat-pullback-test`), the only original hole.
Added: none. Remaining holes in the delivery: none. No new axiom. The only new public declaration is the fully constructed
implementation helper `tensorTestFunctor`, attached to the existing item node.

## No longer needed

Removed these private proof imports and their planned proof dependencies from this item:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
  (`prop-weil-pbc-proetale-constant-exact`): the existing fixed-ring `upperStar` already
  has the additive/exact instances used by `mapDerivedCategoryFactors` and `map_isZero`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
  (`lem-weil-pbc-ringed-topos-flat-module-pullback`): the proved fixed-scalar instance
  `lem-sfb-proetale-fixed-scalar-pullback-flat` directly applies, since finite rings
  are Noetherian. No intrinsic module equivalence needs to be constructed here.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (`lem-pc-bounded-above-flat-kflat-site`): the existing generic categorical criterion
  `lem-sfb-bounded-above-flat-kflat` proves the precise K-flat predicate directly.
- `Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`
  (`lem-weil-derived-tensor-resolution-independent`): the canonical tensorator of the
  existing derived monoidal structure and its K-flat invertibility provide the full
  two-variable natural comparison, using `lem-kun-derived-tensor-well-defined`.

The four obsolete tool-use approvals are removed from the item's node. No module is
withdrawn, and no claim is made that these modules are unused by other items. The exact
constant-coefficient theorem remains a statement dependency, whose field is unchanged.
The replacement generic tools are already stated/proved declarations, not new nodes.

## Where the brief, the DAG or earlier work was wrong

The planned intrinsic ringed-site declarations do not directly accept the fixed-ring
`Sheaf J (ModuleCat A)` arguments of this item's statement. The source library already
contains the necessary generic categorical and fixed-scalar APIs. Using them preserves
every clause and the blueprint's bounded-flat-model route, while avoiding unnecessary
transport between the two presentations.

The fixed-scalar flat-pullback node is a general tool for the flat-model calculation;
the bounded-above K-flat node is a general homological tool; and the K-flat tensor
comparison node supplies the canonical comparison of the existing derived tensor.
They do not replace any step of the unit's route.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
