## What changed

Proved `scalarPullbackIso_existsUnique` from separately proved existence and uniqueness
components, preserving its statement and the chosen comparison definition. The existing
mate/projection proof is unchanged.

Validation: `lcompile.py --all` compiled all five sandbox modules successfully, including
the two unchanged representative/normalization dependencies. The assigned module and both
new proof modules contain zero holes.

The private scalar-invariance argument follows the already proved implementation in
`Sheaf.SixFunctors.EtaleHomComparisonModels`; the generic counit identity is reused from
`Sheaf.CategoryTheory.DerivedAdjointCochainCounit`. No adopted source module changes.

The existence argument identifies the scalar-extension representative with the canonical
derived counit, proves it invertible on K-flat complexes, and compares the two natural
normalization paths on reduced functorial flat resolutions. Their invertible restrictions
supply a natural isomorphism, which descends through localization. Naturality along the
resolution map proves the normalization equation. Uniqueness cancels the same representative
maps on flat resolutions and then uses naturality and localization extensionality.

Private natural transformations store the specified representatives as their components.
Their generic counit and invertibility APIs keep the resolution argument abstract and
avoid expanding the chosen adjunction while checking the normalization equation.

## Proved and sorry left

Closed the assigned module's one original hole,
`AlgebraicGeometry.Etale.scalarPullbackIso_existsUnique`.

The new components `AlgebraicGeometry.Etale.scalarPullbackIso_exists` and
`AlgebraicGeometry.Etale.scalarPullbackIso_unique` have complete proof bodies. No holes are
added. The unchanged dependency `AlgebraicGeometry.Etale.scalarTensorPullback_normalization_kFlat`
still contains its existing hole. No definitions contain `sorry`.

## No longer needed

The new proof does not invoke `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
the general ringed-topos scalar/pullback existence theorem.
It constructs the comparison directly in ordinary small-etale module categories. No existing
module or declaration is withdrawn, and the assigned module's public imports are preserved.
The new proof modules publicly import only the shared representative data; their construction
and resolution imports are private proof imports. The uniqueness module does not import the
existence module.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The prior definition node had no proof steps; its proof
now records the two components. The component nodes depend on the representative data and
flat-resolution theory, rather than on the parent comparison, avoiding a dependency cycle.

## New nodes

`lem-pur-etale-scalar-pullback-existence`, realized by
`Sheaf.Paper.ScalarPullbackIsoExistence`, constructs the normalized comparison.

`lem-pur-etale-scalar-pullback-uniqueness`, realized by
`Sheaf.Paper.ScalarPullbackIsoUniqueness`, proves that two normalized comparisons coincide.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
