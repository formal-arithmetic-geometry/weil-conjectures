## What changed

Filled `AlgebraicGeometry.Etale.supported_kummer_scalar_source` without changing its
signature, `supportedScalarMap`, or any public import. The coefficient maps are actual
constant-sheaf adjuncts of the map sending 1 to 1. Private proved helpers establish their
generator formulas, convert the specified coefficient-comparison isomorphism to the
required derived universal property, transport along identity pushforwards, and prove
the unit square by equality on constant-presheaf generators.

The proof reuses the first conjunct of the existing `geoCartierCoeffExtension` declaration
in `Sheaf.SixFunctors.GeoCartierCoeffExtension`; the second coefficient map is the identity.
Its normalized `coefficientUnitModule` is identified with the direct image of the constructed
constant coefficient map. The proved upstream `constantSheafUnit_app_toSheafify` supplies
the pushforward-unit formula. Both are proof-only imports. The DAG proof, dependencies
and origin now record this route. No unit statement or realized unit step is bypassed.

The proof-scope change record is
`coord/changes/D3-supported-kummer-scalar-proof-scopes.md`. It records only private
helpers and local elaboration settings, with the original public contract preserved.

The unclaimed `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar` also receives a
equivalent generic-functor presentation of `SupportedDerivedScalarUnit`
and a proved categorical transport API. This avoids expanding chosen derived
localizations in every use. Its original signatures and public imports are preserved.
The definition change and consumer check are recorded in
`coord/changes/D3-supported-scalar-universal-api.md`; semantic review is reopened, with
equality of meaning checked by unfolding `CategoryTheory.IsScalarExtensionUnit` and
reassociating with `Category.assoc`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.supported_kummer_scalar_source`
(node `lem-asd-supported-kummer-scalar-source`). No holes remain in the delivered module;
none are added or split off. The repaired `OrdinarySupportedKummerScalar` module has
zero original holes and zero remaining holes; its generic predicate is an actual definition
and its transport theorem is proved. All private helpers are proved. The existing imported theorem
`AlgebraicGeometry.Etale.geoCartierCoeffExtension`
(node `lem-geo-cartier-coeff-extension`) remains a dependency with its pre-existing proof
obligation; this delivery does not claim to prove it.

The argument handles empty support, identity immersion, N=1, zero rings, and nonflat finite
coefficient extensions without adding assumptions.

Validation: both edited modules compile cleanly (26.0 and 51.7 seconds). Unchanged
`OrdinarySupportedKummerSystem`, `CartierKummerMap`, and `OrdinarySupportedCartierKummer`
compile against the repaired definition and proved item (47.5, 47.1, and 40.6 seconds).
`#print axioms CategoryTheory.isScalarExtensionUnit_transport` reports only `propext`,
`Classical.choice`, and `Quot.sound`. The item also reports `sorryAx` inherited from its
existing holed dependency; the delivery introduces no axiom or new hole.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

Removed these old direct proof dependencies (the specialized stalk/K-flat construction
is replaced by the already stated canonical coefficient-extension comparison):

- `def-kun-derived-tensor`
- `def-pc-kflat-complex`
- `def-pur-sheaf-tensor-product`
- `def-weil-closed-immersion`
- `def-weil-finite-integral-morphism`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-pur-derived-change-of-rings`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-finite-stalk-formula-restriction`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `prop-weil-pbc-geometric-stalks-exact`
- `sk-lem-pbc-finite`

The obsolete top-level tool approvals withdrawn are
`sk-lem-pbc-finite`, `lem-weil-pbc-finite-stalk-formula-restriction`,
`lem-pod-etale-stalk-tensor-scalar`, `lem-weil-pbc-exact-functor-derived-functor`, and
`lem-pur-derived-change-of-rings`. The new use of `lem-geo-cartier-coeff-extension` is
recorded in the proof for independent review; maintainer tool approvals are not added
by this worker.

These are removals from this node's direct route only. Some remain statement dependencies
or transitive dependencies of the reused theorem, and no global withdrawal is requested.
No module is deleted, and no source-library declaration or import is changed.

## Where the brief, the DAG or earlier work was wrong

The original six-step proof is mathematically applicable, but its stalk and K-flat
construction need not be repeated here: `geoCartierCoeffExtension` already states the
canonical supported scalar comparison for arbitrary finite coefficient rings and closed
immersions. Its canonical map, not merely an unspecified isomorphic object, suffices.
The residual normalization and unit compatibility are proved explicitly in Lean.
No false statement was found. The old concrete universal-property body was too expensive
to use within the compile limit, so its implementation was refactored to the same formula
with abstract functors and proved categorical API lemmas. All original quantifiers,
objects, maps and hypotheses are retained.

## New nodes

`lem-asd-scalar-unit-transport-api` records the fully proved elementary invariance API:
transport through ordinary source and target isomorphisms preserves those bijections.
It adds no hole. LeanSearch, LeanFinder, Loogle, and source grep searches are recorded;
none states this predicate-specific naturality combination. The API is part of the
repaired existing definition module; no part
of the item module was moved to a new module.

Change records: `coord/changes/D3-supported-scalar-universal-api.md` and
`coord/changes/D3-supported-kummer-scalar-proof-scopes.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
