## What changed

Filled all seven theorem holes in `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`.
Every existing statement, public import, definition body and docstring is preserved.
Only private, proved/constructed helpers were added; no imports were added.
The local instance registration is documented in
`coord/changes/X8-proetale-isomorphism-local-continuity.md`; it is not exported.

Postcomposition equivalence uses `MorphismProperty.Over.mapComp`, `mapId` and the
existing `ProEt.coverPreserving_overMap`. The normalized inverse-image identification
is `Adjunction.leftAdjointUniq` between the recorded adjunction and the sheaf adjunction
lifted from `Over.mapPullbackAdj`. Its inverse is precisely the prescribed unit followed
by restriction along `proEtaleIsoCommaArrow`; equality of all inverse components gives
uniqueness. The provisional route node now records this actual argument.

The sheaf equivalence is assembled using continuous pushforward composition and identity
isomorphisms. Adjunction equivalence transfer proves the recorded unit and counit
invertible; Mathlib supplies arbitrary limit and colimit preservation and the canonical
`limit.post` comparison.

The constant comparison is identified with the isomorphism between the composite
constant-sheaf/inverse-image adjunction and the constant-sheaf adjunction at the
base-changed terminal object. This argument works for every value category in the
statement. Naturality uses the two adjunction Hom equivalences and naturality of
`toSheafification`.

For modules, base change and postcomposition give a continuous site equivalence.
`SheafOfModules.pushforwardPushforwardEquivalence` applies to the invertible recorded
coefficient direct-image map. In the commutative case the existing
`proEtaleRingModuleOperations_properties` adjunction transfers equivalence to the actual
tensor pullback, including the required unit and counit. For arbitrary rings the
constructed equivalence has exactly the specified pushforward as its inverse.

## Proved and sorry left

Seven original holes closed:

- `AlgebraicGeometry.Scheme.proEtaleIsoPostcompose_equivalence`.
- `AlgebraicGeometry.Scheme.existsUnique_proEtaleIsoInverseImageIdentification`.
- `AlgebraicGeometry.Scheme.proEtaleIsoInverseImage_equivalence`.
- `AlgebraicGeometry.Scheme.proEtaleIso_inverseLimitComparison`.
- `AlgebraicGeometry.Scheme.proEtaleIso_constantComparison`.
- `AlgebraicGeometry.Scheme.proEtaleIso_constantModuleEquivalence`.
- `AlgebraicGeometry.Scheme.proEtaleIso_constantRingModuleEquivalence`.

No holes remain in the item and no holes are added. No split-off declarations.
The complete module compiled in 9.5 seconds with no warnings. Two `simp?` calls
are retained: their suggested `simp only` replacements did not reproduce the successful
simplification across these semireducible wrappers. Final validation runs in deliver3.

## No longer needed

No existing imports removed and no modules withdrawn. Existing public imports are retained.
The proof needs no additional imports: `Adjunction.Unique` and
`ModuleCat.Sheaf.PushforwardContinuous` are already publicly available through the
existing imported interfaces.
No new Sheaf proof dependencies are imported. The normalized-identification route node now uses only the existing recorded
inverse-image interface. Its stage-1 statement and review were refreshed from the
current shared repository after a concurrent stage-1 landing. No unit statement or unit proof step is bypassed.

The route node no longer needs `lem-sfb-pointwise-kan-colimit`,
`lem-pur-kan-coprojection-unit-normalization`, or
`lem-weil-pbc-site-continuous-pushforward-sheaf`: lifted adjunctions supply the
normalization directly. Its obsolete approval of the last tool is removed.
The former proof dependencies `lem-weil-iso-weakly-etale`,
`lem-weil-pbc-weakly-etale-composition-base-change`, `def-weil-pbc-proetale-site`,
`def-pc-fibre-product`, and `def-weil-pbc-sheafification` are not separate proof
dependencies of this normalization theorem: their constructions and instances are
already carried by `def-weil-proetale-inverse-image`. The statement dependencies remain.
No corresponding library declarations or modules are removed.

For the proofs in this item, the general
`WeilConjectures.CategoryTheory.SiteEquivalenceMorphismOfSites` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso` are unnecessary:
the existing site-specific continuity instances and module adjunction replace their
planned uses. These are not withdrawn: the main node is attached to the separate
sectionwise interface and other consumers may still use them. No dense-subsite
sheafification lemma is needed for the constant comparison: the constant-sheaf adjunction
provides its canonical identification directly. No explicit comma-colimit construction
is needed: the existing lifted adjunction has exactly the required counit.

## Where the brief, the DAG or earlier work was wrong

The assigned module has seven, rather than eight, original theorem holes. The existing
main node `lem-weil-proetale-isomorphism-inverse-image` is attached to
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, which imports this item;
it cannot be imported here. At session start the directly attached route node was provisional, without numbered
proof steps. A concurrent stage-1 delivery supplied its exact natural-language statement
and eight-step proof. This delivery preserves that current statement and metadata and
records the shorter adjunction implementation, with unchanged mathematical statement.

The latest blueprint places `sk-def-purity-conv` under `sec-six-functors-basics`, whereas
the DAG's stored unit record gives its old smooth-purity location. The fixed unit and
chapter routes are unchanged.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
