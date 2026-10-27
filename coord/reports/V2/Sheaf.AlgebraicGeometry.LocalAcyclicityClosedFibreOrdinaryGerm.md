## What changed

Filled the proof of `AlgebraicGeometry.Etale.closedFibre_unit_stalk_comparison`
without changing its statement. The proof constructs the base, source-stalk and
target-stalk isomorphisms and proves the actual unit equation using naturality,
the unit form of the ordinary base-change mate, and transport of pullback of sections.

Added a proved transport helper and a strictly simpler ordinary-exchange obligation:
`Sheaf.AlgebraicGeometry.GlobalSectionsIsoOverTransport` and
`Sheaf.AlgebraicGeometry.StrictLocalOrdinaryDirectImageComparison`.
The latter records the remaining degree-zero strict-local exchange step and its
proof from the small-model strict-local base-change theorem on global homology.
The former proves a general transport identity without any strict-local geometry.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.closedFibre_unit_stalk_comparison`
(node `lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ`).

New proved declaration: `AlgebraicGeometry.Etale.globalSections_iso_over_transport`
(node `lem-weil-pbc-global-sections-iso-over-transport`).

Added one strictly intermediate hole:
`AlgebraicGeometry.Etale.isIso_strictLocalOrdinaryDirectImageComparison`
(node `lem-weil-pbc-strict-local-ordinary-direct-image-comparison`).
This is a decomposition: one original hole closed and one new hole added.
Dependencies retain their
own existing obligations; this packet does not claim to close those obligations.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations`: the already proved
  strict-fibre comparison encapsulates the geometric argument.
- `WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso`: it concerns the
  adopted strict-local model; the proof uses the general pointed-section-cone criterion
  directly with the small-model residue lift.
- `WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm`: the proof needs only
  ordinary restriction naturality, which is proved directly from its germ colimit.
- `WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate`: the ordinary
  unit identity suffices; no injective-representative section calculation is needed.
- `WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`: ordinary
  exchange invertibility comes directly from small-model base-change on global homology,
  avoiding model transport of the full cohomological stalk formula.
- `Sheaf.CategoryTheory.DerivedAdjunctionSingleZero`: the ordinary unit calculation is
  entirely underived. The helper uses the generic right-derived unit on H^0 instead.
- `WeilConjectures.SixFunctors.BaseChange.Square` and
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: their declarations remain
  available through imports needed for the actual proof.

The corresponding direct DAG dependencies removed are
`lem-weil-pbc-strict-base-closed-point-localizations`,
`lem-weil-pbc-strict-local-germ-restriction-iso`,
`lem-weil-pbc-strict-local-localized-hom-germ`,
`lem-weil-pbc-strict-local-underived-sections-mate`,
`lem-weil-pbc-unrestricted-strict-henselization-stalk`, and
`lem-weil-pbc-derived-adjunction-single-zero`.
`lem-weil-pbc-left-exact-injective-resolution-degree-zero` and
`lem-weil-pbc-inverse-image-composition` move to the helper nodes that use them.
No upstream declaration or module is withdrawn. Geometric dependencies encapsulated
in the strict-fibre theorem remain needed by that theorem. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

Several original proof imports describe `strictLocalization`, while the item and
`localAcyclicityAlpha` use `strictHenselizationScheme`. These models are canonically
isomorphic, but are not definitionally equal. The new proof uses the small-model
base-change-on-global-homology statement and the general section-cone criterion.

The adopted equality between the resolution-defined derived exchange and the
unbounded-derived mate asks for a flat-resolution instance on the coefficient category.
The bounded-below mate equality needed here follows directly from its generic
resolution factorization, avoiding that additional instance.

## New nodes

`lem-weil-pbc-global-sections-iso-over-transport` proves functorial transport of
pullback of sections along isomorphisms over a coefficient scheme. It has no stalk,
strict-local, closed-fibre, or direct-image assertion.

`lem-weil-pbc-strict-local-ordinary-direct-image-comparison` states only invertibility
of ordinary exchange after strict-local global sections. Its recorded proof uses the existing
small-model global-homology comparison and a degree-zero arrow isomorphism.
Neither new node restates the original comparison theorem.

Validation: the main proof compiles without warnings in 21 seconds. It uses general
categorical naturality and
composition helpers to avoid unfolding stalk colimits during rewrites. Local irreducibility
keeps the strict-local cone and inverse-image constructions abstract, and every delivered
module explicitly respects transparency. The original theorem statement is unchanged.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
