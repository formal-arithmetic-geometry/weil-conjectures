## What changed

Proved `AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization_pullback`
in the assigned module. The normalized witnesses, addition law and zero clause
come from `absoluteFrobenius_proEtale_trivialization`. The new proof establishes
naturality for every scheme morphism: iterated Frobenius commutes with it by
`map_pow`; the corresponding fibre-product maps agree on both projections;
presheaf functoriality gives the direct-image square; conjugation under the
module adjunction gives the ordinary pullback square. The proved source-library
exact-derived coherence API transports this square to the required derived one.

All auxiliary lemmas are proved private helpers. The public signature and its
docstring are unchanged. The item compiled cleanly in 18.1 seconds; a later
three-module candidate check compiled it in 51.4 seconds and compiled unchanged
FrobeniusStalkTrivializationNormalization (31.0 seconds) and
SchemeGeometricFrobenius (43.3 seconds) against it. Local
irreducibility attributes prevent repeated unfolding of concrete sheaf and
adjunction constructions; no settings are exported. No new public declaration,
definition or target change is made. The DAG proof now follows this calculation.

Change record: `coord/changes/B7-frobenius-trivialization-proof-interface.md`.

## Proved and sorry left

Closed one of one holes: `AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization_pullback`
(node `lem-pur-frobenius-trivialization-pullback`). The item has zero `sorry`s left;
zero holes were added and zero statements were split off. Its imported normalized
witness theorem remains an existing stage-3 dependency, not a new hole.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap` (public).
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition` (public).
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit`.
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.

Removed direct proof dependencies `prop-weil-pbc-proetale-constant-ring-map`,
`def-weil-pbc-proetale-site`, `lem-weil-pbc-conjugate-iso-unit-equation`,
`def-weil-pbc-composite-adjunction`, `lem-weil-pbc-site-morphism-composition`,
`lem-sf-proetale-tensor-composition-unit`, `lem-weil-pbc-mate-pasting`,
`def-weil-pbc-adjunction-conjugate`, `lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-proetale-derived-pullback-composition`, and `lem-pc-kflat-resolution`.
The corresponding six obsolete top-level tool-use approvals were withdrawn;
`lem-trf-absolute-frobenius-site` is retained. These results need not be invoked
again here: the witness already contains its normalizations, Mathlib supplies the
conjugation identities, and the source library proves exact-derived coherence.
Some removed imports remain transitively needed by AbsoluteFrobeniusSite or
other users; no global module-pruning count is claimed and no module is withdrawn.
The fixed unit statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The longer planned tensor-composition and K-flat/localization argument is
unnecessary given the current normalized AbsoluteFrobeniusSite declaration and
the proved exact-derived coherence API. Its open-restriction clause is not used
to justify arbitrary pullback: that strengthening is proved here geometrically
and sectionwise. No statement was found false or weakened. The previous attempt
had zero written holes but had not passed compilation; the final normalization
and elaboration issues have been repaired.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
