## What changed

Proved `WeilConjectures.isIso_of_surjective_etale_pullback` in
`Sheaf.Paper.EtaleIsoDescent`, preserving its complete statement and public imports.
The proof makes the singleton etale surjection a pro-etale cover, uses the source
library's proved inverse-image/restriction comparison and covering conservativity,
transports reflection through the existing finite-coefficient realization equivalences,
and reflects all cohomology maps before using the unbounded derived isomorphism criterion.
The full-subcategory inclusion gives the requested bounded constructible isomorphism.

Added three proof imports: the source-library modules
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
Updated `lem-pur-etale-iso-descent`'s proof, proof dependencies and proof origin to match.
No statements, definitions, universes or public visibility changed; no consumers need adaptation.
The complete module compiled cleanly through `lcompile.py` in 4.1 seconds.
All three new proof imports passed the repository import-direction check.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.isIso_of_surjective_etale_pullback`
(node `lem-pur-etale-iso-descent`).

Holes closed: 1. Holes added: 0. Holes remaining in this module: 0.
No new declarations or modules were added. Existing dependencies retain their own
proof obligations; this delivery does not claim their transitive axioms are closed.

The argument covers the empty base, the identity cover, zero and shifted complexes,
and positive coefficient levels including level 1: no step requires a chosen point,
nonzero object, Tor amplitude or etale-origin hypothesis. In fact the conservativity
argument applies to arbitrary objects of the ambient derived category; the original
bounded constructible and scheme hypotheses are preserved exactly.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

Pruned declared dependencies `det-pe-morphisms-etale-comparison`,
`lem-weil-pbc-flat-lfp-open`, and `lem-weil-pbc-affine-scheme-qcqs`:
Mathlib's existing `lem-pur-etale-proetale-cover` gives the covering condition directly,
and the weakly etale instance is already supplied by Mathlib.

Pruned `lem-weil-proetale-weakly-etale-localization`,
`def-pur-localized-ringed-site`, and
`lem-pur-site-restriction-module-adjunction-exact`: the source library already proves
`upperStarIsoLocalizationRestriction` and
`isIso_of_isIso_localizationRestriction` for fixed-scalar sheaves. Conjugating by the
canonical intrinsic realization equivalences gives conservativity without the generic
ringed-site restriction interface or its unproved exactness lemmas. Removed all three
obsolete top-level `tool_uses` approvals; no approvals were added or reordered.

The removed source dependency `SfIntrinsicRealizationTransport` is unnecessary:
the inverse-image functor's actual definition in `ProEtaleIntrinsicFiniteOperations`
already is a composite of the canonical realization equivalences with fixed-scalar
pullback. No direct-image normalization theorem is used.

The cohomology and fullness steps of the unit's local-to-global route remain intact.
No unit or chapter record changed and no module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned explicit graph calculation, generic ringed-site transport and handwritten
sheaf gluing are unnecessary: the source library already has the exact comparison and
cover-conservativity lemmas. The revised proof uses these existing constructions and
retains the intended cover-locality argument. It makes no universal conservativity
claim about pro-etale geometric stalks. No statement defect was found.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
