## What changed

Completed `Sheaf.AlgebraicGeometry.ProfiniteSchemeProductComponents` without changing any
existing signature, definition, attribute or public import. Added proved private helpers
and proof imports. The theorem now explicitly constructs every field of
`ProfiniteSchemeProductComparisons`: group and finite-power topology, the specified scheme
limit and ring colimit, affine and open-base-change comparisons, the global homeomorphism,
component quotient, and all normalization and naturality equations.

The affine comparison uses the actual coefficient-ring pushout, proved using the existing
`LocallyConstant.liftPrimeSpectrum`, `specMap_liftPrimeSpectrum` and
`ringHom_ext_of_specMap` API. Its Spec pullback identifies the actual product in the
statement. Finite-section coproducts use the proved `finite_labels` helper from
`RelativeProfiniteTestLabels`; the scheme limit uses the proved `lc_limit` helper from
`ProfiniteTestObjectFunctor`. The global topology is checked on affine charts without
assuming affine intersections. Updated the existing node's proof and dependency list to
this implementation. No new nodes or mathematical interface changes. The two auxiliary instance registrations
are file-local. The command scanner requires the elaboration settings and registrations
to have a change record: `coord/changes/H5-profinite-product-proof-local-settings.md`.

Server compilation passed for the complete proof, with no warnings, in 32.5 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The delivery
preflight performs the final compile and axiom checks. Edge cases are included in the Lean arguments: zero powers,
empty schemes, zero coefficient rings and disconnected bases in all clauses except those
explicitly assuming `ConnectedSpace`.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Scheme.UniversalCover.profinite_scheme_product_components`
(blueprint: `lem-sfb-profinite-scheme-product-components`).

Added 0 holes; split off 0 statements. No `sorry` remains anywhere in the delivered Lean
module, including private helpers and definitions. Existing dependency modules are used
as library results; they are not changed in this delivery.

## No longer needed

Removed the private proof import `Mathlib.Topology.Algebra.ClopenNhdofOne`: the full
canonical group-limit homeomorphism already exists in Mathlib. Also removed two unused
imports left in the earlier sandbox work:
`Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit` and the redundant
`import all Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`.
The public `PointedLimitCech` import remains unchanged. Removed the redundant explicit
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` proof import as well: this module
is already publicly imported by `PointedLimitCech`.

The DAG no longer directly needs `lem-sfb-profinite-group-open-normal-subgroup-basis`
or `lem-sfb-compact-closed-finite-intersection`: their work is already contained in
Mathlib's proved `continuousMulEquivLimittoFiniteQuotientFunctor` and
`toLimit_surjective`. No project Lean module is withdrawn or deleted. All other declared
dependencies are used by the proof. The Spec small-colimit/limit fact is also used on the
coefficient pushout. The relative-label and test-object-functor nodes remain needed via
their proved finite-family and locally constant limit helpers.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The planned reconstruction of the group quotient
homeomorphism duplicates a proved Mathlib result. The planned affine-limit comparison can
be obtained more directly from the actual coefficient-ring pushout; this also makes its
normalizations explicit. Earlier H5 sandbox work was present when this session resumed;
it was preserved, checked and completed. Its remaining open-chart image proof had an
equality in the wrong orientation, and the finite-quotient naturality and final package
assembly were unfinished. These are now repaired and proved.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
