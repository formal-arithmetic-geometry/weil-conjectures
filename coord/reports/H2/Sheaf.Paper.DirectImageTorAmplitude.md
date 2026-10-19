## What changed

Replaced the sole sorry in `AlgebraicGeometry.Etale.sf_directImage_torAmplitude` by a
proof from coefficient arithmetic, finite-type constructibility, the existing derived
upper-amplitude theorem, the finite constant projection formula, and the residue Tor test.
The theorem signature and all public imports are unchanged. The upper-amplitude theorem
replaces the truncation spectral sequence and its filtration machinery. The proof locally
marks `derivedTensor` irreducible to keep the tensor construction sealed during elaboration;
this local attribute changes no exported definition. The theorem docstring now describes
the implemented proof rather than the superseded spectral-sequence plan.

Repaired `Padic.coefficientExtensionRing`: it is now an ordinary definition with named
canonical quotient CommRing and Algebra instances. Its quotient construction and
operations are unchanged. This prevents expensive eager quotient/hierarchy unfolding when specializing
the generic module-sheaf derived-tensor argument. The original proof against the original
coefficient module exceeded the 60-second limit; the repaired version compiled.
The record `coord/changes/H2-coefficient-extension-ring-instance.md` contains the exact
old and new definitions and the full consumer inventory. All 24 original direct
importers, plus the residue-test module, compiled individually against the repaired
coefficient definition. This session also compiled the new direct importer
`Sheaf.NumberTheory.Padics.IntegersCosetBasis` and the newly listed textual consumers
`Sheaf.Paper.IntrinsicComparisonConstructibility`,
`Sheaf.Paper.IntrinsicComparisonTorAmplitude`, and `Sheaf.Paper.TwistFrobeniusScalar`
against the same repair; all four passed. The current item also compiled in 22.5 seconds.
No consumer source is edited.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.sf_directImage_torAmplitude`
(node `thm-sf-direct-image-tor-amplitude`), 1 of 1 original holes.
Added: 0 holes. No sorry remains in the item's module or the changed coefficient module.
The proof uses existing declarations, including
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`,
`AlgebraicGeometry.Etale.isIso_finiteConstantProjectionMap`, and
`AlgebraicGeometry.Etale.residue_tor_amplitude_test`; their pre-existing dependencies
are unchanged. This is not a new decomposition.

## No longer needed

Node `thm-sp-truncation-e2` is replaced by
`lem-etale-derived-functor-upper-amplitude`; the matching obsolete tool-use entry is
removed. The exact-couple, convergence and filtration machinery is unnecessary for this
proof. All removed proof imports are listed below:

- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.CategoryTheory.ExactCoupleConvergence`
- `Sheaf.CategoryTheory.Filtration`
- `Sheaf.CategoryTheory.TruncationCouple`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The Grothendieck, left-exactness, comparison, and projection properties remain needed;
the existing imports supply them. Removing a redundant direct import does not claim
that its module is globally unreachable. No unit statement or realized unit proof step
is bypassed. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

The spectral-sequence route is longer than applying the already proved
`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj_of_dimension` and left t-exactness.
The retained draft's report omitted its coefficient-definition performance repair;
this delivery documents that repair explicitly and checks original consumers against it.
The module uses ordinary unbounded derived direct image throughout; no extra comparison
hypothesis is needed. For `N = 0` the argument gives the original interval, and for
`n = 1` the same residue quotient and finite-presentation argument apply. The definition
repair preserves the zero ring at `n = 0` as well.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
