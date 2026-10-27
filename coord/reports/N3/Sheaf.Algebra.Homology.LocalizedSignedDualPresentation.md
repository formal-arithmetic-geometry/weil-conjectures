## What changed

Filled the four theorem bodies in `Sheaf.Algebra.Homology.LocalizedSignedDualPresentation`.
All existing public declaration signatures are preserved. The implementation of
`dualProjection` now calls `homComplexπ` directly, which is the identical chosen
projection fixed by the old wrapper's `ProjectionData.eq_chosen` field. New helpers are private
and proved. Added the proof import `Mathlib.Data.Int.Interval` for finite integer intervals and
the public import `WeilConjectures.Algebra.Homology.HomComplexComponents` for the
projection definition and differential formula. The implementation repair is recorded
in `coord/changes/N3-signed-dual-projection.md`; there are zero current downstream modules.
Local instance priorities and transparency settings keep elaboration on the existing
coefficient structures; they add no exported instances or attributes.

For integral strictification, replace terms outside the interval by integral zero objects,
and transport the localized differentials to these terms. Write each differential as an
integral numerator divided by a power of t, take a finite common denominator, and use
localized-module equality to kill the finitely many successive-composite defects by a
common power. The resulting differentials square to zero integrally. Scaling degree q by
t^((N+E)*(b-q).toNat) gives the chain isomorphism. Its inverse identity transports the
specified localized retractions. Empty intervals, single-degree intervals, t=0, and
t-power-torsion objects require no additional hypotheses.

The derived corollary transports the chain isomorphism through the canonical equality of
zero-morphism structures, then applies the derived localization functor. Postcomposition
naturality is the naturality equation of the Hom-complex bifunctor.

For the final presentation, use the existing rational-term comparison with its normalized
identifications and linear extensions. The product universal property shows the surviving
projection is invertible; its differential formula gives the required sign. Zero terms
outside the interval give trivial localized retractions. Apply the existing comparison to
every term and transport its dual retraction along the surviving projection. The existing
Hom-to-single isomorphism supplies the derived signed-dual identification. No total
postcomposition-isomorphism claim is introduced.

Searches used the launcher's LeanFinder, Loogle and grep services and local searches of
Sheaf, WeilConjectures and Mathlib. No existing raw localized bounded-complex lift was found;
Mathlib's localized-module surjectivity and equality criteria provide the fraction steps.

## Proved and sorry left

Closed all four existing holes, verified by a clean full-module compile: `CategoryTheory.LocalizedSignedDual.bounded_localized_complex_lift`,
`CategoryTheory.LocalizedSignedDual.bounded_localized_complex_lift_derived`,
`CategoryTheory.LocalizedSignedDual.postcompose_natural`, and
`CategoryTheory.LocalizedSignedDual.localized_signed_dual_presentation`.
All belong to node `lem-sf-localized-signed-dual-presentation`.
No holes added; actual remaining hole count is zero. No split-off statements.
The imported rational-term comparison is used as its stated theorem; it is not reproved here.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the proof
uses the ordinary Hom-complex bifunctor and the already stated term comparison.
Removed the redundant direct proof import `Mathlib.Algebra.Module.LocalizedModule.Basic`;
`Mathlib.RingTheory.Localization.BaseChange` supplies the needed localized-module API.
Removed the duplicate private helper `CategoryTheory.LocalizedSignedDual.soleFactorIso`.
The proof now calls the existing private theorem
`CategoryTheory.RationalTermHom.soleFactorIsIso` through a proof-only
`import all Sheaf.Algebra.Homology.RationalTermHomComparison`; the existing public
import is preserved. No change to the comparison module is needed.

All recorded proof dependencies remain used. Added `lem-sc-hom-complex-projections`
to the dependency record for the normalized projection and differential law.
No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned delivery at `4280f1c1d4c` duplicated the existing private
`RationalTermHom.soleFactorIsIso`. This repair removes that helper and applies the
existing theorem directly using Lean module-system private proof access.
The retained packet was compared with the current shared sources before editing.

No mathematical correction is needed. The DAG's denominator and torsion-defect argument
works without regularity of t, and its restriction of integral object equality to the
specified interval is essential and preserved.

The retained draft had not passed a complete compiler check. This session repaired the
fraction-map coercions, imported integer finite intervals, supplied the scalar-tower
instance for raw localized Homs, transported the zero-morphism cast with a private
definition, and gave the termwise comparison its full proposition type. Explicit
universes and local transparency settings keep the Hom-complex specification from
unfolding during routine elaboration. The commuting square is the existing sheaf Hom
bifunctor's naturality equation. A version preserving the wrapper compiled cleanly in
54.5 seconds, but delivery exceeded 60 seconds. The direct projection API removes the
redundant dependent-family transport while preserving the exact mathematical map.
No compile limit or launcher tool was changed. No public signature changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
