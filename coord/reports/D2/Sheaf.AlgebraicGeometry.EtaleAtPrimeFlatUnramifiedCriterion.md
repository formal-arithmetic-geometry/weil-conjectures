## What changed

Proved `Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler`
in `Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion`, preserving its
signature, universes, hypotheses and visibility. The first equivalence is Mathlib's
basic-open characterization. The second spreads flatness and unramifiedness to one
basic open, glues flatness from its maximal local rings, and applies Mathlib's
flat, formally unramified, finitely presented criterion.

Removed the proof import of
`WeilConjectures.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing`.
Added proof imports `Mathlib.RingTheory.Smooth.Fiber`,
`Mathlib.RingTheory.Smooth.Flat`, and
`Mathlib.RingTheory.Localization.LocalizationLocalization` for the final étale
criterion, flatness of étale algebras, and the local-ring identifications.
Retained `Sheaf.RingTheory.OpenFlatLocus`, whose stated theorem is used.
Updated the node's proof, proof dependencies and proof origin to this route,
and removed obsolete entries from its top-level tool-use list.

Validation: the complete proof compiled on the server in 6.0 seconds, with no
warnings or errors. A separate `#print axioms` compile (31.2 seconds total)
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. No new declarations, definitions, statements or modules were
introduced; no consumer adaptation or change record is needed. The zero-ring
case has no prime ideal; the proof also permits g to be a unit and arbitrary
commutative base rings. All localization maps used have the canonical scalar
compatibilities explicitly supplied.

## Proved and sorry left

Closed the one original hole in
`Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler`
(node `lem-sc-etale-at-prime-flat-unramified-criterion`).
Proved 1 of 1 original sorries; 0 added; 0 split off; 0 left in the delivery.
The proof uses the existing `Module.isOpen_setOf_flat_localizedModule` theorem;
its own proof dependencies are unchanged.

## No longer needed

Removed import/module:
`WeilConjectures.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing`.
Its node `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing` is unnecessary
for this criterion because `Algebra.exists_etale_of_isEtaleAt` directly supplies
the required algebraic basic neighbourhood, in arbitrary separate universes.

Removed proof dependencies (and their obsolete top-level tool-use approvals):
`lem-weil-pbc-etale-ring-map-iff-etale-affine` and
`lem-weil-pbc-unramified-ring-map-iff-unramified-affine`.
The proof works with algebraic loci and Mathlib's ring criterion throughout,
so neither comparison with affine scheme morphisms is required.

The cotangent-support criterion is retained for the forward differential
vanishing; flatness of étale algebras, localization flatness, openness of
flatness and gluing from maximal local rings are all retained and used.
`def-weil-etale-morphism` remains a statement dependency and records the final
flat/unramified/finite-presentation criterion in its affine ring form.
No other existing proof-dependency modules were imported and then discarded.
These removals concern this item's route; no claim is made that these modules
are unused by other parents in the target closure.

## Where the brief, the DAG or earlier work was wrong

The original plan unnecessarily went through cotangent H₁ vanishing and affine
scheme comparisons to obtain the basic-open equivalence. Mathlib already
proves it directly. The reverse flatness criterion still needs the existing
open-flat-locus result: Mathlib's `IsEtaleAt.of_isUnramifiedAt_of_flat` requires
global flatness of S over R and cannot be applied directly to the original
pointwise-flatness hypothesis. Intersecting the flat and unramified loci and
using the global étale criterion resolves that mismatch without any new lemma.
The unit route and all mathematical statements are unchanged.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
