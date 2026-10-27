## What changed

Proved `AlgebraicGeometry.etale_stalk_invariants` in
`Sheaf.AlgebraicGeometry.EtaleStalkInvariants`, preserving its statement and all public
imports. Added proved private helpers for transport of the three ring invariants,
normal-domain characterization of a local ring by its prime localizations, and the
localized étale comparison. The main proof obtains faithful flatness from the flat local
stalk map and uses `HasRingHomProperty.stalkMap_of_respectsIso` to transfer the localized
comparison to the actual stalk map.

The shorter route uses the already proved upstream
`IsRegularLocalRing.localization_of_etale_of_comap` and
`Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap` for ascent.
Regularity descent uses regular-local localization and faithfully flat regular-ring
descent; normality descent uses faithfully flat normal-ring descent. Added one private
proof import, `WeilConjectures.RingTheory.Etale.IntegrallyClosedLocalization`.
Updated the item's proof, proof dependencies and proof origin, and removed obsolete
entries from its existing tool-use approvals. No shared interface or other existing
module was changed, and no change record is needed.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.etale_stalk_invariants`
(`lem-sfb-etale-stalk-invariants`). Added 0 holes; 0 remain in the item or any added Lean
module. The private helpers are completely proved. The two new DAG records attach to
existing proved source declarations and introduce no Lean statements or holes.
This is a proof from existing declarations, including the previously stated ring
comparison and descent dependencies, rather than a claim that all their transitive
axioms have now been discharged. Final single-file compilation passed without warnings in 3.3 seconds. The delivery
tool also runs the required preflight checks.

## No longer needed

Removed these eight direct proof imports:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`
- `Mathlib.CategoryTheory.Limits.MorphismProperty`
- `Mathlib.RingTheory.Smooth.Basic`
- `WeilConjectures.RingTheory.RegularRingSmoothAscent`
- `WeilConjectures.RingTheory.LocalizationOfRegularRing`
- `WeilConjectures.RingTheory.EtaleNormalRing`

The proof no longer directly needs these planned nodes:

- `lem-sbc-finite-affine-tensor-base-change`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-ring-map-iff-etale-affine`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `lem-weil-pbc-localization-of-regular-ring`
- `lem-weil-pbc-etale-over-normal-ring-normal`

The generic stalk-transfer theorem handles affine restriction and stalk identification;
the existing localized ascent lemmas already perform the required ring arguments.
Removed the corresponding obsolete approved tool uses: finite affine tensor base change,
regular-ring smooth ascent, localization of a regular ring, and étale normal-ring ascent.
These are removals from this proof's direct dependency route, not assertions that every
one is globally unreachable or absent transitively. No module is withdrawn and no source
library declaration is removed. The unit's own statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The statement is correct, including non-Noetherian ambient schemes and infinite Krull
dimension. The DAG's longer tensor-base-change/smooth-ascent construction was unnecessary:
the adopted source already proves pointwise localized regularity and normal-domain ascent.
These two proved declarations had no exact DAG attachment, so their attachments are added.
The original module docstring describes a valid longer mathematical argument; the updated
DAG and Lean record the shorter actual proof. No statement repair was made.

## New nodes

`lem-sfb-etale-localization-regular-ascent` attaches the existing proved declaration
`IsRegularLocalRing.localization_of_etale_of_comap` from
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`. It is precisely the ascent
part of Stacks Tag 0AH0 for prime localizations, with no global Noetherian assumption.

`lem-sfb-etale-localization-normal-ascent` attaches the existing proved declaration
`Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap` from
`WeilConjectures.RingTheory.Etale.IntegrallyClosedLocalization`. It supplies localized
normal-domain ascent from Stacks Tag 033C, without imposing normality on the unlocalized
base ring. Both declarations' complete source proofs were read; LeanSearch, Loogle,
LeanFinder and source searches found no exact Mathlib replacement. No new Lean module
is added. At an actual prime, localizations are nonzero local rings; empty schemes
have no points to consider, so no extra nonemptiness hypothesis is introduced.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
