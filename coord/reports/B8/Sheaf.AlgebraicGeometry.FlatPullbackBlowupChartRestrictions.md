## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.blowup_flat_fiber_residue` directly from
`blowupFlatBaseChangeIso` and Mathlib's fibre pullback square, with both projection equations.
Proved `AlgebraicGeometry.Scheme.IdealSheafData.etale_blowup_reduced_point_neighbourhood` by
removing the other points of the closed discrete fibre. The restricted fibre and the canonical
residue-field point have reduced sources and the same range, hence the same kernel ideal.
All existing declaration signatures, definitions and public imports are unchanged.

Added proof imports for the proved source results `isReduced_of_etale` and
`Scheme.Hom.ker_eq_vanishingIdeal`. Updated node steps 5--6 and their dependency union.
The node's chart plan (steps 1--4) remains available for the next worker.

Validation: the final module compiled through `lcompile.py` in 7.7 seconds, without warnings.
The edge cases used to check the argument are an infinite discrete fibre, a singleton fibre,
and a nontrivial residue-field extension. Closedness of the complement uses the closed map
property of the fibre inclusion, so no finiteness hypothesis is needed.

## Proved and sorry left

Closed 2 of the original 3 holes, with no holes added and no split-off statements:

- `AlgebraicGeometry.Scheme.IdealSheafData.blowup_flat_fiber_residue`.
- `AlgebraicGeometry.Scheme.IdealSheafData.etale_blowup_reduced_point_neighbourhood`.

One hole remains:
`AlgebraicGeometry.Scheme.IdealSheafData.blowup_flat_chart_restrictions`, attached to
`lem-sfb-flat-pullback-blowup-chart-restrictions`. Its complete existing statement and
natural-language proof remain unchanged. In particular this delivery does not claim the
chart ring isomorphism or its compatibility with the specified global comparison is proved.

## No longer needed

Removed unused proof imports:

- `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`.
- `Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`.
- `WeilConjectures.Blowup.Affine.Principalization`.
- `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
- `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`.

The first four remain mathematical inputs in the plan for the outstanding chart theorem;
their import removal does not assert that those chart steps have been bypassed.
`lem-pc-closed-subscheme-base-change-ideal-image` is no longer needed by this module's
argument: the existing Mathlib kernel/comap identity directly identifies the fibre ideal.
Removed that obsolete `proof_deps` and top-level `tool_uses` entry. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The full chart construction is unnecessary for the fibre
isomorphism: the already proved global blowup comparison suffices. For the last clause,
explicit field-spectrum component isomorphisms can be replaced by reduced-source kernel
uniqueness. The finite-type hypothesis is retained in both signatures although these two
proofs do not need it. No unit statement or route changes.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
