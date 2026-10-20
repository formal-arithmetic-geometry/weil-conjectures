## What changed

Completed the retirement assigned by coord/retire-items.tsv and the human-approved
handoff in coord/changes/retire-sheaf-twins-20261020.md. The item is already a
declaration-free re-export of the fully proved upstream module. Withdraw it through
deleted.txt and replace its three remaining active private imports with direct
imports of WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf in:

- Sheaf.AlgebraicGeometry.CommutativeExchangeChart
- Sheaf.AlgebraicGeometry.EtaleHigherDirectImageStalkCriterion
- Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity

Each consumer changes exactly one import line. Its public imports, signatures,
definitions, proofs and attributes remain identical. No upstream file is changed.
The node sbc-lem-higher-direct-image-presheaf already points to the canonical
upstream theorem, so no node edit is needed. Its mathematical dependencies and
unit route remain in place. The retired prerequisite DerivedCategories is already
absent, and the canonical upstream file imports its upstream replacement.

Change record: coord/changes/retire-abelian-higher-direct-image-presheaf-b3.md.

Validation: lcompile.py --all compiled all three adapted consumers successfully.
An exact source comparison confirms that each differs only in that one import.

## Proved and sorry left

This is a zero-hole retirement: proved 0 of 0 item sorries; added 0; split off 0.
The two canonical nonempty_higherDirectImage_iso_sheafification_abelian and
nonempty_higherDirectImage_iso_sheafification_abelian_single theorems remain proved
upstream, together with the canonical comparison construction and local bijectivity.

Existing consumer holes are untouched:

- AlgebraicGeometry.Etale.commutativeExchangeChart
  (lem-kun-commutative-exchange-chart).
- AlgebraicGeometry.Etale.higherDirectImage_relative_continuity (lem-kun-0eym).

The consumer theorem isZero_higherDirectImage_iff_geometric_cohomology_colimits
remains fully proved. No declaration is weakened, moved or restated.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf.
Removed its public upstream re-export and replaced all three active private imports
of the shim with imports of the same upstream provider. No mathematical node or
dependency is pruned: in particular sbc-lem-higher-direct-image-presheaf is still
used, with its existing upstream Lean attachment.

The four archived consumers in quarantine (StrictLocalBaseChangeGlobalHomology,
PrimeCurveArtinSchreierKernel, SmoothCurveEtaleStructureDirectImages, and
Paper.PurityRelativeKummer) are not active library sources. Their archives remain
intact; restoring them must migrate this old import to the same upstream provider.
This delivery does not withdraw those modules or their mathematical dependencies.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed module. The current queue instead assigns
this module as a retirement. The retirement inventory predates D2's landed canonical
upstream reuse and still describes twelve consumers and a missing helper
nonempty_mapIso_trans. The current item has no declarations, its node is already
repointed, and only three active consumers remain. Thus no API bridge or new proof
is required; redirecting the imports completes the remaining retirement.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
