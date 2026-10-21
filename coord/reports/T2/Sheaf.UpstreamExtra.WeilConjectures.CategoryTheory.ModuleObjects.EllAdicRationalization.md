## What changed

Restored the assigned quarantined module from the exact archive named by
`coord/rework.tsv`, preserving all eight private helper declarations and their proofs,
all existing public imports, and all coefficient and rationalization interfaces.

Added the private proof imports `import all Sheaf.Paper.IntegralConstructibleSequentialHom`
and `import Sheaf.Paper.IntegralConstructibleSheafHom`. The former makes the proved private
bounded-Hom and isomorphism-transport helpers available; the latter explicitly exposes
the sheaf-source continuity statement and its public Hom-colimit definitions.
No theorem body or signature changed. Wrapped the sync comment to 100 columns and disabled
only the private-module style warning: this archive intentionally contains private helpers.

Validation: the unmodified archive failed compilation with unknown `homColimitProperty`
and `CategoryTheory.homColimit_bounded`, followed by cascading cocone errors. The repaired
module compiled cleanly through `lcompile.py` in 14.6 seconds, without warnings.
LeanFinder, Loogle, msearch grep and local ripgrep searches confirmed that the repair is
an import-visibility issue and located the existing helpers; no replacement theorem was needed.
Change record: `coord/changes/T2-ell-adic-rationalization-archive-imports.md`.

## Proved and sorry left

This is a zero-hole rework repair, not a new proof or decomposition. Closed 0 of 0 holes;
added 0 holes; split off 0 statements. No `sorry` remains in the item.
The eight retained proved private declarations are
`CategoryTheory.essSurj_of_subcategory_models`, `CategoryTheory.scalar_power_isIso`,
`CategoryTheory.scalar_sequence_map`, `CategoryTheory.scalar_unit_cocone_zero`,
`CategoryTheory.rationalization_inverts_of_scalar`,
`CategoryTheory.rationalization_localization_of_hom`,
`CategoryTheory.rationalization_of_subcategory_models`, and
`AlgebraicGeometry.ProEtale.CondensedRing.integral_scalar_map_eq`.
The archive has no DAG Lean attachment; none is removed or changed.

## No longer needed

None. No import, declaration, DAG node, module or dependency was withdrawn.
The complete archived proof route is preserved, including its bounded-Hom continuity
argument. Existing public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

The item's absence from the live tree was quarantine, not withdrawal: its archive was
restored from the current rework record. After the module-system sync, a plain import
of `IntegralConstructibleSequentialHom` does not expose its private `homColimit_bounded`
and `homColimit_iso` helpers or privately imported Hom-continuity API. Explicit proof
imports repair that visibility without changing consumer statements or upstream files.
The downstream tool reports an unknown module because the item is quarantined; exact
import scans across both `lean/` and `quarantine/` found no consumer, consistent with the
queue's zero quarantined importers. No mathematical statement or definition was repaired.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
