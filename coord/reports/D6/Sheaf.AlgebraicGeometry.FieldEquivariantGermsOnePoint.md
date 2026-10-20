## What changed

Retire Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint in favor of the existing
WeilConjectures.AlgebraicGeometry.FieldEquivariantGermsOnePoint, as requested by its
current retire-items.tsv row. Redirect the three existing DAG attachments to the
upstream declarations, with their verbatim upstream signatures. Preserve their
mathematical obligations and all dependency edges.

Migrate both direct importers. EtaleGlobalSectionsGaloisImage only swaps a proof import.
FieldEquivariantGermFamilySection applies the upstream one-point theorem to the sheaf
composed with ULift. The stalk comparison equivalence transports rho and f; its germ
formula lowers each obtained local section before the unchanged gluing proof.
Both consumer signatures remain identical. Update the germ-family DAG proof and its
Lean docstring, and the selected-lift DAG proof to describe the retained source proof.

Both adapted consumers compiled clean on the remote server (4.9 and 6.3 seconds).
The original zero-hole item also compiled (9.8 seconds). The delivery preflight verifies
the complete final packet, including the import/deletion and axiom checks.

Change record: coord/changes/D6-retire-field-equivariant-germs-one-point.md.

## Proved and sorry left

This is a retirement repair, not a new proof or decomposition. Original item: zero
holes. Holes closed: zero. Holes added: zero. No sorry remains in any delivered file.
The three existing proved results are retained upstream:

- AlgebraicGeometry.Scheme.onePoint_selected_lift_section
- AlgebraicGeometry.Scheme.onePoint_propagate_from_selected_lift
- AlgebraicGeometry.Scheme.field_equivariant_germ_family_section_onePoint

The delivered consumer proofs of etaleGlobalSections_galoisInvariants_image and
field_equivariant_germ_family_section remain complete. The new ULift transport is
proved directly from Mathlib and the existing upstream one-point theorem.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/FieldEquivariantGermsOnePoint.lean, listed in
deleted.txt. Remove its proof import from both direct consumers and use the upstream
module instead. This removes its duplicated private helpers and three public theorems
from the local tree. All three DAG nodes remain needed and point upstream; none is
withdrawn and no dependency of their argument is pruned. The unit route is retained.
The added proof import Mathlib.CategoryTheory.Limits.Preserves.Ulift is used by the
stalk comparison in FieldEquivariantGermFamilySection.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with sorry; the current queue and explicit
retirement row instead request retirement of an already proved duplicate. Its actual
hole count is zero. A direct import swap suffices for the global-sections consumer,
but fails to account for the smaller coefficient universe of the general germ-family
consumer. The explicit ULift proof transport preserves that consumer's existing
statement while respecting the source-library boundary. No new statements, arbitrary
witness choices, source-library changes, or unit-route shortcuts are introduced.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
