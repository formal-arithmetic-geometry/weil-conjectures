## What changed

Filled `AlgebraicGeometry.Scheme.IdealSheafData.BlowupPreservedOpenDiagram.flat_baseChange_preserved_open_diagram`
in `Sheaf.AlgebraicGeometry.BlowupPreservedOpenDiagram`, preserving its statement and the nine
existing abbreviations. Added a private proof import of Mathlib's pullback associator and proved
private helpers for forgetting an invertible factor, the ambient comparison, and exchanging an
open pullback with base change. All helpers construct actual isomorphisms from Mathlib's
pullback isomorphisms and verify their projections.

The proof uses the upstream flat blowup comparison and complement theorem. Mathlib
`IdealSheafData.support_comap` identifies the preserved open directly. The ambient isomorphism
is induced by the specified blowup comparison; its P and W projections prove compatibility
with the displayed closed immersions. The restricted comparison identifies both opens with
the common open, and every requested projection equation is checked explicitly. Updated the
item node's proof and dependencies to match this argument.

Validation: the complete module compiled cleanly through `lcompile.py` in 6.0 seconds.
The theorem signature and all nine original abbreviations were compared verbatim with the
shared source and are unchanged. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.IdealSheafData.BlowupPreservedOpenDiagram.flat_baseChange_preserved_open_diagram`
(node `lem-trf-blowup-base-change-preserved-open-diagram`).

No new holes, split-off statements, or new nodes. No `sorry` remains in the delivered module.
The private helpers are all proved.

## No longer needed

The proof no longer needs these declared proof dependencies:

- `lem-pc-ideal-sheaf-comap-affine-extension` (module
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`): replaced the affine computation
  with Mathlib's already-proved `IdealSheafData.support_comap`.
- `lem-weil-pbc-closed-immersion-image-zero-locus`: the same support identity avoids the
  zero-locus calculation.
- `def-weil-affine-spectrum`: no affine prime-contraction calculation is required.

Removed the obsolete tool-use entry `lem-pc-ideal-sheaf-comap-affine-extension` from this node.
No existing import was removed: the existing public imports are retained as the module's public
interface, and the private `WeilConjectures.Blowup.Complement` import is used. The affine module
also remains an upstream dependency of the blowup construction; this delivery does not claim
it is globally pruned or withdraw any upstream declaration. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error. The affine support calculation in the original plan is unnecessary because
Mathlib already provides exactly the required equality of supports. The node describes a factor
exchange for the flat blowup comparison; the existing Lean comparison already has the required
blowup-first target order, so the proof uses it directly without an additional exchange.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
