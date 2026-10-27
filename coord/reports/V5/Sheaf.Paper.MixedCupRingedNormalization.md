## What changed

Filled all four proof holes in `Sheaf.Paper.MixedCupRingedNormalization` without
changing any declaration signature, definition body, public import, or normalization.
`ringedSource` and `ringedTarget` inspect the three ringed-passage constructors.
`scalarTransport_exists` applies the existing
`CompactSupportCondensedRealization.scalarModelTransport_nonempty`, with local
spectral-norm structures on the two small coefficient fields. This adds one private
proof import, `Sheaf.Paper.CompactSupportCondensedRealization`.
`integralPush_eq` identifies the completed ring-map adjunct using the inverse
adjunction law, then identifies the ordinary module functors and their right derived
functors. Updated the owning node's proof and proof dependencies to match.

The shorter-route search used LeanFinder for normalized derived scalar extension,
Loogle for `Equiv.apply_symm_apply`, the Mathlib grep search, and project `rg`.
The exact normalized scalar-transport existence theorem was already in the project.

## Proved and sorry left

Closed four of four original holes, all in namespace
`WeilConjectures.MixedCupCoefficientChange`:

- `ringedSource`.
- `ringedTarget`.
- `scalarTransport_exists`.
- `integralPush_eq`.

No `sorry` remains in the item module. No holes or split-off statements were added.
The reused `CompactSupportCondensedRealization.scalarModelTransport_nonempty` is
an existing postponed theorem, owned by
`lem-pur-compact-support-condensed-realization`; this delivery does not prove it.

## No longer needed

None. All original public prerequisites remain relevant to the published definitions
and coordinate maps. No node or module is withdrawn. The scalar construction is
reused from an existing declaration instead of duplicated into new obligations.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite owning four postponed theorems.
Its proof now records constructor inspection, the existing normalized transport
existence theorem, and the adjunct inverse-law calculation. No mathematical statement
or unit route was changed.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
