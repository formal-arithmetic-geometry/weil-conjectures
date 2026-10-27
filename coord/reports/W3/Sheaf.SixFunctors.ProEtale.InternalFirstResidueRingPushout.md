## What changed

The target proof now obtains the normalized first-residue coefficient isomorphism,
applies the sheaf-level pushout, and transports that pushout through section-ring
reconstruction and the coefficient-sized small site. The proof-only imports of
`InternalFirstResidueRingIso`, `InternalFirstResidueSheafPushout`, and
`InternalFirstResidueSmallMapPushout` were added. Three strictly smaller public
intermediate statements were split into those modules and recorded as new DAG
nodes.

## Proved and sorry left

The target declaration `AlgebraicGeometry.ProEtale.internal_first_residue_ring_pushout`
is proved by composition of the three named intermediate statements. The following
new statements remain as split-off proof obligations:

- `AlgebraicGeometry.ProEtale.internal_first_residue_ring_iso`;
- `AlgebraicGeometry.ProEtale.internal_first_residue_sheaf_pushout`;
- `AlgebraicGeometry.ProEtale.internal_first_residue_smallMap_pushout`.

No definition contains a `sorry`; the delivery leaves three theorem-proof `sorry`s,
one in each new module.

## No longer needed

No source declaration or public statement import was removed. The original detailed
proof dependencies are now consumed by the split-off coefficient and sheaf-level
statements, while the target itself imports only the three proof interfaces it uses.
The target's old direct proof route is therefore no longer needed in the target
module, but its mathematical dependencies remain needed by the new nodes.

## Where the brief, the DAG or earlier work was wrong

The existing node presented the entire coefficient identification, sheaf pushout,
and small-site transport as one theorem-sized step. No compilable library theorem
supplied that composite argument, so the proof was decomposed into the three strict
interfaces above. The target statement and all existing signatures are unchanged.

## New nodes

- `lem-sfb-internal-first-residue-ring-iso`: finite discrete first-quotient
  coefficient-ring isomorphism.
- `lem-sfb-internal-first-residue-sheaf-pushout`: pushout before section-ring and
  `AsSmall` transport.
- `lem-sfb-internal-first-residue-small-map-pushout`: generic transport of a
  commutative ring-sheaf pushout to the coefficient-sized small site.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
