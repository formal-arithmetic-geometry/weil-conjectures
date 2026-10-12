# AlgebraicGeometry.etaleSetSectionLift_affine

## Reason

The delivery checker treats the local irreducibility attribute as an interface command.
The attribute prevents unfolding of the large canonical comparison while constructing
the stage sheaf diagram. It is local to this module; its public signature is unchanged.

## Old

No local irreducibility attribute for `etaleSetSectionComparison`.

## New

`attribute [local irreducible] etaleSetSectionComparison`

The transparency and heartbeat options are scoped to the target theorem. The attribute
has no effect outside this module and changes no definitions or target statements.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSetSectionLiftAffine --uses etaleSetSectionLift_affine` lists the following actual users.
All other downstream modules import them transitively; no statement or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleAffineSectionColimit | unclaimed | Identical theorem type; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleSetSectionLift | none inspected | Identical theorem type; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleSetSectionLiftAffine | M3 | Local proof elaboration only. |

## Status

landed 20261012T144128-L-2101954 2026-10-12 (merge of deliver/M3/Sheaf.AlgebraicGeometry.EtaleSetSectionLiftAffine)
