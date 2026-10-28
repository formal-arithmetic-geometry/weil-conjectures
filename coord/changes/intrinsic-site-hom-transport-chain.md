# AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport_chain

## Reason

The representative proof needs a concrete localization-level bridge from the fixed-coefficient derived Hom to the intrinsic Hom complex. This new public theorem states that strictly simpler step and is imported by the item module.

## Old

No declaration existed in the library.

## New

`AlgebraicGeometry.ProEtale.intrinsicSiteHom_transport_chain` states that the exact intrinsic realization of the fixed-coefficient derived Hom on `Lc` and K-injective `Ic` is isomorphic to the localization of `homComplex` over `proEtaleConstantRing X A` applied to the realized complexes.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives` | B9 | imports the new proof dependency and composes its isomorphism with the generic representative theorem |

## Status

landed 20261028T034705-L-3531835 2026-10-28 (merge of deliver/B9/Sheaf.Paper.IntrinsicSiteHomTransportRepresentatives)
