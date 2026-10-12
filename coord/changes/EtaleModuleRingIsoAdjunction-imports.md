# EtaleModuleRingIsoAdjunction imports

## Reason
The proof needs the concrete abelian instance and direct pushforward definitions; the inverse-image algebraic-structures module is unused.

## Old
`public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`

## New
`public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients` and `public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; the concrete coefficients import supplies the proof-only Abelian instance.

## Users
| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleModuleInverseImageTransport` | E1 | imports this module; statement remains unchanged |

## Status
landed 20261012T112834-L-765800 2026-10-12 (merge of deliver/E1/Sheaf.AlgebraicGeometry.EtaleModuleRingIsoAdjunction)
