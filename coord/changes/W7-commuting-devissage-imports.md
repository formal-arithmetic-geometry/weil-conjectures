# Representation.commuting_representation_devissage

## Reason

Prove the existing theorem and remove the unused finite coefficient-ring public import.
The theorem concerns finite-dimensional representations over E; its statement and proof do
not use finite coefficient-ring quotients. The existing LAdic import provides all coefficient
field definitions. No declaration signature or definition changes.

## Old

```lean
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.LadicLattice
```

## New

```lean
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.Topology.LadicLattice
```

The theorem has its identical statement and a complete proof. Its proof privately imports
ContinuousCoefficientSubquotients, BigOperators.Pi, Padics.RingHoms and the retained
Topology.Algebra.Module.FiniteDimension. The redundant private SpectralNorm and
Basis.VectorSpace imports are removed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RepresentationTheory.CommutingRepresentationDevissage | W7 | Proof completed; unused public import removed. |

`python3 tools/downstream.py Sheaf.RepresentationTheory.CommutingRepresentationDevissage
--direct --uses commuting_representation_devissage` reports zero direct importers and no
external use of the declaration. The node remains needed by unfinished DAG parents; this
is not a withdrawal. No consumer adaptation is needed, and no target meaning changes.

## Status

landed 20261025T052007-L-45508 2026-10-25 (merge of deliver/W7/Sheaf.RepresentationTheory.CommutingRepresentationDevissage)
