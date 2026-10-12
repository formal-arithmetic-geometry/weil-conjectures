# AlgebraicGeometry.torAmplitude_of_open_neighbourhoods

## Reason

The preflight detects changed top-level commands in the proof file. The additional
namespace openings, elaboration options and local instance registrations support
elaboration of the five private helpers and the proof. They are scoped to this file
or namespace and do not change any exported signature, definition, global attribute
or public import. No downstream adaptation is necessary.

## Old

```lean
open CategoryTheory
```

The original file has no elaboration options or local instance registrations.
The theorem signature is unchanged verbatim; see the item's node lean.statement.

## New

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The options and attribute command occur inside namespace AlgebraicGeometry.
The new monoidal instance and all five helpers are private; the instance is also
local. All proof dependencies are imported with ordinary proof-only imports.
There is no change to the mathematical meaning of any target or to a definition
used in a target statement.

## Users

The downstream.py query with --uses
AlgebraicGeometry.torAmplitude_of_open_neighbourhoods lists these two textual users.
All other import descendants also retain exactly the same theorem interface.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal | P3 | Own proof completed; signature identical. |
| Sheaf.AlgebraicGeometry.QuasiCompactFiniteTorDimension | unclaimed | Its existing application remains unchanged; no elaboration commands or local registrations propagate to this importer. |

## Status

landed 20261012T223412-L-1639169 2026-10-12 (merge of deliver/P3/Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal)
