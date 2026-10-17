# G4 EtaleSectionZeroOpen

## Reason

The theorem body is completed using an existing agreement-open theorem and the Mathlib étale stalk
APIs. The proof-only environment therefore changes, and the static stage-3 check requires a change
record.

## Old

The target theorem contained `sorry` and imported four proof-only Mathlib modules for the planned
Stacks descent and filtered-colimit route.

## New

The target theorem is fully proved. It imports the agreement-open criterion for proof use and keeps
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` as its public import. The four unused proof-only imports
are removed. The theorem signature, visibility, and statement are unchanged.

## Users

Importers see the same public target declaration and public étale-point API. The new agreement-open
import is proof-only and is not re-exported. No other module is adapted.

## Status

landed 20261017T050318-L-3205119 2026-10-17 (merge of deliver/G4/Sheaf.EtaleCohomology.EtaleSectionZeroOpen)
