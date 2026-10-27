# Proper compact-support compositor split

## Reason

The assigned compositor theorem requires an equality-case normalization before
the raw forget-supports compositor can be applied. This delivery records that
normalization as a separate public theorem with its own DAG node. The theorem is
strictly simpler than the assigned theorem and is left as a named proof
obligation, as required for a stage-3 decomposition. No existing declaration or
target statement changes.

## Users

| Module | Effect |
| --- | --- |
| Sheaf.AlgebraicGeometry.ProperShriekCompSupports | Contains the parent theorem and the split-off normalization. |

## Status

Open.
