# picardExternalCechCupBidegree_leibniz

## Reason

Restore the two withdrawn Leibniz modules from the exact archived repair diff and keep their
complete reduction through the existing differential inclusion theorem.

The original ModuleCupNaiveDerivedCompatibility compiles against the delivered dependencies.
Its independent instance-name collision repair is excluded from this delivery.

## Old

The checkout and initial sandbox contain neither Leibniz module. The earlier H3 delivery had
picardExternalCechCupBidegree_leibniz proved by the coordinate theorem, whose proof was sorry.
The archived G3 repair has both signatures unchanged and both proof bodies complete.

## New

Restore those exact signatures and proofs. The Leibniz module privately imports
Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate and derives the pure-tensor
identity from its inclusion equation, using coordinate uniqueness to compare chosen bidegree
maps with the three specified ones. The coordinate module privately imports Leibniz and evaluates
that equality. The main docstring now describes the actual proof rather than the abandoned direct
face calculation. Both restored nodes record the actual acyclic proof dependencies.

The archived signatures are included verbatim in the restored node lean.statement fields.
The choice of bidegree maps is determined on pure tensors by the prescribed coordinates, so it
introduces no arbitrary mathematical data. No new sorry, definition or axiom is introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz | T4 | Archived signature preserved; complete proof restored and compiled. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate | unclaimed | Archived signature preserved; imports Leibniz privately; complete proof compiled. |

There are no other source importers of these withdrawn modules on the supplied checkout.
The restored main theorem uses the current unchanged differential-coordinate module; that
module does not import the restored Leibniz module, so the reduction has no import cycle.

## Status

landed 20261014T095138-L-867123 2026-10-14 (merge of deliver/T4/Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz)
