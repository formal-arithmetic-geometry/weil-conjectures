# Frobenius integral root transport proof decomposition

## Reason

The target proof uses two new proof dependencies: an additive root-line transport
statement and a generic module-adjunction glue statement. The target's local
transparency attributes were adjusted so its statement-side coefficient definitions
elaborate consistently with those dependencies.

## Old

The target theorem had a single `sorry` and used the original local irreducibility
and instance-reducibility commands.

## New

The target theorem has a complete proof. The additive and module-glue statements are
new public declarations in separate Sheaf modules and are recorded by new DAG nodes;
their proofs remain explicit split-off `sorry`s. The target theorem signature and all
public imports required by its statement are unchanged. The local attributes now use
implicit reducibility for the coefficient and root constructions and retain
irreducibility for the module adjunction definitions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed in shared snapshot | Compiled unchanged against the delivered target and split modules. |

No existing consumer is adapted in this delivery.

## Status

landed 20261028T020531-L-2521730 2026-10-28 (merge of deliver/K2/Sheaf.Paper.FrobeniusIntegralRootTransport)
