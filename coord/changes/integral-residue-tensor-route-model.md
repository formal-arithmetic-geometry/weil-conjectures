# Change record: integral residue tensor route model

## Reason
The explicit monoidal transport declaration is required as a strictly more general intermediate theorem because dependent instance normalization blocks direct rewriting of the irreducible exchange functor.

## Old
The item module contained only the target theorem and no explicit transport interface.

## New
The item module adds integralResidue_tensorRoute_model_transport, recorded by DAG node new-integral-residue-tensor-route-transport, and specializes it to prove the target.

## Users
The target theorem is the only current user. Future proof modules may use the transport theorem through the item module.

## Status
landed 20261017T182557-L-1569109 2026-10-17 (merge of deliver/B4/Sheaf.Paper.IntegralResidueTensorRouteModel)
