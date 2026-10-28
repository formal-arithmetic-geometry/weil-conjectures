## Reason

The parent proof is decomposed into four named component equations, each used directly
in the structure constructor.  These are new public declarations required by the
parent proof.

## Old version

`Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints` exposed only the parent theorem
and imported `Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit`.

## New version

The parent module imports four component modules and assembles their conclusions.
Each component module exposes one strictly smaller constraint equation with the same
finite-model and native-coherence inputs.

## Effect on users

`AdicCompletedTensorCommonLiftCoherence` continues to use the parent theorem unchanged.
The four declarations add reusable component obligations and do not alter existing
signatures or definitions.

## Status

Pending maintainer verification of the component proofs.
