# Staged representative equations for scalar realization

## Reason

The direct concrete specialization rechecks large coefficient and realization data
and exceeds 60 seconds. Two proved theorem stages specialize the ordinary models
and then the scalar source before the concrete functor is substituted.

## Old

Neither new theorem nor its module existed. The assigned theorem had one `sorry`.
Its statement and the existing construction definitions are preserved verbatim.

## New

`Sheaf.Paper.FiniteScalarTensorOrdinaryModelRepresentativeEquation` adds the fully
proved `finiteScalarTensorRealizationForOrdinaryModels_representative`, applying
the existing generic descent equation to the ordinary-model construction.

`Sheaf.Paper.FiniteScalarTensorScalarSourceModelRepresentativeEquation` adds the
fully proved `finiteScalarTensorRealizationForScalarSourceModels_representative`.
It fixes the source coefficient category and its specified representative class,
while leaving the target ring sheaf and both realization functors abstract.

The exact new signatures are recorded in their DAG nodes and Lean files. Neither
adds an assumption, a choice, or a hole. The item uses the second theorem after
unfolding only its scalar realization and total-comparison wrappers. All added
imports at consumers are proof-only. Local elaboration attributes change no global
instance, attribute, definition or existing signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteScalarTensorScalarSourceModelRepresentativeEquation | B2 (new) | Specializes the new ordinary-model theorem. |
| Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation | B2 | Uses the new scalar-source theorem; public statement unchanged. |

The new modules have no existing library importers. No definition used by a target
statement changes, and no source-library module is edited.

## Status

landed 20261027T180452-L-3863760 2026-10-27 (merge of deliver/B2/Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation)
