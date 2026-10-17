# Restore exact-functor-couple declaration

## Reason

The upstream sync commented out the DAG declaration and left a hollow private definition.

## Old

The module exposed no `exactFunctor_couple` declaration and contained private helper declarations, including `mapped` with a sorry body.

## New

The module exposes the exact DAG theorem statement with its proof currently postponed as one named theorem sorry, and removes the hollow private helper context.

## Users

`Sheaf.AlgebraicGeometry.HypercohomologyFiltrations` imports this module and can resolve the restored declaration. Its public interfaces are otherwise unchanged.

## Status

landed 20261017T163410-L-3003725 2026-10-17 (merge of deliver/D2/Sheaf.CategoryTheory.ExactFunctorCouple)
