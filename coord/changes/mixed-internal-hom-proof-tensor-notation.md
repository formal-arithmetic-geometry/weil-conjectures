# AlgebraicGeometry.mixedInternalHom_baseChange_exchange

## Reason

The proof uses tensor products and tensor morphisms in the monoidal namespace.
Opening that namespace supplies the notation and named tensor-composition lemmas.
The stage-3 syntactic visibility check requires this record for the added `open`.
No declaration signature, definition body, public import or exported instance changes.
The extra opening is used only to elaborate the proof and its proved private helpers.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.MixedInternalHomBaseChangeExchange | E1 | Proof notation only; public theorem type unchanged. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | No adaptation; imported theorem signature and public imports unchanged. |

This is not a change to the statement or to any definition. There are no forced
adaptations and no target meaning is changed. Namespace openings do not alter the
elaborated type of downstream declarations.

## Status

landed 20261013T140815-L-312437 2026-10-13 (merge of deliver/E1/Sheaf.AlgebraicGeometry.MixedInternalHomBaseChangeExchange)
