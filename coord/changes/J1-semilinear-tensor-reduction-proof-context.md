# WeilConjectures.SemilinearSections.systemTensorReduction proof context

## Reason

Document the private proof context conservatively identified as command changes by preflight.
All existing public signatures and public imports are unchanged. New definitions and lemmas
are private and fully proved. Local irreducibility and instance attributes affect this file's
proof elaboration only. No data definition, canonical morphism, exported instance, target
statement or target meaning changes. No consumer adaptation is necessary.

## Old

The original file has only its public import of `Sheaf.Paper.SemilinearTensorComparisons`,
`autoImplicit false`, universes `c v r`, the category opens, the section variables and
`systemTensorReduction` with its original signature and `by sorry` proof.

## New

The public import and theorem signature remain identical. Four private proof imports are added:
`SystemOrdinaryTensorReduction`, `SystemCochainTensorReduction`,
`SystemTensorReductionFormula` (each using `import all` for existing proved private helpers),
and `SystemEvaluationFlat`.

The proof context adds `synthInstance.maxSize 4096`,
`backward.defeqAttrib.useBackward true`, disables the generic sheafification instance locally
in favor of the already specified independent-universe one, and opens `MonoidalCategory`.
Inside `TensorReductionProof`, local irreducibility is set for `hasDerived`,
`SheafOfModules.monoidalCategory`, `evaluation`, `Functor.mapDerivedCategory` and
`Functor.mapDerivedCategoryFactors`; the two composition preservation instances are local.
The cochain-summand proof uses the same 400000-heartbeat allowance as the source proof.
No transparency-respect option is disabled, and no profiling option remains.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearTensorCoherence | unclaimed | Sole direct importer; exact public signature and import retained, no adaptation. |

## Status

landed 20261026T104441-L-824508 2026-10-26 (merge of deliver/J1/Sheaf.Paper.SemilinearTensorReduction)
