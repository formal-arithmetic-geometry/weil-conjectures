# WeilConjectures.PurityCommonStageLifting.finite_object_lifting

## Reason

Restore the module quarantined by the 2026-10-26 build and repair its invalid
projection errors without changing any public statement or definition. The
rational `Stage` type must be visible to the representative calculations, while
the large theorem must avoid unfolding its category instances. Profiling an
unrestricted unfolding variant identified the stage-change application as the
remaining expensive step. Three private proved helpers isolate these calculations;
the resulting complete compile took 9.3 seconds.

## Old

The archived local transparency declaration begins:

```lean
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.Stage
  operationStageTransitionIso
```

The object formula, representative formula and explicit application of
`existsIsoOfThree` are proved inline in `finite_object_lifting`, after `Stage`
has been sealed. The object proof applies:

```lean
        exact (commonStageDerivedPullback_existsUnique.{u, v}
          P.coefficients.l Ω (j i)).exists.choose_spec.1 A
```

## New

The three existing calculations are proved as private theorems
`componentObject_spec`, `componentMap_spec`, and `stageChange_spec` before the
local irreducibility of `Stage`. They prove respectively the original first
conjunct, second conjunct and specified stage-change isomorphism conclusion.
The main theorem calls them directly. The object calculation explicitly
simplifies `commonStagePullbackObject`; the representative calculation reduces
only `commonRestriction`, `Functor.pi'`, `commonComponent`, `rationalComponent`
and `commonStageDerivedPullback`.

Local attributes also seal `ObjectProperty.FullSubcategory.category`,
`ScalarLocalization.category`, `sfIntegralConstructible`, scalar-localization
linear/preadditive instances and their module/group components, and make
`catToReflQuiver` implicit-reducible. The two initial
`respectTransparency false` settings are removed. `Elab.async false` keeps
elaboration synchronous. All public signatures, definition bodies, attributes,
imports and docstrings remain verbatim. No shared definition is modified.

## Users

A source search of `lean/` and `quarantine/` finds no current direct Lean importer
and no external use of the declarations. The unfinished DAG parent is retained.
There is no changed interface requiring consumer adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageFiniteObjectLifting | B3 | Restored with local proof elaboration repaired. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | unclaimed | DAG proof parent; dependency preserved. |

## Status

landed 20261026T100216-L-4148232 2026-10-26 (merge of deliver/B3/Sheaf.Paper.CommonStageFiniteObjectLifting)
