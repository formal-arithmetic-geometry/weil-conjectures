# ModuleRingedToposDerivedComparison proof elaboration settings

## Reason

The retained tensor and projection-mate proofs expand large sheaf and derived
category constructions. Local irreducibility guards keep the five existing
pullback constructions behind their APIs; elaborator options and declaration
scoped heartbeat settings support the completed proofs. The static checker
conservatively classifies changed commands as an interface change and requires
this record. These options and local attributes do not propagate to importers.
No existing signature, definition body, public import or global attribute changes.
The coefficient variable command is moved below the new private general-category
helpers; the variables and all existing declaration binders are identical.
No target statement or definition used by a target changes meaning.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

No local irreducibility attributes or declaration-scoped heartbeat options were
present in the item. Existing theorem signatures and definitions remain verbatim.

## New

```lean
set_option linter.all false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

Inside the existing namespace:

```lean
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
```

The `ordinary_monoidal` and `open_homEquiv` proofs have declaration-scoped
`maxHeartbeats 800000`; the proper and open projection comparison proofs have
`maxHeartbeats 1600000`. The server's 60-second file limit is unchanged.
All ten new helpers are private and completely proved, including the
componentwise currying definition and its naturality fields.
The final coherence tactic passes an existing proof term directly to Lean's
kernel, which checks its type normally; it does not disable kernel checking.

## Users

`tools/downstream.py Sheaf.Paper.ModuleRingedToposDerivedComparison --uses
ordinary_monoidal` lists the eight downstream modules below and only the item
itself as a textual user of `ordinary_monoidal`. All existing signatures and
non-theorem bodies were compared verbatim with the source. Options and local
attributes have no importer-visible effect; no downstream adaptation is needed.
Untouched modules' ownership is immaterial to this proof-local change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | B6 | Completed proofs and local settings |
| Sheaf.Paper.CoefficientProjectionSquare | unchanged; not adapted | None |
| Sheaf.Paper.CoefficientPushFilteredLegs | unchanged; not adapted | None |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unchanged; not adapted | None |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unchanged; not adapted | None |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unchanged; not adapted | None |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unchanged; not adapted | None |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | unchanged; not adapted | None |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unchanged; not adapted | None |

## Status

landed 20261022T022019-L-428771 2026-10-22 (merge of deliver/B6/Sheaf.Paper.ModuleRingedToposDerivedComparison)
