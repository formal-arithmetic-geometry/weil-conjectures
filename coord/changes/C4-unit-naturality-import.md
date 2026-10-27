# WeilConjectures.commonStageTensorRightUnitor_naturality

## Reason

Unit coherence needs the already proved right-unitor naturality theorem for cancellation.
Its module imports DerivedPullbackTensorIso, which imports unit coherence. Its proof
actually uses only the constraints and fully faithful integral reduction. Replace that
unnecessary parent import with the owning constraint module to permit this reuse without
an import cycle. The module is unclaimed in the current claim records.

The DAG citation is corrected from the parent comparison node to its existing constraint
node, which owns the identical definitions. No mathematical statement changes.

## Old

```lean
public import Sheaf.Paper.DerivedPullbackTensorIso
```

## New

```lean
public import Sheaf.Paper.DerivedPullbackTensorConstraints
```

All existing declarations and proofs are retained. Set `Elab.async false`, and after
`end Integral` add the following local elaboration cache:

```lean
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
  Linear.homModule Preadditive.homGroup
```

Profiling located repeated 33-second comparisons of category data in the common-stage
proof. This cache reduces the file from 111 seconds to about 22 seconds. All attributes
are local; no exported declaration, typeclass instance, construction or proof changes.
The old cache and new cache use definitionally identical structures.

## Users

The downstream declaration-use scan finds only the naturality module and the following
consumer. The direct-import scan gives the same consumer. It is checked against this
change without modifying its source; its other imports supply the parent interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageTensorRightUnitorNaturality | unclaimed | Replace unused parent import. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Same naturality theorem and constraints. |
| Sheaf.Paper.PullbackTensorCommonStageUnitCoherence | C4 | Reuse the proved naturality theorem. |

## Status

landed 20261027T233828-L-4121113 2026-10-27 (merge of deliver/C4/Sheaf.Paper.PullbackTensorCommonStageUnitCoherence)
