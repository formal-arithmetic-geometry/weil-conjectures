# AlgebraicGeometry.etaleTowerBrownAdjunction

## Reason

The combining proof needs the recorded standard derived localizations to take
priority over the equivalent private localization choices exposed by proof imports.
The added local commands select these instances during elaboration of this file.
They change no declaration signature, definition, public import, exported instance,
notation or target meaning. The delivery checker requests this record for new
`attribute` and `universe` commands even though the attributes are local.

## Old

The namespace opened with no local instance-priority command:

```lean
namespace AlgebraicGeometry
```

The original file declares only `universe u` before that namespace. It has no
local attribute commands for `CoefficientSystemOrdinaryImage` fields.

## New

```lean
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived
```

The private generic helpers also introduce:

```lean
universe a b w dA dB v u' v'
```

The coefficient-image additive field instances, already declared as instances in
their defining module, are registered locally for proof elaboration:

```lean
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive
```

All existing public signatures and non-theorem bodies are retained verbatim.
All new helper declarations are private and proved. The new universes are used
only by those helpers. No global instance attribute is added.

## Users

`python3 tools/downstream.py Sheaf.Paper.EtaleTowerBrownAdjunction --uses
etaleTowerBrownAdjunction` reports zero downstream modules and only the item's
own declaration use. DAG parents with unfinished proofs remain attached unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleTowerBrownAdjunction | E3 | Local proof elaboration only; existing public interface unchanged. |

No consumer adaptation is necessary and no source-library module is edited.

## Status

landed 20261024T014529-L-2212573 2026-10-24 (merge of deliver/E3/Sheaf.Paper.EtaleTowerBrownAdjunction)
