# RingTensorCohomology.derivedTensor_localization_cohomology

## Reason

Restore the quarantined localization module after the 2026-10-20 upstream sync.
Its Sheaf model import collides with the upstream model imported by all three
proof dependencies. Both modules declare `ModuleCat.BaseDerivedTensorCohomologyModel`.
Use the adopted upstream model consistently. This is an import repair, not a
change to the mathematical statement, definitions, or proof route.

## Old

```lean
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

## New

```lean
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
```

The import above is the entire source change relative to the quarantined file.
Every declaration, binder, universe, attribute, and proof body is preserved.
The model structures in the two providers have byte-identical fields; the differing
name of their additive-instance theorem is not used by this module.

## Users

`tools/downstream.py` is checked against the current library with
`--allow-missing --uses derivedTensor_localization_cohomology`.
Quarantined consumers were additionally inspected, since they are absent from
that script's library scan. The scan returned zero current library consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology | D5 | Restored with the upstream public model import; complete proof retained. |
| Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare | D5 rework cluster, quarantined | Its call at line 260 uses the same theorem signature; no source adaptation. |
| Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationIsos | D5 rework cluster, quarantined | Indirect consumer through the square; no source adaptation. |
| Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison | D5 rework cluster, quarantined | Indirect consumer through localization isomorphisms; no source adaptation. |

The separate quarantined root `PrescribedTensorCohomologyModelRealization`
is not restored or changed by this packet. Dependents remain eligible for the
project's rework/autorestore process once their other dependencies are restored.
No target statement or definition is changed. No forced adaptation is included.

## Return repair

The landing of returned head `c619dbfe719` was refused because the item source
changed after its base `d92f73d8e`. The current shared source is again the
quarantined file recorded in `coord/rework.tsv`; its model import still names
the Sheaf duplicate. Re-read that current file and reapplied exactly the Old to
New replacement above, preserving all remaining bytes. The reconstructed file
is identical to the retained sandbox repair. Delivery checks use the refreshed
shared branch as their base.

## Status

landed 20261020T145500-L-2400395 2026-10-20 (merge of deliver/D5/Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology)
