# AlgebraicGeometry.perfect_overlap_object_realization_core_of_data

## Reason

Restore the assigned module from its coord/rework.tsv quarantine archive. The unchanged
archive fails at import line 6: the environment already contains
`AlgebraicGeometry.perfectOverlapObjectRealizationCoreStatement._proof_41` from
`Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase` when the adopted
`WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase` is imported.
The restored comparison and transport dependencies already use the adopted source base.
Redirect this item's base import to that same source. Also replace the retired empty
Sheaf PerfectHomTransport import with the adopted PerfectHomTransportExtension API.

## Old

The live module is absent; its complete source remains at
quarantine/Sheaf/AlgebraicGeometry/PerfectOverlapObjectRealizationCoreOfData.lean.
The two obsolete public imports are:

```lean
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
```

## New

Restore the complete archive at
lean/Sheaf/AlgebraicGeometry/PerfectOverlapObjectRealizationCoreOfData.lean,
changing only those two import lines to:

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
```

All other bytes match the archive: declaration signatures, visibility, docstrings,
definition bodies, proofs, settings and private proof imports. In particular the
canonical-family equality hypothesis and explicit seven-field core construction remain.
The equality-pinned cache still chooses only the uniquely specified value, never an
arbitrary witness of an unfinished existence statement. There are zero holes before
and after this repair. The restored module compiles cleanly in 21.0 seconds through
lcompile.py. The changed base import is acyclic according to import_direction.py.

## Users

The downstream.py query reports an unknown module because the item is quarantined.
A source scan of lean/Sheaf, lean/WeilConjectures and quarantine finds one consumer:
the separately quarantined CoreData module. There are no live importers to adapt.
The node's Lean attachment, all three proof dependencies and the unit route remain.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | A4 | restored; two import redirects |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData | quarantined | unchanged theorem and definition APIs; no adaptation in this packet |

The archived parent's statement independently fails to elaborate against the adopted
CoreBase: `perfectOverlapObjectRealizationCoreStatement R c hc i Z t j hij` is
already a Prop, so its additional `hstage` argument is obsolete. This predates the
restoration and is not caused by changing any API in this item. The separately
quarantined parent is not restored or changed by this packet. A scratch consumer
check removes that obsolete application: the original packaging proof then compiles
cleanly with the restored construction in 18.3 seconds. Both theorem axiom probes
report only the three standard axioms. This scratch check is not part of the delivery.

An explicit axiom probe of this item's theorem reports exactly propext,
Classical.choice and Quot.sound.

No definition or statement changes, and no target-meaning review is reopened.

## Status

landed 20261022T022017-L-428507 2026-10-22 (merge of deliver/A4/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData)
