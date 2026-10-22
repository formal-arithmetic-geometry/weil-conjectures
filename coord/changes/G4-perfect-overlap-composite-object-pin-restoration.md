# AlgebraicGeometry.perfect_overlap_composite_object_pin

## Reason

Restore the assigned quarantined module, preserving its Lean attachment and both
proof dependencies. The archived source fails at line 35 because `derivedPullback`
is now declared with `irreducible_def` in the adopted source library. Lean rejects
reassigning its already irreducible status with a local reducibility attribute.
Remove that redundant attribute entry. No definition, statement or proof changes.

## Old

The live module is absent; its source is preserved at
quarantine/Sheaf/AlgebraicGeometry/PerfectOverlapCompositeObjectPin.lean.
The failing archived command is:

```lean
attribute [local irreducible] derivedPullback perfectHomComposition
```

## New

Restore the complete archived module at
lean/Sheaf/AlgebraicGeometry/PerfectOverlapCompositeObjectPin.lean, replacing only
that command by:

```lean
attribute [local irreducible] perfectHomComposition
```

The theorem signature, universes, visibility, public import, private proof imports,
private pasting lemma and theorem proof remain byte-for-byte identical to the archive.
There are zero holes before and after the repair. The repaired module compiles cleanly
in 9.0 seconds through lcompile.py.

## Users

The downstream.py query reports an unknown module because it is quarantined.
A source scan of lean/Sheaf, lean/WeilConjectures and quarantine finds one archived
consumer, listed below. Its application supplies exactly the unchanged theorem
parameters. There are no live Lean importers to adapt. The DAG attachment and the
unit route are preserved, with both component dependencies still used.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin | G4 | restored; redundant local attribute entry removed |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | quarantined | theorem signature and public imports unchanged; no adaptation |

This is a local elaboration repair; no consumer statement or target meaning changes.
No definition is changed, and no target-meaning review is reopened.

## Status

landed 20261022T013412-L-3564380 2026-10-22 (merge of deliver/G4/Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin)

Consumer verification: compiling the unchanged archived
PerfectOverlapObjectRealizationCoreOfData stops at import line 6 with a duplicate
perfectOverlapObjectRealizationCoreStatement proof declaration from the old Sheaf
and adopted WeilConjectures CoreBase modules. It does not reach the unchanged call.
That separately quarantined consumer needs its own restoration; it is not adapted
by this local-attribute repair.
