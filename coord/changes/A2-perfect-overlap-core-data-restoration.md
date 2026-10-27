# AlgebraicGeometry.perfect_overlap_object_realization_core_data

## Reason

Repair the returned packet using the current library and preserved caller source.
The assigned CoreData import/signature repair and pointwise/family attachments
already landed in 20261022T025311-L-1269528; preserve them. The returned caller
PerfectOverlapObjectRealization is currently absent in the shared checkout and
on the project server, and remains listed in coord/rework.tsv. Its archive has
one obsolete public import that cannot expose perfectLimitMap in the public
PerfectHomObjectRealization.hom_pin signature. Restore the full caller with that
import redirected to the adopted source module.

The current original caller was checked through lcompile.py and fails in 16.2
seconds at line 64 with Unknown identifier perfectLimitMap. Lean explicitly
requests public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport.

The assigned theorem also packages the proved nonempty core by elimination
into its Prop-valued conclusion, avoiding an unnecessary Classical.choice call.
Its statement, canonical family, compatibility equation and assumptions stay
unchanged. No source-library module or target is edited.

## Old

Current preserved caller header:

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Mathlib.CategoryTheory.HomCongr
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData
```

Its full source is
quarantine/Sheaf/AlgebraicGeometry/PerfectOverlapObjectRealization.lean.

Current assigned theorem's final proof lines:

```lean
  exact ⟨⟨data, Classical.choice
    (hcore U V hcover hU hV A B hA hB E φU φV data rfl)⟩⟩
```

## New

Restore the full preserved caller at its original library path, with this header:

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
public import Mathlib.CategoryTheory.HomCongr
import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData
```

Every line after its header is identical to the preserved source. All three
public declarations, private helpers, definitions and theorem proofs are retained.

The assigned theorem's final proof lines become:

```lean
  obtain ⟨core⟩ := hcore U V hcover hU hV A B hA hB E φU φV data rfl
  exact ⟨⟨data, core⟩⟩
```

This eliminates Nonempty into Nonempty; it constructs the required dependent
pair with the same canonical data. Update the final main-node proof step to
match. All other node fields and dependencies stay as currently landed.
The already corrected pointwise/family attachments are not resubmitted.
Refresh only the existing caller node's Lean note to record the restored source
and its adopted public import. Its statement, proof, dependencies and declaration
attachment are preserved; no new node is introduced.

## Users

Source scans include the quarantined parents; absence from the current import
graph is not treated as withdrawal. No other group's held module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData | A2, assigned | same signature; direct elimination replaces Classical.choice |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization | unclaimed, quarantined | complete restoration; one obsolete public import redirected |
| Sheaf.AlgebraicGeometry.PerfectOverlapHomPresentation | unclaimed, quarantined | consumes restored caller; every public declaration and definition preserved; no adaptation needed |

No target signature or definition changes, and no target-meaning review is
reopened. The corrected compatibility condition already landed in CoreOfData
and is supplied by the unchanged canonical-family equality proof.
The final delivered set compiles through lcompile.py: CoreData in 46.9 seconds
and the corrected caller in 1.9 seconds, with zero literal holes in either file.

## Status

landed 20261022T043925-L-1096532 2026-10-22 (merge of deliver/A2/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData)
