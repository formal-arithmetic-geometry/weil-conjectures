# AlgebraicGeometry.ProEtale.proper_indConstructible_boundedBelow

## Reason

Restore the quarantined module assigned by coord/rework.tsv. The archived proofs contain
zero holes, but compilation against the current library fails in hypercohomology_zero:
`failed to synthesize instance of type class ObjectProperty.IsClosedUnderIsomorphisms IsZero`.
The finite-filtration helper requires this instance. Construct it locally from IsZero.of_iso.
This is a proof repair; every archived declaration signature, visibility, definition and
public import is preserved. No target statement or definition changes.

## Old

The beginning of the affected proof block in the archived module is:

```lean
  have hHprop : IsZero (H n) := by
    apply filtration_property (IsZero (C := B)) (fun _ h ↦ h)
```

## New

```lean
  have hHprop : IsZero (H n) := by
    have : ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := B)) :=
      ⟨fun e h ↦ h.of_iso e.symm⟩
    apply filtration_property (IsZero (C := B)) (fun _ h ↦ h)
```

Remove the unused private import Mathlib.CategoryTheory.ObjectProperty.Extensions.
Its extension-closure instance does not supply closure under isomorphisms.

## Users

The downstream tool reports the item as unknown because its source is quarantined.
A source search over lean/ and quarantine/ finds the following direct consumers.
The same search checks both public theorem names and the private helper names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperIndConstructibleUnbounded | no local claim; quarantined | Both public theorem signatures and public imports preserved; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | no local claim; quarantined | Its import-all access to derived_from_heart is preserved with the identical signature; no adaptation. |

## Status

landed 20261021T233744-L-857165 2026-10-21 (merge of deliver/M2/Sheaf.Paper.ProperIndConstructibleBoundedBelow)
