# AlgebraicGeometry.ProEtale.SemilinearProperOpen.Derived

## Reason

Use the module's existing standard derived-category instance directly. The old DS alias spells the same localization through SemilinearSections.hasDerived; conversion between the two instance expressions eagerly expands localization data. Restoring DS with the new proofs and named functors still exceeded the 60-second compile limit. Both constructions are definitionally equal.

## Old

```lean
abbrev Derived (X : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X) (transition C τ X)
```

## New

```lean
abbrev Derived (X : Scheme.{u}) :=
  DerivedCategory (Modules C τ X)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | S4 | Compiles the same constructions and theorem signatures with the new proofs. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed (quarantined) | Archived textual consumer; definitionally equal presentation; no adaptation. |

The live-only downstream search omits the quarantined consumers listed above.
They are retained conservatively from the landing check's name matches, which
include unrelated unqualified names. Inspection of the archived sources found no
required adaptation: the changed definitions have definitionally equal bodies
and the existing theorem signatures and public imports are unchanged. In
particular, `FiniteFreeCompactComposition` directly imports the item and uses its
system functors; those constructions keep the same sources, targets and bodies.
The DAG parents and definition attachments are retained. No archived source is
withdrawn or restored by this delivery; this presentation repair does not change
a target's meaning.

## Status

landed 20261020T230833-L-618817 2026-10-20 (merge of deliver/S4/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
