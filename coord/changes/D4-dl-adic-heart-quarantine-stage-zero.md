# WeilConjectures.dlAdicLocalCompatible_zero

## Reason

The returned delivery did not land after the module was quarantined. The current
rework root reports failure to synthesize `OfNat (A.toStage hA ⟶ B.toStage hB) 0`
when applying the common-stage representative formula. Restore the archived module
and give this zero the existing cached stage-Hom type. The D4 claim is already held.

## Old

Public signature (unchanged):

```lean
theorem dlAdicLocalCompatible_zero (F G : DlAdicLocalRaw D c T) :
    dlAdicLocalCompatible D c T (InducedCategory.homMk (fun U ↦ (0 : F.value U ⟶ G.value U)))
```

Failing proof expression:

```lean
    have he := (commonStageDerivedPullback_existsUnique c.l c.Qbar
      (T.left.homOfLE h)).exists.choose_spec.2 A B L hA hB 0
```

## New

```lean
    have he := (commonStageDerivedPullback_existsUnique c.l c.Qbar
      (T.left.homOfLE h)).exists.choose_spec.2 A B L hA hB
      (0 : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩)
```

All public signatures, visibility, attributes, imports and non-theorem bodies are
unchanged from the quarantine archive. The existing stage-Hom instance provides the
same zero; no new instance or mathematical assumption is introduced. The archive and
DAG attachment remain intact. No target meaning changes and consumers need no source
adaptation. The module compiles cleanly in 27.2 seconds through `lcompile.py`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | D4 | Restore full module; repair proof only. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.DlLocalHeartAbelianEvaluation | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.DlLocalHeartCoverBasisZero | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.DlLocalHeartCoverDefects | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ShiftedCoefficientLinesInvertible | unclaimed | Unchanged interface; no adaptation. |

## Status

landed 20261027T135100-L-3665056 2026-10-27 (merge of deliver/D4/Sheaf.Paper.DlLocallyConstructibleAdicHeart)
