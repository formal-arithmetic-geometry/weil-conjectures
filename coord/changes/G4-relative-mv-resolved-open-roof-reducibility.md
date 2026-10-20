# relativeMV_resolved_open_roof_comparison: local reducibility setting

## Reason

Restore the quarantined module for its assigned compile repair. Upstream now
declares `AlgebraicGeometry.derivedPullback` using `irreducible_def`. Lean rejects
the archived command that tries to mark it locally irreducible again:
`failed to set [local irreducible], derivedPullback is currently [irreducible]`.
Remove that redundant entry while preserving the three remaining local entries.

The full original file reproduces the error. With this one-token removal, the
full restored file compiles through `lcompile.py` in 33.7 seconds. The archive
and repair both contain zero `sorry`s. All declaration signatures, proofs,
docstrings and imports are identical to the archive. No definition or target
meaning changes, and no consumer adaptation is necessary. The delivery checker
classifies a changed attribute command as an interface change, so this record
documents the local-command edit for independent review.

## Old

```lean
attribute [local irreducible] derivedPullback Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh
```

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh
```

## Users

No live Lean module imports the quarantined item. Its two archived consumers
below retain the exact same public theorem signature; their own restoration is
outside this repair. No existing source-library declaration or public import is
changed, and no existing DAG attachment or dependency is removed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedOpenRoofComparison | G4 | Restored with the redundant local attribute removed; all declarations preserved. |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons | unclaimed (quarantined) | Uses the identical theorem signature; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMiddleMateComparison | unclaimed (quarantined) | Uses the identical theorem signature; no adaptation. |

## Status

landed 20261020T153007-L-2860838 2026-10-20 (merge of deliver/G4/Sheaf.AlgebraicGeometry.RelativeMVResolvedOpenRoofComparison)
