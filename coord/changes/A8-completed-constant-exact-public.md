# AlgebraicGeometry.Scheme.CompletedConstantReduction.constant_exact

## Reason

The return at delivery head `1258cccfe7d` requires reusing this exact theorem rather
than repeating its proof in `LocalIntegralPerfectModelCohomology`. It was private,
so expose it in its existing, unclaimed Sheaf module. Its binders, conclusion and
complete proof are unchanged. Add a source/proof docstring and record the helper
in the existing node's Lean declarations. No definition or target meaning changes.

## Old

```lean
private theorem constant_exact (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (adicLisseConstantModules T A) ∧
      PreservesFiniteColimits (adicLisseConstantModules T A)
```

## New

```lean
theorem constant_exact (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (adicLisseConstantModules T A) ∧
      PreservesFiniteColimits (adicLisseConstantModules T A)
```

This theorem occurs in an `@[expose] public noncomputable section`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedConstantSheafReduction | unclaimed | Expose the existing helper; its internal uses and proof are unchanged. |
| Sheaf.Paper.LocalIntegralPerfectModelCohomology | A8 | Remove the duplicate private theorem; apply the existing helper twice. |
| Sheaf.Paper.AdicReductionCohomologySequence | unclaimed | Existing qualified calls become public calls; no source edit needed. |
| Sheaf.Paper.TowerClassSystems | unclaimed | The downstream name scan finds its own unrelated `constant_exact`; no edit needed. |

These are all name matches reported by `tools/downstream.py` with `--uses`.
The broader import closure contains 1414 modules: existing public signatures,
imports and defining data are unchanged, and visibility is only increased.
The new theorem is qualified at its external call sites. No consumer requires
adaptation and no module held by another group is edited.

## Status

landed 20261021T120317-L-3749629 2026-10-21 (merge of deliver/A8/Sheaf.Paper.LocalIntegralPerfectModelCohomology)
