# SheafOfModules.RingedCoefficientProjection.coefficientPullbackComparisons

## Reason

The proof needs private constructions, explicit local typeclass certificates and local
irreducibility attributes to avoid repeated unfolding. The returned packet also duplicated
the existing generic descent lemmas in `RingedProjectionPullbackComparisons`; this repair
removes both duplicates and reuses the existing proved private theorem.

## Old

```lean
theorem coefficientPullbackComparisons [PreservesFiniteLimits uInv] :
    Nonempty (Comparisons g nY nX) := by
  sorry
```

The sole public import was `Sheaf.Paper.RingedCoefficientProjectionData`.

## New

The signature, universes, parameters and sole public import are unchanged. The theorem
is proved. All new helpers are private and proved; added imports are proof-only.
The certificates `flatQuotient_full` and `flatQuotient_essSurj` are private theorems,
installed as explicit local class hypotheses. The existing binary-product cache is
registered locally and irreducibility attributes apply locally to private constructions.
The anonymous section is explicitly closed at EOF for appended inspection commands.

Relative to returned dd158ce46, remove private `iso_descent` and
`localization_iso_descent`, add proof-only
`import all Sheaf.Paper.RingedProjectionPullbackComparisons`, and call
`SheafOfModules.ProjectionCoherence.localization_iso_descent` in `flat_iso_descent`.
This imports the existing private API without adding public declarations or changing
its source module. The import-direction check reports no cycle.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | no local claim record | Same public comparison theorem; no adaptation. |
| Sheaf.Paper.ReductionOpenEtaleOrigin | no local claim record | Same public interface; no adaptation. |
| Sheaf.Paper.CanonicalRingedRefinementShape | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.RingedRefinementClopen | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.RingedRefinementConstruction | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.RingedRefinementCore | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.RingedRefinementData | no local claim record | Transitive consumer; same interface. |
| Sheaf.Paper.RingedRefinementFinite | no local claim record | Transitive consumer; same interface. |

`tools/downstream.py --uses` identifies only the cocycle module as an external textual
user of the comparison theorem. No consumer is adapted, no target-dependent definition
changes, and no target statement review is reopened. The source library is unchanged.

## Status

landed 20261021T111227-L-60755 2026-10-21 (merge of deliver/K2/Sheaf.Paper.RingedCoefficientPullbackComparison)

K2 stage-3 repair; independent review pending.
