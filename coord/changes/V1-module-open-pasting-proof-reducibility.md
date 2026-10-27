# AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting.moduleDirectImageOpenPasting

## Reason

Complete the original proof using the existing module functors and mate coherence API.
Local irreducibility attributes prevent proof elaboration from expanding the large chosen
compositors and adjunction into their scalar-extension constructions. The stage-3 static
command check requests this record because an `attribute` command was added. Every attribute
is explicitly `local`; no imported module receives a changed reducibility attribute.

## Old

No local irreducibility command in this module. The existing theorem was:

```lean
theorem moduleDirectImageOpenPasting :
    ∃ β : Comparisons Λ, Sectionwise Λ β ∧ Composition Λ ∧ SuccessiveOpens Λ β ∧
      MixedPasting Λ β ∧ Units Λ β ∧ Degreewise Λ β := by
  sorry
```

## New

The theorem signature above and all public definitions remain verbatim unchanged.
Its body is a complete proof from private constructions and proved private helpers.
The only additional command outside private declarations is:

```lean
attribute [local irreducible] lowerStarComp
  upperStarComp lowerStarId upperStarId lowerStarCongr upperStarLowerStarAdjunction
```

This command affects unfolding only within the current file. It neither changes a definition
body nor makes any new statement available to importers. The original public imports remain
verbatim; additional proof imports are private. Compilation with project defaults is clean
in 27.6 seconds. No new holes, axioms, or arbitrary existence witnesses are introduced.

## Users

`tools/downstream.py` was run with the module and the full theorem name. It lists two
downstream modules; direct textual theorem uses are the item and IdentityOpenModuleSections.
The current claim directory has no claim for either downstream module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | V1 | Original hole closed; local unfolding policy only. |
| Sheaf.AlgebraicGeometry.IdentityOpenModuleSections | unclaimed | Same theorem, coprojection and action-comparison signatures; no adaptation needed. |
| Sheaf.SixFunctors.OpenStarShriekScalarMateSquare | unclaimed | Private proof import sees the same public API; no adaptation needed. |

No target statement or definition used by a target is changed, so no target's statement review
is reopened. The DAG route is updated to match the proof; the affine-space unit route stays.

## Status

landed 20261024T020829-L-2673987 2026-10-24 (merge of deliver/V1/Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting)
