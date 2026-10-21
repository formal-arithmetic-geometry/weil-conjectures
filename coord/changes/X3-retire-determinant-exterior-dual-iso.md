# AlgebraicGeometry.exteriorSheaf_dual_iso

## Reason

Complete the retirement listed in `coord/retire-items.tsv`:893. The adopted
`WeilConjectures.AlgebraicGeometry.DeterminantExteriorDualIso` already proves the
same determinant-duality theorem using the canonical sectionwise `exteriorPower`
construction. The duplicate Sheaf theorem uses `exteriorSheaf`; the sole consumer
is adapted to transport the adopted isomorphism through
`Scheme.Modules.exteriorSheafPowerIso`. No upstream source file or target statement
changes.

## Old

The duplicate declaration was in
`lean/Sheaf/AlgebraicGeometry/DeterminantExteriorDualIso.lean`:

```lean
theorem exteriorSheaf_dual_iso (X : Scheme.{u}) (M : X.Modules) (d : ℕ)
    (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((Scheme.Modules.exteriorSheaf
      (SheafOfModules.homObj (R := X.sheaf) M
        (SheafOfModules.unit X.ringCatSheaf)) d) ≅
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M d))
```

## New

The node is attached to the unchanged adopted declaration:

```lean
theorem exteriorSheaf_dual_iso (X : Scheme.{u}) (M : X.Modules) (d : ℕ)
    (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((Scheme.Modules.exteriorPower
      (SheafOfModules.homObj (R := X.sheaf) M
        (SheafOfModules.unit X.ringCatSheaf)) d) ≅
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M d))
```

The duplicate module is withdrawn through `deleted.txt`. Its sole consumer,
`Sheaf.AlgebraicGeometry.DeterminantDualEvaluation` (unclaimed), now imports the
adopted theorem and `Modules.ExteriorSheafPowerComparison`. It forms
`exteriorSheafPowerIso (dual M) ≪≫ e ≪≫ dualFunctor.mapIso (exteriorSheafPowerIso M).op`,
which has exactly the old sheafified type. The consumer's public imports,
statement, docstring and all other proof steps are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | forced import and proof transport |

## Status

landed 20261021T004846-L-1796014 2026-10-21 (merge of deliver/X3/Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso)
