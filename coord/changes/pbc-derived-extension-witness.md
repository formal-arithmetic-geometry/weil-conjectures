# AlgebraicGeometry.Scheme.pbcDerivedExtensionExistence

## Reason

The retained specialized derived-adjunction argument exceeded the 60-second file limit.
The profiler showed definitional equality descending into concrete restriction-of-scalars
maps and the differentials of the mapped complex. The universally quantified categorical
argument now runs with abstract functors in the proved private helper
`normalizedDerivedAdjunction`. The nested existential witness is also given an explicit
stable type, changed from a reducible abbreviation to a definition with `@[no_expose]`.
This prevents importers from expanding its proof projections. The public characterizing
lemmas `pbcDerivedExtension_universal` and `pbcExtensionCounit_isIso` expose exactly its
universal property and its K-flat computation. The full module compiled in 13.3 seconds
before adding these two proved API lemmas.

## Old

```lean
abbrev pbcDerivedExtensionExistence :=
  (pbcExtensionExistence φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## New

```lean
@[no_expose] def pbcDerivedExtensionExistence :
    ∃ (LF : DerivedCategory (pbcModules X R) ⥤ DerivedCategory (pbcModules X S))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (pbcExtend φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (pbcModules X R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (pbcModules X R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (pbcExtensionExistence φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedConstructibleTower | K2 | The same witness with the same body and mathematical meaning; its two proven projections now have a named API. |

`tools/downstream.py Sheaf.Paper.BoundedConstructibleTower --uses
pbcDerivedExtensionExistence` finds only the item module itself. No other module mentions
this witness. Its existing public consumers inside the module keep identical signatures:
`pbcExtensionCounit` and `pbcDerivedScalarAdjunction_exists`. All other public signatures,
coefficient functors and local-model definitions stay identical. Consequently no consumer
adaptations are needed. The target statements and the meanings of their definitions are
unchanged; the independent reader can verify the witness body is verbatim identical.

## Status

landed 20261019T005311-L-2750273 2026-10-19 (merge of deliver/K2/Sheaf.Paper.BoundedConstructibleTower)
