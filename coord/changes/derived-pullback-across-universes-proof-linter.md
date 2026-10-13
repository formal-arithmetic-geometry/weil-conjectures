# AlgebraicGeometry.exists_derivedPullbackAcrossUniverses_monoidal_adjunction

## Reason

The existing existential binder `m` does not occur in the second conjunct. When its
proof hole is replaced, the unusedVariables linter warns about that existing binder.
Keep the statement verbatim and disable that linter only for this declaration.
The command is scoped to the theorem; it changes no definition, signature, visibility,
instance, notation, or behavior seen by importers. The static preflight treats added
commands conservatively as context changes and requests this record.

## Old

The declaration used the default linter options:

```lean
theorem exists_derivedPullbackAcrossUniverses_monoidal_adjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ m : (derivedPullbackAcrossUniverses f).CoreMonoidal,
      Nonempty (derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f) := by sorry
```

## New

`set_option linter.unusedVariables false in` immediately precedes the existing
unchanged docstring and theorem, so the option applies only to that theorem.
The unchanged signature is:

```lean
theorem exists_derivedPullbackAcrossUniverses_monoidal_adjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ m : (derivedPullbackAcrossUniverses f).CoreMonoidal,
      Nonempty (derivedPullbackAcrossUniverses f ⊣ schemeDerivedDirectImage f)
```

Its proof is the monoidal-composition and derived-adjunction uniqueness assembly.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionProjection | not adapted | None: all existing signatures and visibility are unchanged. |

No module requires adaptation: this is a scoped proof-linter setting only.

## Status

landed 20261013T123543-L-3710646 2026-10-13 (merge of deliver/E2/Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction)
