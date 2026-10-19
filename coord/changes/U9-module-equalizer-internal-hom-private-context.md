# CategoryTheory.Mod.nonempty_equalizerInternalHomAdjunction

## Reason

The proof needs four private helpers comparing the relative tensor coequalizer with
`Mod.tensorLeft`. They are enclosed in a section with `open MonoidalCategory Limits
MonObj in` and shared `variable` declarations. The interface checker conservatively
flags these commands. They end with the section, introduce no public instance or
notation, and do not alter any public signature or definition. The public imports
stay identical; one redundant proof-only import is removed.

## Old

```lean
theorem nonempty_equalizerInternalHomAdjunction
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    (R : C) [MonObj R] [IsCommMonObj R] (M : Mod C R) :
    Nonempty (MonoidalCategory.tensorLeft M ⊣ ihom' R M) := by
  sorry
```

There was no helper section.

## New

```lean
theorem nonempty_equalizerInternalHomAdjunction
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    (R : C) [MonObj R] [IsCommMonObj R] (M : Mod C R) :
    Nonempty (MonoidalCategory.tensorLeft M ⊣ ihom' R M) := by
  exact ⟨(ihom'Adjunction R M).ofNatIsoLeft
    (equalizerAdjTensorRightIso M ≪≫
      (BraidedCategory.tensorLeftIsoTensorRight M).symm)⟩
```

Four fully proved private definitions precede this theorem:
`equalizerAdjTensorπ`, `equalizerAdjTensorCofork`,
`isColimitEqualizerAdjTensorCofork`, and `equalizerAdjTensorRightIso`.
They share the following section-local context, closed immediately after the theorem:

```lean
open MonoidalCategory Limits MonObj in
section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom | U9 | Proves the existing statement; private helper scope only. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Imports the module for its proof; identical public signature and imports, no adaptation needed. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Imports the module for its proof; identical public signature and imports, no adaptation needed. |

These are the two direct importers. The helper section has no effect on any
transitive importer: it exports no notation, variable context, instance, or public
data definition. Neither direct importer refers to a private helper. No target
statement or definition used by a target changes, so no target review reopens.

## Status

landed 20261019T112551-L-3956233 2026-10-19 (merge of deliver/U9/Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom)
