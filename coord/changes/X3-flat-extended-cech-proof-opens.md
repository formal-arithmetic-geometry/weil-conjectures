# SheafOfModules.flat_extendedLocalizationCech_comparison_quasiIso

## Reason

The proof uses limits and monoidal-category notation in its private helpers and tensor
comparison. The namespace opens are file-local name-resolution commands. The interface
checker conservatively records changed commands as an interface change and requires this
record. No existing statement, visibility, public import, definition or global instance
changes. No consumer needs adaptation.

## Old

```lean
open CategoryTheory
```

Existing public signature, verbatim:

```lean
theorem flat_extendedLocalizationCech_comparison_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections)
    (hflat : IsFlat ((LocalizationCech.restriction φ).obj
      (unit (LocalizationCech.rings B))))
    (hquot : IsIso (LocalizationCech.quotientComparison φ r f)) :
    QuasiIso (LocalizationCech.comparison φ r f)
```

## New

```lean
open CategoryTheory CategoryTheory.MonoidalCategory
```

Inside `namespace SheafOfModules`:

```lean
open CategoryTheory.Limits
```

The existing public signature is identical:

```lean
theorem flat_extendedLocalizationCech_comparison_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections)
    (hflat : IsFlat ((LocalizationCech.restriction φ).obj
      (unit (LocalizationCech.rings B))))
    (hquot : IsIso (LocalizationCech.quotientComparison φ r f)) :
    QuasiIso (LocalizationCech.comparison φ r f)
```

The proof now uses signed Koszul contraction, uniform ideal-power annihilation, naturality
of exact-functor homology comparisons, and exact sequential colimits. The sole new deferred
statement is the finite tensor comparison, in its own module with its own node. The added
namespace opens and the scoped transparency option of a private proof are not exported.

## Users

`tools/downstream.py Sheaf.Paper.FlatExtendedCechComparison --uses
SheafOfModules.flat_extendedLocalizationCech_comparison_quasiIso` lists the item itself as
the only textual user and `Sheaf.Paper.FlatRingedIdealCompleteEquivalence` as the only
external importer. The latter currently does not mention the theorem by name. Both see
the identical public signature, public imports and definitions. No module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatExtendedCechComparison | X3 | Identical signature; proof reduced. |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | M1 | Identical imported interface; no edit. |

## Status

landed 20261018T071241-L-1683108 2026-10-18 (merge of deliver/X3/Sheaf.Paper.FlatExtendedCechComparison)
