# AlgebraicGeometry.smoothDiagonal_dualizing_determinant

## Reason

Restore the quarantined module without redeclaring names now provided by the adopted source
library. Its old private constant-rank comparison import has been retired; its old exterior
sheaf construction equals the canonical construction by an existing proved equality.
The canonical theorem has the same hypotheses, universes, shift, and mathematical conclusion.
The exact archived conclusion is checked by the proved private theorem
`AlgebraicGeometry.exteriorSheaf_compatibility` in the restored module.
No source-library declaration or public import is edited.

## Old

Archived public imports:

```lean
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
```

Archived signature:

```lean
theorem smoothDiagonal_dualizing_determinant (X S : Scheme.{u}) [IsNoetherian S] (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f] [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] [HasDerivedCategory.{wP} (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))] (hRΔ : ∀ E : schemeDerivedQCohCategory X, schemeDerivedQCohProperty (pullback f f) ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj)) (c : schemeDerivedQCohCategory (pullback f f) ⥤ schemeDerivedQCohCategory X) (adjC : (schemeDerivedQCohProperty (pullback f f)).lift ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c) (OP : schemeDerivedQCohCategory (pullback f f)) (hOP : OP.obj ≅ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj (SheafOfModules.unit (pullback f f).ringCatSheaf)) : Nonempty ((c.obj OP).obj ≅ ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (Scheme.Modules.exteriorSheaf (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧)
```

## New

The restored module reexports the canonical theorem and the equality of exterior sheaves:

```lean
public import WeilConjectures.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison
```

Canonical signature (node attachment):

```lean
theorem smoothDiagonal_dualizing_determinant (X S : Scheme.{u}) [IsNoetherian S] (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f] [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] [HasDerivedCategory.{wP} (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))] (hRΔ : ∀ E : schemeDerivedQCohCategory X, schemeDerivedQCohProperty (pullback f f) ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj)) (c : schemeDerivedQCohCategory (pullback f f) ⥤ schemeDerivedQCohCategory X) (adjC : (schemeDerivedQCohProperty (pullback f f)).lift ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c) (OP : schemeDerivedQCohCategory (pullback f f)) (hOP : OP.obj ≅ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj (SheafOfModules.unit (pullback f f).ringCatSheaf)) : Nonempty ((c.obj OP).obj ≅ ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj (Scheme.Modules.exteriorPower (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧)
```

All the old public statement prerequisites remain reachable through these imports.
The original theorem name is provided by the upstream import, so no duplicate declaration
is introduced. Its result uses `exteriorPower`; rewriting
`Scheme.Modules.exteriorSheaf_eq_exteriorPower` recovers the old result exactly.
The local private proof checks that rewrite, with the archived binders unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | T4 | Restored compatibility module; canonical upstream attachment; exact archived conclusion checked privately. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | quarantined, not a current Lean module | Archive preserved. Its DAG citation remains attached to this node. When restored, its use of the canonical result can be rewritten by exteriorSheaf_eq_exteriorPower, reexported by the bridge. No archived file is deleted or modified here. |

There are no current Lean importers or declaration users of the absent item path.
`tools/downstream.py` reports the item module unknown because it is quarantined;
a textual search of lean/ and quarantine/ identifies the archived consumer listed above.
The parent node's dependency edges are preserved, so this is not a withdrawal based on
zero live importers. The theorem it needs remains available from the canonical source.

## Status

landed 20261020T155828-L-3294386 2026-10-20 (merge of deliver/T4/Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant)
