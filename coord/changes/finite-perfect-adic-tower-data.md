# AlgebraicGeometry.Scheme.FinitePerfectAdicAlgebraTower

## Reason

Move the existing data declarations to `Sheaf.Paper.FinitePerfectAdicTowerData`, publicly
imported by the item. The two finite-level preparation modules must use these data without
importing the extraction theorem that uses them. This prevents an import cycle. Every
existing declaration name, signature, definition body, visibility and instance scope is
preserved. The theorem `finitePerfectAdicConstant_exact` also keeps its proof verbatim.
Only the module docstring and blueprint attachments of the moved data are updated.

Two concrete convenience definitions are added: `finitePerfectAdicModelDiagram` names the
existing right-hand diagram, and `finitePerfectAdicChartObject` composes the actual scheme
morphisms. Neither chooses data from an existence theorem.

## Old

The following declarations were in `Sheaf.Paper.FinitePerfectAdicTowerExtraction`:

```lean
structure FinitePerfectAdicAlgebraTower {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) where
  level : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  transition : ∀ n : ℕ, level (n + 1) ⟶
    (DerivedCategory.adicStepRestriction d.ideal n).obj (level n)
  extension : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
    DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  adjunction : ∀ n : ℕ, extension n ⊣ DerivedCategory.adicLevelRestriction d.ideal n
  stepExtension : ∀ n : ℕ,
    DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  stepAdjunction : ∀ n : ℕ, stepExtension n ⊣ DerivedCategory.adicStepRestriction d.ideal n
  normalized : ∀ n : ℕ, IsIso
    (((stepAdjunction n).homEquiv (level (n + 1)) (level n)).symm (transition n))
  residuePerfect : DerivedCategory.IsPerfect (level 0)
```

Alongside it were `finitePerfectAdicAlgebraDerived`, `finitePerfectAdicConstant`,
`finitePerfectAdicConstant_exact`, `finitePerfectAdicDerivedConstant`,
`finitePerfectAdicLocalRealization`, `finitePerfectAdicRestrictedTower` and
`FinitePerfectAdicLocalTower`. All six original public imports were in this module.

## New

The declaration above, all seven companion declarations and all six public imports are
preserved in `Sheaf.Paper.FinitePerfectAdicTowerData`. The extraction module begins with:

```lean
public import Sheaf.Paper.FinitePerfectAdicTowerData
```

It therefore reexports the same declarations and the same imported interfaces. The
extraction theorem's signature is unchanged. The new finite-level preparation modules
are proof imports of the extraction module. No existing definition is mathematically
changed, so no target-statement meaning changes.

## Users

All listed existing users are unclaimed in the current shared claim records.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FinitePerfectAdicTowerExtraction | K6 | Same data publicly reexported; theorem proof replaced. |
| Sheaf.Paper.FinitePerfectAdicQuotientDiagram | unclaimed | Direct importer; names and definitions unchanged. |
| Sheaf.Paper.FinitePerfectAdicTowerLimit | unclaimed | Direct importer; local tower and realization unchanged. |
| Sheaf.Paper.FinitePerfectAdicComplexRoos | unclaimed | Direct importer; public imports preserved transitively. |
| Sheaf.Paper.FinitePerfectAdicMarkedRoos | unclaimed | Indirect user of local realization and the algebraic localization. |
| Sheaf.Paper.FinitePerfectAdicRealization | unclaimed | Indirect user of extraction and the constant realization. |
| Sheaf.Paper.FinitePerfectAdicCanonicalComparison | unclaimed | Indirect user of local realization. |

The direct importers are compiled unchanged against the relocated data and new extraction
proof. Their sandbox copies are removed after validation; no consumer edits are delivered.
The remaining transitive import closure sees identical existing signatures and bodies.
`tools/downstream.py --uses FinitePerfectAdicAlgebraTower` finds the original item itself;
the table also includes every source file that mentions any moved declaration, and the
additional direct importer that reexports the item.

## Status

landed 20261027T050617-L-244429 2026-10-27 (merge of deliver/K6/Sheaf.Paper.FinitePerfectAdicTowerExtraction)
