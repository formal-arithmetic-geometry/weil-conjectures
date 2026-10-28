# AlgebraicGeometry.Scheme.lisseTower_localized_actual_normalized

## Reason

STATEMENT-DISPUTED: the original theorem asserts coherence for arbitrary level
isomorphisms `actual`, although no hypothesis relates them to `e` or to each other.
Take coefficient ring F3, zero ideal, and a geometric point. At levels 1 and 2
the rank-one constant tower has identity transition. Changing the sign at just one
of those levels changes one side of the equation
and leaves the other side unchanged. The original assertion would force -1 = 1.
This defect was introduced by splitting coherent existence into bare level existence
and compatibility of every possible family. Naturality of functor comparisons does
not imply compatibility of arbitrary object isomorphisms.

The repair constructs the family using one coherent comparison of functors. Its
source coefficient square and target coefficient square are independent of any
chosen descent markings. The corrected theorem proves the passage between them
using naturality and the supplied descent equation. The sole parent keeps its exact
statement and now constructs this family. No target or existing definition changes.

## Old

```lean
theorem lisseTower_localized_actual_normalized
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (c : ∀ n : ℕ, LisseTowerScalarSquare (U.hom ≫ g) d n)
    (hc : ∀ n : ℕ, LisseTowerScalarSquareSections (U.hom ≫ g) d n (c n))
    (δ : ∀ n : ℕ, D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (hδ : ∀ n : ℕ,
      (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map (δ n) ≫
          (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map (e n).hom =
        (e (n + 1)).hom ≫
          adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n))
    (actual : ∀ (n : ℕ),
      ((ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d n).obj
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :
    ∀ (n : ℕ),
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual n).hom =
    (H (n + 1)).map (actual (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
```

## New

```lean
theorem lisseTower_localized_actual_normalized
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (cmp : LisseTowerLocalizationComparisons X Y g d U V W f)
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (c : ∀ n : ℕ, LisseTowerScalarSquare (U.hom ≫ g) d n)
    (hc : ∀ n : ℕ, LisseTowerScalarSquareSections (U.hom ≫ g) d n (c n))
    (δ : ∀ n : ℕ, D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (hδ : ∀ n : ℕ,
      (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map (δ n) ≫
          (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map (e n).hom =
        (e (n + 1)).hom ≫
          adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n)) :
    ∀ (n : ℕ),
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    let actual (j : ℕ) := (cmp.level j).app (D j) ≪≫
      (cmp.pull j).mapIso (e j) ≪≫ (cmp.base j).app (M.level j)
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual n).hom =
    (H (n + 1)).map (actual (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
```

The new public module `Sheaf.Paper.LisseTowerLocalizationComparisons` exposes the
comparison-system structure and its existence theorem, and the two explicitly
constructed operations on arbitrary semilinear arrows. The item publicly imports
this module because its corrected signature uses the structure. This module
publicly imports the former public dependency `LisseTowerPulledScalar`, preserving
visibility of the existing API. No public definition selects a witness of the
new existence theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseTowerLocalizedActualNormalized | X6 | Corrected false signature and proved the constructed-family equation. |
| Sheaf.Paper.LisseTowerLocalizedActual | unclaimed (server checked 2026-10-28) | Sole declaration caller and direct importer. Signature unchanged; proof constructs the family and applies the corrected theorem. Removes the private import of LisseTowerLocalizedActualLevels. |
| Sheaf.Paper.LisseTowerLocalizedRealization | indirect importer; unchanged | Uses the parent's unchanged existential theorem; no adaptation required. |

`tools/downstream.py --uses` found no other source use of the changed declaration.
The remaining indirect importers use unchanged interfaces. The current server queue
listed the item as `proof`, with one hole; no rework row or build-error file named it.
The level-existence module is held by X5 and has not been modified or withdrawn.

## Status

landed 20261028T055828-L-814363 2026-10-28 (merge of deliver/X6/Sheaf.Paper.LisseTowerLocalizedActualNormalized)
