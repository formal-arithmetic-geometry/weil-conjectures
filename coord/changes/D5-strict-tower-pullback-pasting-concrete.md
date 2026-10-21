# AlgebraicGeometry.ProEtale.StrictTower.squareG_pasting_inv

## Reason

Repair the returned packet C-c7970 by retaining the original explicit public
statement and proving it with a concrete compositor calculation. The returned
family-law representation is omitted. Its conversion to the concrete component
equation repeatedly compared large derived-category instances, causing kernel
timeouts in the item and its unchanged U3 consumer.

The private helper `squareG_eq` expands the concrete square directly, without
introducing a generic category family. Three applications of the already proved
`gCompEq_coherence` complete the argument. The final item compiles in 3.6 s and the
unchanged U3 consumer in 28.2 s, at standard limits. No target meaning changes.

## Old

```lean
theorem squareG_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : Derived B X) :
    (gComp B b a).hom.app ((G B j).obj N) ≫
        (G B b).map ((squareG B a j₁ j g w₁).inv.app N) ≫
        (squareG B b j₂ j₁ h w₂).inv.app ((G B g).obj N) =
      (squareG B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (G B j₂).map ((gComp B h g).hom.app N)
```

## New

```lean
theorem squareG_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : Derived B X) :
    (gComp B b a).hom.app ((G B j).obj N) ≫
        (G B b).map ((squareG B a j₁ j g w₁).inv.app N) ≫
        (squareG B b j₂ j₁ h w₂).inv.app ((G B g).obj N) =
      (squareG B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (G B j₂).map ((gComp B h g).hom.app N)
```

The public signature, public import and original docstring are retained verbatim.
There are no new public definitions or consumer edits. The proof-only import is
`import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence`; it supplies
proved private coherence and elementary rearrangement helpers. Two new private
helpers are fully proved. The following settings apply only inside this module:

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G gComp gCompEq squareG towers_hasDerivedCategory
```

The three theorem declarations also locally disable
`CategoryTheory.catToReflQuiver` with declaration-scoped `attribute [-instance] ... in`.
No debugging or increased resource-limit setting remains.

## Users

`tools/downstream.py ... --uses squareG_pasting_inv` currently lists 23 transitive
modules and identifies only `StrictTowerProperOpenCalculus` as an external textual
user (two uses). Its current source compiled unchanged against this delivery.
The table records current claim holders; no listed module requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.StrictTowerPullbackSquarePasting` | D5 | Original explicit signature; one hole proved. |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | U3 | Original two uses compile unchanged in 28.2 s. |
| `Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | U1 | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | C8 | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingTensorComparison` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingTensorSupport` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.CategoryTheory.FilteredDerivedOperationLifts` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.CanonicalRingedRefinementShape` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.CanonicalRingedRefinementSquare` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.ProperOpenTowerComparison` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RefinementExchangeCoherence` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RingedRefinementClopen` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RingedRefinementCoefficientSquare` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RingedRefinementConstruction` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RingedRefinementCore` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RingedRefinementData` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.RingedRefinementFinite` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.Paper.SystemTensorMateArrows` | unclaimed | Original signature retained; no source adaptation. |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | T3 | Original signature retained; no source adaptation. |

## Status

landed 20261021T020105-L-2584464 2026-10-21 (merge of deliver/D5/Sheaf.AlgebraicGeometry.StrictTowerPullbackSquarePasting)
