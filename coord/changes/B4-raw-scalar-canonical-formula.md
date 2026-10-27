# AlgebraicGeometry.Etale.RawModuleScalarComparison

## Reason

The current source already contains P2's canonical-construction migration, landed
2026-10-24. The assigned module has zero holes and reexports the exact scalar-forgetting
API. The construction node nevertheless claims that the new adjunction-mate comparison
equals the original Kan-extension/sheafification composite, while the previous delivery
retained that identification only as a scratch regression. Retain the complete
identification in the actual library, with the unit equation and its uniqueness theorem.
This is additional checked construction verification, not a rebase or a hole-count gain.

No existing definition, theorem signature, instance, public import or target changes.
The Lean change is three fully proved public characterization lemmas in the
assigned Sheaf module, plus a proof-only import of
`Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition`. There is no new construction or arbitrary choice.

## Old

The assigned compatibility module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! # Compatibility import for the canonical scalar-forgetting comparison

The canonical comparison and free-generator maps are supplied by the adopted
upstream module. The derived-comparison module retains the historical exact
forgetting abbreviations and instances. This import path remains necessary for
quarantined consumers and introduces no duplicate constructions.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison).
-/

@[expose] public section
```

## New

The same public import and all existing exports are retained. A private proof import
provides its already-proved private `scalar_unit` identity. The module additionally
proves the following signatures in namespace
`AlgebraicGeometry.Etale.RawModuleScalarComparison`:

```lean
theorem pullback_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (pullback Λ f F) =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F)

theorem eq_pullback_of_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : (upperStar AddCommGrpCat.{u + 1} f).obj ((forget Λ Y).obj F) ⟶
      (forget Λ X).obj ((upperStar (ModuleCat.{u + 1} Λ) f).obj F))
    (hc : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫ (lowerStar AddCommGrpCat.{u + 1} f).map c =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F)) :
    c = pullback Λ f F

theorem kanSheafification_eq_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let G := (MorphismProperty.Over.pullback @Etale ⊤ f).op
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (U.leftKanExtensionCompIsoOfPreserves F.obj G).inv ≫
      (sheafComposeNatTrans X.smallEtaleTopology U
        (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
          (G.lan.obj F.obj) = pullback Λ f F
```

`pullback_unit` reuses the fully proved private `scalar_unit` identity; it does not
assume the public sheaf-composition theorem.
`eq_pullback_of_unit` applies injectivity of that equivalence.
`kanSheafification_eq_pullback` composes the inverse Kan-extension comparison with
sheafification and the coefficient sheafification comparison. The proof computes its
adjoint using the two composite adjunction units, sheafification-unit naturality,
`sheafComposeNatTrans_fac` and `leftKanExtensionCompIsoOfPreserves_inv_fac`.
The proof follows the adopted ModuleAbelianInverseImageComparison proof, retaining
its equality conclusion rather than only invertibility.

## Users

The added names have no existing users; `tools/downstream.py` with
`--uses kanSheafification_eq_pullback` finds none. The existing import path and every
existing declaration retain exactly the same meaning. The current direct importers
were read against their coefficient constructions; neither needs source adaptation.
No quarantined path or attachment is withdrawn or restored.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison | B4 | Three complete characterization proofs added; existing reexport retained. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | unclaimed | Its proved private scalar unit identity is reused through a proof-only import. Its source and public theorem are unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso | unclaimed | Continues providing the exact forgetting aliases and derived comparison, unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Integral generator, root map and Ext realization use the same canonical constructions; no adaptation needed. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Coefficient realization and scalar adjunction use the same retained API; no adaptation needed. |

The scalar construction node keeps its upstream Lean attachment and its mathematical
statement/dependencies. Its proof and Lean note now identify the retained verification
theorems. No target-meaning review is reopened because no existing definition changes.

## Status

landed 20261024T035804-L-1154508 2026-10-24 (merge of deliver/B4/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
