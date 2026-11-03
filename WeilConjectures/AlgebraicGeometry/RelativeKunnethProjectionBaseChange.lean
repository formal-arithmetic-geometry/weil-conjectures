/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import all WeilConjectures.AlgebraicGeometry.ProperRelativeKunnethSupports

/-! # Base change for the inverse compact-support projection formula -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open Lean Meta Elab Tactic
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

private theorem kunneth_inverse_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {X' Y' : D} (i : X ≅ Y) (j : X' ≅ Y')
    (a : F.obj X ⟶ X') (b : F.obj Y ⟶ Y')
    (h : F.map i.hom ≫ b = a ≫ j.hom) :
    F.map i.inv ≫ a = b ≫ j.inv := by
  apply (cancel_epi (F.map i.hom)).1
  have hid : F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id X
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
  rw [hid, Category.id_comp]
  apply (cancel_mono j.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm

private theorem kunneth_projection_forward_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f b)
    (K : DerivedCategoryModule A X)
    (L : DerivedCategoryModule A Y) :
    (L((b)^*[ModuleCat.{u + 1} A])).map (projectionIsoApp A f K L).hom ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
          ((L((f)^*[ModuleCat.{u + 1} A])).obj L)) ≫
      (R(f')_![ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a K
          ((L((f)^*[ModuleCat.{u + 1} A])).obj L)).hom ≫
      (R(f')_![ModuleCat.{u + 1} A]).map
        (((derivedTensor (ModuleCat.{u + 1} A) X').obj
          ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).map
            (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq L)) =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) b
      ((R(f)_![ModuleCat.{u + 1} A]).obj K) L).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y').map
        ((rightDerivedLowerShriekBaseChangeMap A sq).app K)).app
          ((L((b)^*[ModuleCat.{u + 1} A])).obj L) ≫
      (projectionIsoApp A f' ((L((a)^*[ModuleCat.{u + 1} A])).obj K)
        ((L((b)^*[ModuleCat.{u + 1} A])).obj L)).hom := by
  have hn := projectionMap_rightDerivedLowerShriekBaseChangeMap A sq K L
  simp only [leftDerivedUpperStarTensorIso_hom, projectionIsoApp_hom]
  dsimp only [rightDerivedLowerShriek, derivedTensorLeftDerivedUpperStar,
    leftDerivedUpperStarDerivedTensor, derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.postcompose₂,
    Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.comp_obj, Functor.id_obj, catToReflQuiver] at hn ⊢
  run_tac support_transport_local `hn

/-- Inverting the two projection-formula isomorphisms in the exchange square.
Source: thm-sf-kunneth-relative, base-change clause, projection factors.
(blueprint: lem-sf-relative-kunneth-projection-base-change).

Proof: precompose with pullback of the forward projection isomorphism and postcompose
with the primed forward projection isomorphism. Inverse cancellation leaves exactly
the published projection/exchange coherence equation. -/
theorem relativeKunneth_projection_inv_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f b)
    (K : DerivedCategoryModule A X)
    (L : DerivedCategoryModule A Y) :
    (L((b)^*[ModuleCat.{u + 1} A])).map (projectionIsoApp A f K L).inv ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) b
          ((R(f)_![ModuleCat.{u + 1} A]).obj K) L).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y').map
          ((rightDerivedLowerShriekBaseChangeMap A sq).app K)).app
            ((L((b)^*[ModuleCat.{u + 1} A])).obj L) =
      (rightDerivedLowerShriekBaseChangeMap A sq).app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
            ((L((f)^*[ModuleCat.{u + 1} A])).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} A]).map
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a K
            ((L((f)^*[ModuleCat.{u + 1} A])).obj L)).hom ≫
        (R(f')_![ModuleCat.{u + 1} A]).map
          (((derivedTensor (ModuleCat.{u + 1} A) X').obj
            ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).map
              (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq L)) ≫
        (projectionIsoApp A f' ((L((a)^*[ModuleCat.{u + 1} A])).obj K)
          ((L((b)^*[ModuleCat.{u + 1} A])).obj L)).inv := by
  have he := kunneth_inverse_square
    (L((b)^*[ModuleCat.{u + 1} A])) (projectionIsoApp A f K L)
    (projectionIsoApp A f' ((L((a)^*[ModuleCat.{u + 1} A])).obj K)
      ((L((b)^*[ModuleCat.{u + 1} A])).obj L))
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) b
      ((R(f)_![ModuleCat.{u + 1} A]).obj K) L).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y').map
          ((rightDerivedLowerShriekBaseChangeMap A sq).app K)).app
            ((L((b)^*[ModuleCat.{u + 1} A])).obj L))
    ((rightDerivedLowerShriekBaseChangeMap A sq).app
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
        ((L((f)^*[ModuleCat.{u + 1} A])).obj L)) ≫
      (R(f')_![ModuleCat.{u + 1} A]).map
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a K
          ((L((f)^*[ModuleCat.{u + 1} A])).obj L)).hom ≫
      (R(f')_![ModuleCat.{u + 1} A]).map
        (((derivedTensor (ModuleCat.{u + 1} A) X').obj
          ((L((a)^*[ModuleCat.{u + 1} A])).obj K)).map
            (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq L)))
    (by
      simpa only [Category.assoc] using
        kunneth_projection_forward_square A sq K L)
  simpa only [Category.assoc] using he

end AlgebraicGeometry.Etale
