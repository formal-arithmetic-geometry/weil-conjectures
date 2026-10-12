/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# Composition of morphisms of sites

Source: Stacks Project, Lemma 03CB and Definition 03CC
(blueprint: lem-weil-pbc-site-morphism-composition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Lemma 03CB and Definition 03CC
(blueprint: lem-weil-pbc-site-morphism-composition).

The precoverages encode the sites of 00VH, and the covering and pullback hypotheses
are the two conditions of 00WV. The `IsContinuous` instances are their consequences
by `siteContinuous_pushforward_isSheaf`; they only make the sheaf functors typeable.
`sheafPullback` here is the left-Kan-extension followed by sheafification construction,
not the arbitrarily chosen left adjoint. Both coefficients use the same construction.

Proof:
1. Apply each covering condition successively. Compose the two pullback comparison
   isomorphisms. This proves Stacks continuity of the composite. Precomposition
   agrees objectwise and on restriction maps, hence agrees as a functor, for sets
   and abelian groups (lem-weil-pbc-site-continuous-pushforward-sheaf and
   lem-weil-pbc-sheaf-algebraic-structures-objects).
2. Compose the adjunctions of
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction using
   def-weil-pbc-composite-adjunction. The composite right adjoint is the functor in
   step 1. Uniqueness of left adjoints gives the unique isomorphism compatible with
   units (lem-weil-pbc-conjugate-iso-unit-equation). Its component equation below
   is exactly the composite unit: eta_v followed by v^s applied to eta_u at v_s F.
3. Finite limits and colimits are preserved by successive application of the two
   preservation hypotheses. Transport along the isomorphism of step 2. This is
   exactness of the composite left adjoint. Together with step 1 it defines the
   composite morphism of sites; its direct and inverse images are the functors in
   steps 1 and 2, as in 03CC. -/
theorem siteMorphism_composition
    {C₁ C₂ C₃ : Type u} [SmallCategory C₁] [SmallCategory C₂] [SmallCategory C₃]
    (J₁ : Precoverage C₁) (J₂ : Precoverage C₂) (J₃ : Precoverage C₃)
    [J₁.HasIsos] [J₁.IsStableUnderComposition] [J₁.IsStableUnderBaseChange] [J₁.HasPullbacks]
    [J₂.HasIsos] [J₂.IsStableUnderComposition] [J₂.IsStableUnderBaseChange] [J₂.HasPullbacks]
    [J₃.HasIsos] [J₃.IsStableUnderComposition] [J₃.IsStableUnderBaseChange] [J₃.HasPullbacks]
    (U : C₂ ⥤ C₁) (V : C₃ ⥤ C₂)
    (hUcover : ∀ (X : C₂) (R : Presieve X), R ∈ J₂ X → R.map U ∈ J₁ (U.obj X))
    (hUpullback : ∀ (X Y Z : C₂) (R : Presieve X), R ∈ J₂ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (hVcover : ∀ (X : C₃) (R : Presieve X), R ∈ J₃ X → R.map V ∈ J₂ (V.obj X))
    (hVpullback : ∀ (X Y Z : C₃) (R : Presieve X), R ∈ J₃ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) V)
    [U.IsContinuous J₂.toGrothendieck J₁.toGrothendieck]
    [V.IsContinuous J₃.toGrothendieck J₂.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback U (Type u)
      J₂.toGrothendieck J₁.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback U (Type u)
      J₂.toGrothendieck J₁.toGrothendieck)]
    [PreservesFiniteLimits (sheafPullback V (Type u)
      J₃.toGrothendieck J₂.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback V (Type u)
      J₃.toGrothendieck J₂.toGrothendieck)] :
    (∀ (X : C₃) (R : Presieve X), R ∈ J₃ X →
      R.map (V ⋙ U) ∈ J₁ ((V ⋙ U).obj X)) ∧
    (∀ (X Y Z : C₃) (R : Presieve X), R ∈ J₃ X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) (V ⋙ U)) ∧
    ∃ (hVU : (V ⋙ U).IsContinuous J₃.toGrothendieck J₁.toGrothendieck),
      ((V ⋙ U).sheafPushforwardContinuous (Type u) J₃.toGrothendieck J₁.toGrothendieck =
        U.sheafPushforwardContinuous (Type u) J₂.toGrothendieck J₁.toGrothendieck ⋙
          V.sheafPushforwardContinuous (Type u) J₃.toGrothendieck J₂.toGrothendieck) ∧
      (∃! e : sheafPullback (V ⋙ U) (Type u) J₃.toGrothendieck J₁.toGrothendieck ≅
          sheafPullback V (Type u) J₃.toGrothendieck J₂.toGrothendieck ⋙
            sheafPullback U (Type u) J₂.toGrothendieck J₁.toGrothendieck,
        ∀ F : Sheaf J₃.toGrothendieck (Type u),
          (sheafAdjunctionContinuous (V ⋙ U) (Type u)
            J₃.toGrothendieck J₁.toGrothendieck).unit.app F ≫
            ((V ⋙ U).sheafPushforwardContinuous (Type u)
              J₃.toGrothendieck J₁.toGrothendieck).map (e.hom.app F) =
          (sheafAdjunctionContinuous V (Type u)
            J₃.toGrothendieck J₂.toGrothendieck).unit.app F ≫
            (V.sheafPushforwardContinuous (Type u) J₃.toGrothendieck J₂.toGrothendieck).map
              ((sheafAdjunctionContinuous U (Type u)
                J₂.toGrothendieck J₁.toGrothendieck).unit.app
                ((sheafPullback V (Type u) J₃.toGrothendieck J₂.toGrothendieck).obj F))) ∧
      ((V ⋙ U).sheafPushforwardContinuous AddCommGrpCat.{u} J₃.toGrothendieck J₁.toGrothendieck =
        U.sheafPushforwardContinuous AddCommGrpCat.{u} J₂.toGrothendieck J₁.toGrothendieck ⋙
          V.sheafPushforwardContinuous AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck) ∧
      (∃! e : sheafPullback (V ⋙ U) AddCommGrpCat.{u} J₃.toGrothendieck J₁.toGrothendieck ≅
          sheafPullback V AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck ⋙
            sheafPullback U AddCommGrpCat.{u} J₂.toGrothendieck J₁.toGrothendieck,
        ∀ F : Sheaf J₃.toGrothendieck AddCommGrpCat.{u},
          (sheafAdjunctionContinuous (V ⋙ U) AddCommGrpCat.{u}
            J₃.toGrothendieck J₁.toGrothendieck).unit.app F ≫
            ((V ⋙ U).sheafPushforwardContinuous AddCommGrpCat.{u}
              J₃.toGrothendieck J₁.toGrothendieck).map (e.hom.app F) =
          (sheafAdjunctionContinuous V AddCommGrpCat.{u}
            J₃.toGrothendieck J₂.toGrothendieck).unit.app F ≫
            (V.sheafPushforwardContinuous AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck).map
              ((sheafAdjunctionContinuous U AddCommGrpCat.{u}
                J₂.toGrothendieck J₁.toGrothendieck).unit.app
                ((sheafPullback V AddCommGrpCat.{u} J₃.toGrothendieck J₂.toGrothendieck).obj F))) ∧
      Nonempty (PreservesFiniteLimits (sheafPullback (V ⋙ U) (Type u)
        J₃.toGrothendieck J₁.toGrothendieck)) ∧
      Nonempty (PreservesFiniteColimits (sheafPullback (V ⋙ U) (Type u)
        J₃.toGrothendieck J₁.toGrothendieck)) := by
  sorry

end CategoryTheory
