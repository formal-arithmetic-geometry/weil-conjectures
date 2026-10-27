/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.TowerClassReduction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Integral line-bundle classes and geometric pullback

Source: blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
classes proof (2), and the integral extension argument in steps 1--3 of
lem-sp-tower-chern-pullback (blueprint: lem-sp-tower-integral-class-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Exact inverse image of entire abelian towers, by componentwise sheaf inverse image.
Source: the system-topos construction (blueprint: lem-sp-tower-integral-class-pullback). -/
def abPull {X Y : Scheme.{u}} (f : X ⟶ Y) : Ab Y ⥤ Ab X :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb Y) (DiagonalAb X)).obj
    (upperStar AddCommGrpCat.{u + 1} f)

instance abPull_additive {X Y : Scheme.{u}} (f : X ⟶ Y) : (abPull f).Additive := by
  unfold abPull
  infer_instance

instance abPull_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (abPull f) := by
  unfold abPull
  exact ⟨fun _ _ _ ↦ inferInstance⟩

instance abPull_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (abPull f) := by
  unfold abPull
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Pullback of full units along the projection of a base-changed chart.
Source: integral extension gluing (blueprint: lem-sp-tower-integral-class-pullback). -/
def unitsDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleUnitsSheaf Y ⟶
      (lowerStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf X) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (Additive.ofMul
            (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul))
          map_zero' := by
            apply ULift.ext
            exact (Units.map _).map_one
          map_add' := fun x y ↦ by
            apply ULift.ext
            exact (Units.map _).map_mul x.down.toMul y.down.toMul }
     naturality := by
      intro U V a
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Units.ext
      change (pullback.fst V.unop.hom f).appTop
          (a.unop.left.appTop x.down.toMul.val) =
        ((Scheme.proEtaleBaseChange f).map a.unop).left.appTop
          ((pullback.fst U.unop.hom f).appTop x.down.toMul.val)
      have h : ((Scheme.proEtaleBaseChange f).map a.unop).left ≫
          pullback.fst U.unop.hom f = pullback.fst V.unop.hom f ≫ a.unop.left :=
        pullback.lift_fst _ _ _
      exact congrArg (fun k ↦ k.appTop.hom x.down.toMul.val) h.symm }⟩

/-- Constant-integer comparison on towers, normalized by constant sections.
Source: inverse image of constants (blueprint: lem-sp-tower-integral-class-pullback). -/
def integerPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).obj (integers Y) ⟶ integers X :=
  { app := fun _ ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
      ((constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).symm
      (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    naturality := fun _ _ _ ↦ by
      change (upperStar AddCommGrpCat.{u + 1} f).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
      dsimp only [integers, units, constant, Functor.const_obj_obj]
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }

/-- Full-units comparison on constant towers, with no invertibility assertion.
Source: integral extension gluing (blueprint: lem-sp-tower-integral-class-pullback). -/
def unitsPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).obj (units Y) ⟶ units X :=
  { app := fun _ ↦ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
      (Scheme.proEtaleUnitsSheaf Y) (Scheme.proEtaleUnitsSheaf X)).symm (unitsDirect f)
    naturality := fun _ _ _ ↦ by
      change (upperStar AddCommGrpCat.{u + 1} f).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
      dsimp only [integers, units, constant, Functor.const_obj_obj]
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] }

/-- Derived constant-integer comparison, including the canonical single comparison.
Source: exact localization (blueprint: lem-sp-tower-integral-class-pullback). -/
def integerDerivedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)) ⟶
      (DerivedCategory.singleFunctor (Ab X) 0).obj (integers X) :=
  ((abPull f).mapDerivedCategorySingleFunctor 0).hom.app (integers Y) ≫
    (DerivedCategory.singleFunctor (Ab X) 0).map (integerPull f)

/-- Derived units comparison, including the canonical shift by one.
Source: exact localization (blueprint: lem-sp-tower-integral-class-pullback). -/
def unitsDerivedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abPull f).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Ab X) 0).obj (units X))⟦(1 : ℤ)⟧ :=
  ((abPull f).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    (((abPull f).mapDerivedCategorySingleFunctor 0).hom.app (units Y))⟦(1 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor (Ab X) 0).map (unitsPull f))⟦(1 : ℤ)⟧'

/-- Integral line-bundle classes commute with pullback to full units, in the ordinary
 derived category of abelian towers. No torsion coefficient or root comparison occurs.
Source: blueprint classes proof (2); lem-sp-tower-chern-pullback, steps 1--3
(blueprint: lem-sp-tower-integral-class-pullback).

Proof: choose Zariski frames e_a of L, with e_b = g_ab e_a. Glue G_m times Z by
(u,m)_b -> (g_ab^m u,m)_a. Its fibre over 1 is the generator torsor of L, so the
line-bundle/torsor and torsor/Ext correspondences identify its extension boundary with
lineBundleEtaleClass, after the specified etale-to-pro-etale comparison. The same
formulas with full pro-etale units give the pushout along cartierUnitsComparison;
naturality of the boundary identifies it with the definition of lineBundleClass.
On pulled frames the transition functions are the pullbacks of g_ab. The maps
(u,m) -> (f^*u,m) glue to a morphism of extensions whose endpoint maps are integerPull
and unitsPull. Exact inverse image and the naturality of the signed short-exact
boundary give the displayed equation. Constant towers and their transitions are
preserved throughout, and exact localization supplies precisely the single and shift
comparisons displayed in integerDerivedPull and unitsDerivedPull. The argument also
works for empty schemes, trivial bundles and nonflat f. -/
theorem tower_integralClass_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    (abPull f).mapDerivedCategory.map (lineBundleClass Y (Scheme.Pic.ofIsInvertible L)) ≫
        unitsDerivedPull f =
      integerDerivedPull f ≫
        lineBundleClass X (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
