/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalIntegralBoundaryPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalBaseChangeCartesian
public import WeilConjectures.AlgebraicGeometry.DiagonalReductionPullback

/-! # The integral diagonal boundary under simultaneous reduction and pullback

Source: blueprint coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalIntegralBoundary diagonalBoundarySource diagonalBoundaryUnits

private theorem exactBoundary_square
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : C} {S' T' : D} (a : F.obj S ⟶ S') (b : F.obj T ⟶ T')
    (κ : Ext S T 1) (κ' : Ext S' T' 1)
    (h : (Ext.mk₀ a).comp κ' (zero_add 1) =
      (κ.mapExactFunctor F).comp (Ext.mk₀ b) (add_zero 1)) :
    F.mapDerivedCategory.map κ.hom ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app T ≫
          (DerivedCategory.singleFunctor D 0).map b)⟦(1 : ℤ)⟧' =
      ((F.mapDerivedCategorySingleFunctor 0).hom.app S ≫
        (DerivedCategory.singleFunctor D 0).map a) ≫ κ'.hom := by
  have hh := congrArg (fun z : Ext (F.obj S) T' 1 ↦ z.hom) h
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom, ShiftedHom.map] at hh
  apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app S)).1
  simpa only [ShiftedHom, Nat.cast_one, Nat.cast_ofNat,
    Functor.comp_obj, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc] using! hh.symm

private theorem naturalBoundary_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (T : C ⥤ D) (V : D ⥤ F) (U : C ⥤ E) (T' : E ⥤ F)
    (q : T ⋙ V ⟶ U ⋙ T')
    {A B : C} {A' B' : E} (κ : A ⟶ B) (κ' : A' ⟶ B')
    (a : U.obj A ⟶ A') (b : U.obj B ⟶ B')
    (h : U.map κ ≫ b = a ≫ κ') :
    V.map (T.map κ) ≫ (q.app B ≫ T'.map b) =
      (q.app A ≫ T'.map a) ≫ T'.map κ' := by
  have hq := q.naturality κ
  change V.map (T.map κ) ≫ q.app B = q.app A ≫ T'.map (U.map κ) at hq
  rw [← Category.assoc, hq]
  simp only [Category.assoc]
  rw [← T'.map_comp, h, T'.map_comp]

/-- Naturality of the positive diagonal boundary holds before passing to the
inverse limit: every natural reduction comparison gives one equation in the
derived category of strict systems.

Source: blueprint coefficient changes (3), the Cartier extension followed by
simultaneous Kummer reduction.
(blueprint: lem-diagonal-reduced-boundary-pullback).

Proof: the Cartesian diagonal square identifies the supported integral source.
Pullback of the positive Cartier boundary gives an Ext equation with its units
endpoint. The exact-single and shift comparisons turn it into an equation of
integral derived arrows. Naturality of the supplied reduction comparison and
functoriality of reduction give the displayed strict-system equation. No finite
evaluation functor is used to detect equality. -/
theorem diagonalReducedBoundary_pullback (l : ℕ) [Fact l.Prime]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))) :
    let F := upperStar Ab.{u + 1} (baseW g)
    let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (baseW g)
    let V := (Functor.whiskeringRight ℕᵒᵖ
      (DiagonalMod l (diagonalSurface Y)) (DiagonalMod l (diagonalSurface Y'))).obj G
    let S := (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).obj
      (diagonalIntegralSource Y)
    let T := ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧
    let a := (F.mapDerivedCategorySingleFunctor 0).hom.app (diagonalIntegralSource Y) ≫
      (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y')) 0).map
        (diagonalBoundarySource (baseW g) (baseP g) (diagonalBaseChange_cartesian g).toCommSq)
    let b := (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app (diagonalComparisonUnits Y) ≫
        (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y')) 0).map
          (diagonalBoundaryUnits (baseW g)))⟦(1 : ℤ)⟧'
    ∀ q : D.T ⋙ V.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ D'.T,
      V.mapDerivedCategory.map (D.T.map (diagonalIntegralBoundary Y).hom) ≫
          (q.app T ≫ D'.T.map b) =
        (q.app S ≫ D'.T.map a) ≫ D'.T.map (diagonalIntegralBoundary Y').hom := by
  intro F G V S T a b q
  apply naturalBoundary_square D.T V.mapDerivedCategory F.mapDerivedCategory D'.T q
  exact exactBoundary_square F _ _
    (diagonalIntegralBoundary Y) (diagonalIntegralBoundary Y')
    (diagonalIntegralBoundary_pullback (baseW g) (baseP g)
      (diagonalBaseChange_cartesian g)).2

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
