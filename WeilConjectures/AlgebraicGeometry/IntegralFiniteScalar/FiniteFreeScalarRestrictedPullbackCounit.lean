/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarPullbackCounit

/-! # Restricted scalar counits and exact pullback

Source: blueprint scalar-six direct-image proof, formal properties and finite free
coefficient extensions.
(blueprint: new-sfb-finite-free-scalar-restricted-pullback-counit)
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

private instance ring_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X := Λ.comm

private instance map_monoid {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  DerivedCategory.monoidalClosed Mod.monoidalClosed
  Mod.monoidalCategoryStruct Sheaf.monoidalCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] derivedComapUpperStarIso comapUpperStarIso

set_option maxHeartbeats 1600000 in
set_option profiler true in
-- Compute the scalar mate before using any K-flat invertibility.
/-- Restricted scalar counits commute with exact geometric pullback and the normalized
scalar mate.
Source: blueprint scalar-six formal properties, pullback of scalar extension.
(blueprint: new-sfb-finite-free-scalar-restricted-pullback-counit)

Proof. The normalized scalar-mate counit equation gives the square before restriction.
Map it through exact restriction. The inverse derived comap comparison is natural for
that scalar counit. The exact-square factorization identifies its component on the
ordinary extension complex with the localization of the ordinary comap square.
Naturality of restriction's localization comparison moves the remaining ordinary
pullback isomorphism through Q. Compose these equations and reassociate. -/
theorem finiteFreeScalar_restrictedCounit_pullback
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ) :
    let F := CondensedRing.upperStar Λ.X f
    let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
    let EC := ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
        (.up ℤ)).obj C
    let p := (NatTrans.mapHomologicalComplex
      (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
    let q := (NatTrans.mapHomologicalComplex
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
        ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) ≫
      (restriction a X).map
        ((scalarSixChange a X).map (F.mapDerivedCategoryFactors.hom.app C)) ≫
      ((restriction a X).map (scalarCounit a X FC) ≫
        (Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
            (.up ℤ)).obj FC)) =
    (scalarSixPull Λ f).map (((restriction a Y).map (scalarCounit a Y C) ≫
        (Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapDerivedCategoryFactors.hom.app
            EC)) ≫
      F.mapDerivedCategoryFactors.hom.app
        (((Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
            (.up ℤ)).obj EC) ≫
      DerivedCategory.Q.map q ≫
      DerivedCategory.Q.map
        (((Mod.comap
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
            (.up ℤ)).map p) := by
  dsimp only
  let F := CondensedRing.upperStar Λ.X f
  let G := CondensedRing.upperStar Λ'.X f
  let RX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  let EC := ((Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)).mapHomologicalComplex
        (.up ℤ)).obj C
  let FC := (F.mapHomologicalComplex (.up ℤ)).obj C
  let p := (NatTrans.mapHomologicalComplex
    (pullIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app C
  let q := (NatTrans.mapHomologicalComplex
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv (.up ℤ)).app EC
  let d := derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f
  have hp : (D.theta a f).inv.app (DerivedCategory.Q.obj C) ≫
      (scalarSixChange a X).map (F.mapDerivedCategoryFactors.hom.app C) ≫
      scalarCounit a X FC =
    (scalarSixPull Λ' f).map (scalarCounit a Y C) ≫
      G.mapDerivedCategoryFactors.hom.app EC ≫ DerivedCategory.Q.map p := by
    apply (cancel_epi ((D.theta a f).hom.app (DerivedCategory.Q.obj C))).1
    simp only [Iso.hom_inv_id_app_assoc]
    have hs := finiteFreeScalar_pullback_scalarCounit D a f C
    erw [← reassoc_of% hs]
    simp only [← DerivedCategory.Q.map_comp]
    erw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp]
    simp only [Iso.hom_inv_id, NatTrans.mapHomologicalComplex_id,
      NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hq := Functor.exactSquare_fac
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm EC
  rw [Functor.square_symm_hom] at hq
  have hd : d = Functor.mapDerivedCategorySquareIso
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f) := by
    dsimp only [d]
    delta CondensedRing.derivedComapUpperStarIso Functor.mapDerivedCategorySquareIso
    rfl
  rw [← hd] at hq
  have hn := d.inv.naturality (scalarCounit a Y C)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  have hp' := congrArg RX.mapDerivedCategory.map hp
  simp only [Functor.map_comp] at hp'
  erw [reassoc_of% hp']
  simp only [Functor.map_comp, Category.assoc]
  erw [RX.mapDerivedCategoryFactors_hom_naturality p]
  dsimp only [scalarSixPull, restriction]
  slice_lhs 1 2 => exact hn.symm
  slice_lhs 2 4 => exact hq
  simp only [Category.assoc, Iso.symm_hom]
  rfl

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
