/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Hypercohomology of complexes of étale sheaves and its pullback maps

For a scheme `Y` and a complex `K` of abelian étale sheaves on `Y`, the hypercohomology
`Hⁿ(Y, K)` is the group `Hom(ℤ_Y, K[n])` of morphisms in the derived category
(`AlgebraicGeometry.Etale.hyperH`), and a morphism `f : X ⟶ Y` induces the pullback map
`Hⁿ(Y, K) ⟶ Hⁿ(X, f^* K)` (`AlgebraicGeometry.Etale.hyperHPullback`). For a sheaf `F` placed in
degree `0` these are the sheaf cohomology `Hⁿ(Y, F)` and its pullback map
`AlgebraicGeometry.Etale.cohomologyMap` (`AlgebraicGeometry.Etale.hyperHPullback_homEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The constant sheaf `ℤ_Y`. -/
noncomputable abbrev unitSheaf (Y : Scheme.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The hypercohomology `Hⁿ(Y, K) = Hom(ℤ_Y, K[n])` of a complex of abelian étale sheaves. -/
abbrev hyperH {Y : Scheme.{u}}
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ) : Type (u + 1) :=
  ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf Y)) K n

/-- The pullback of the constant sheaf `ℤ_Y` is the constant sheaf `ℤ_X`, in the derived
category. -/
noncomputable def unitSheafSingleIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor _ 0).obj (unitSheaf X) ≅
      ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf Y)) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app _) ≪≫
    (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategorySingleFunctor 0).app _).symm

/-- The pullback map `Hⁿ(Y, K) ⟶ Hⁿ(X, f^* K)` on hypercohomology. -/
noncomputable def hyperHPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) :
    hyperH K n →+ hyperH (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory).obj K) n where
  toFun φ := (ShiftedHom.mk₀ 0 rfl (unitSheafSingleIso f).hom).comp
    (φ.map (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory) (zero_add n)
  map_zero' := by simp [ShiftedHom.map_zero]
  map_add' a b := by simp [ShiftedHom.map_add, ShiftedHom.comp_add]

/-- For a sheaf placed in degree `0`, the pullback map on hypercohomology is the pullback map
`AlgebraicGeometry.Etale.cohomologyMap` on sheaf cohomology. -/
lemma hyperHPullback_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (e : Sheaf.H F n) :
    Abelian.Ext.homEquiv (cohomologyMap f F n e) =
      (hyperHPullback f ((DerivedCategory.singleFunctor _ 0).obj F) n
        (Abelian.Ext.homEquiv e)).comp (ShiftedHom.mk₀ 0 rfl
          (((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategorySingleFunctor 0).hom.app F))
          (add_zero _) := by
  rw [cohomologyMap_apply]
  change (Abelian.Ext.comp _ _ _).hom = _
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, Abelian.Ext.mapExactFunctor_hom]
  simp only [hyperHPullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk, unitSheafSingleIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom]
  rw [ShiftedHom.comp_assoc _ _ _ (zero_add _) (add_zero _) (by simp),
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp]
  simp [Category.assoc]

end AlgebraicGeometry.Etale
