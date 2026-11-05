/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalTrivialization
public import WeilConjectures.WeilSheaf.CondensedTwistedConstant

/-! # Transport of a scalar Frobenius law with abstract coefficients -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory

/-- An inverse comparison square is equivalent to its forward comparison square. -/
lemma purity_isoSquareOfInverseSquare {C : Type*} [Category C]
    {A B A' B' : C} (a : A ≅ B) (b : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (h : v ≫ b.inv = a.inv ≫ u) :
    u ≫ b.hom = a.hom ≫ v := by
  apply (cancel_mono b.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, h,
    Iso.hom_inv_id_assoc]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance 20000] ProEtale.laxBraided_upperStar_of_weaklyEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))

/-- The underlying abelian-sheaf factorization of the geometric Frobenius pullback. -/
noncomputable def purityAbelianFrobeniusFactorIso :
    (a.geometricFiberProj)^*[Ab.{u + 1}] ⋙
        (a.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}] ≅
      (a.geometricFiberProj)^*[Ab.{u + 1}] :=
  (ProEtale.upperStarComp' Ab.{u + 1} a.geometricGaloisFrobenius.hom
    a.geometricFiberProj a.geometricFiberProj
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj.symm).symm

/-- Compare two successive module pullbacks with their underlying abelian pullbacks. -/
noncomputable def purityFrobeniusProjUnit
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (a.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}].map
      (CondensedRing.upperStarUnitHom Λ a.geometricFiberProj M) ≫
    CondensedRing.upperStarUnitHom Λ a.geometricGaloisFrobenius.hom
      ((a.geometricFiberProj)^*⟦Λ⟧.obj M)

/-- Forgetting coefficients carries the canonical Weil structure to the factorization map. -/
@[reassoc]
lemma purityFrobeniusProjUnit_structure
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    purityFrobeniusProjUnit Λ a M ≫
        ((CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app M).hom =
      (purityAbelianFrobeniusFactorIso a).hom.app M.X ≫
        CondensedRing.upperStarUnitHom Λ a.geometricFiberProj M := by
  have h := CondensedRing.upperStarForgetIso_hom_app_map_upperStarComp_symm_trans_inv_app
    Λ a.geometricFiberProj a.geometricGaloisFrobenius_hom_comp_geometricFiberProj M
  simp only [CondensedRing.upperStarForgetIso_hom_app, Mod.forget_map] at h
  rw [← cancel_mono ((CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).inv.app M).hom,
    Category.assoc, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom']
  erw [Category.comp_id]
  rw [CondensedRing.geometricFiberProjUpperStarFrobeniusIso, h]
  exact (Iso.hom_inv_id_app_assoc (purityAbelianFrobeniusFactorIso a) M.X _).symm

attribute [local instance 20000] ProEtale.laxBraided_upperStar_of_weaklyEtale

variable (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (e : ((a.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
    ((a.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj N)
  (c : ℤ)

/-- A scalar Frobenius relation descends from underlying sheaves to coefficient modules. -/
theorem purityExtendPullbackIso_weil
    (he : (a.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}].map e.hom.hom ≫
        (purityAbelianFrobeniusFactorIso a).hom.app N.X =
      c • ((purityAbelianFrobeniusFactorIso a).hom.app M.X ≫ e.hom.hom)) :
    c • ((CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app M ≫
        (purityExtendWeakPullbackIso Λ a.geometricFiberProj M N e).hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Λ⟧.map
          (purityExtendWeakPullbackIso Λ a.geometricFiberProj M N e).hom ≫
        (CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app N := by
  have : IsIso (purityFrobeniusProjUnit Λ a M) := by
    dsimp only [purityFrobeniusProjUnit]
    infer_instance
  have hunit : CondensedRing.upperStarUnitHom Λ a.geometricFiberProj M ≫
        (purityExtendWeakPullbackIso Λ a.geometricFiberProj M N e).hom.hom =
      e.hom.hom ≫ CondensedRing.upperStarUnitHom Λ a.geometricFiberProj N := by
    exact purityExtendWeakPullbackIso_unit Λ a.geometricFiberProj M N e
  have hstructureN := purityFrobeniusProjUnit_structure Λ a N
  dsimp only [purityFrobeniusProjUnit] at hstructureN
  rw [Category.assoc] at hstructureN
  refine Mod.hom_ext _ _ ?_
  rw [← cancel_epi (purityFrobeniusProjUnit Λ a M), Mod.zsmul_hom,
    Preadditive.comp_zsmul, Mod.comp_hom', Mod.comp_hom',
    purityFrobeniusProjUnit_structure_assoc,
    hunit, purityFrobeniusProjUnit, Category.assoc,
    CondensedRing.upperStarUnitHom_map_hom_assoc, ← Functor.map_comp_assoc,
    hunit, Functor.map_comp_assoc,
    hstructureN,
    ← Category.assoc ((a.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}].map e.hom.hom), he,
    Preadditive.zsmul_comp, Category.assoc]

end AlgebraicGeometry.ProEtale
