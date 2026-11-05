/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalTrivialization
public import WeilConjectures.WeilSheaf.SmoothPurityScalarSquare
public import WeilConjectures.WeilSheaf.SmoothPurityPullbackForgetFactor

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

/-- The isomorphism of underlying objects of a module isomorphism. -/
noncomputable def purity_underlyingModuleIso {C : Type*} [Category C] [MonoidalCategory C]
    {R : C} [MonObj R] {M N : Mod C R} (e : M ≅ N) : M.X ≅ N.X :=
  (Mod.forget R).mapIso e

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X U : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)

/-- The underlying abelian-sheaf factorization of the geometric Frobenius pullback. -/
noncomputable def purityAbelianFactorIso :
    (p)^*[Ab.{u + 1}] ⋙
        (s)^*[Ab.{u + 1}] ≅
      (p)^*[Ab.{u + 1}] :=
  (ProEtale.upperStarComp' Ab.{u + 1} s
    p p
    hs.symm).symm

/-- The module pullback factorization attached to s ≫ p = p. -/
noncomputable def purityModuleFactorIso :
    (p)^*⟦Λ⟧ ⋙ (s)^*⟦Λ⟧ ≅ (p)^*⟦Λ⟧ :=
  (CondensedRing.upperStarComp Λ s p).symm ≪≫ CondensedRing.upperStarCongr Λ hs

/-- Compare two successive module pullbacks with their underlying abelian pullbacks. -/
noncomputable def purityFactorUnit
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    ((p)^*[Ab.{u + 1}] ⋙ (s)^*[Ab.{u + 1}]).obj M.X ⟶
      (((p)^*⟦Λ⟧ ⋙ (s)^*⟦Λ⟧).obj M).X :=
  (s)^*[Ab.{u + 1}].map
      (CondensedRing.upperStarUnitHom Λ p M) ≫
    CondensedRing.upperStarUnitHom Λ s
      ((p)^*⟦Λ⟧.obj M)

/-- Forgetting coefficients carries the canonical Weil structure to the factorization map. -/
@[reassoc]
lemma purityFactorUnit_structure
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    purityFactorUnit Λ p s M ≫
        ((purityModuleFactorIso Λ p s hs).hom.app M).hom =
      (purityAbelianFactorIso p s hs).hom.app M.X ≫
        CondensedRing.upperStarUnitHom Λ p M := by
  have h := CondensedRing.purity_upperStarForgetIso_factor_hom Λ p s hs M
  simpa only [purityFactorUnit, purityModuleFactorIso, purityAbelianFactorIso,
    CondensedRing.upperStarForgetIso_hom_app, Mod.forget_map] using h



variable (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (e : ((p)^*[Ab.{u + 1}].mapMod _).obj M ≅
    ((p)^*[Ab.{u + 1}].mapMod _).obj N)
  (c : ℤ)

/-- A scalar Frobenius relation descends from underlying sheaves to coefficient modules. -/
theorem purityExtendPullbackIso_factor
    (he : (s)^*[Ab.{u + 1}].map e.hom.hom ≫
        (purityAbelianFactorIso p s hs).hom.app N.X =
      c • ((purityAbelianFactorIso p s hs).hom.app M.X ≫ e.hom.hom)) :
    c • ((purityModuleFactorIso Λ p s hs).hom.app M ≫
        (purityExtendPullbackIso Λ p M N e).hom) =
      (s)^*⟦Λ⟧.map
          (purityExtendPullbackIso Λ p M N e).hom ≫
        (purityModuleFactorIso Λ p s hs).hom.app N := by
  have : IsIso (purityFactorUnit Λ p s M) := by
    dsimp only [purityFactorUnit]
    infer_instance
  have hunit : CondensedRing.upperStarUnitHom Λ p M ≫
        (purityExtendPullbackIso Λ p M N e).hom.hom =
      e.hom.hom ≫ CondensedRing.upperStarUnitHom Λ p N := by
    exact purityExtendPullbackIso_unit Λ p M N e
  have hf : purityFactorUnit Λ p s M ≫
        ((s)^*⟦Λ⟧.map (purityExtendPullbackIso Λ p M N e).hom).hom =
      (s)^*[Ab.{u + 1}].map e.hom.hom ≫ purityFactorUnit Λ p s N := by
    dsimp only [purityFactorUnit]
    rw [Category.assoc, CondensedRing.upperStarUnitHom_map_hom_assoc,
      ← Functor.map_comp_assoc, hunit, Functor.map_comp, Category.assoc]
  refine Mod.hom_ext _ _ ?_
  simpa only [Mod.zsmul_hom, Mod.comp_hom'] using
    purity_scalarSquare
      (purityFactorUnit Λ p s M) (purityFactorUnit Λ p s N)
      (CondensedRing.upperStarUnitHom Λ p M) (CondensedRing.upperStarUnitHom Λ p N)
      ((purityAbelianFactorIso p s hs).hom.app M.X)
      ((purityAbelianFactorIso p s hs).hom.app N.X)
      (((purityModuleFactorIso Λ p s hs).hom.app M).hom)
      (((purityModuleFactorIso Λ p s hs).hom.app N).hom)
      e.hom.hom (purityExtendPullbackIso Λ p M N e).hom.hom
      ((s)^*[Ab.{u + 1}].map e.hom.hom)
      (((s)^*⟦Λ⟧.map (purityExtendPullbackIso Λ p M N e).hom).hom) c
      (purityFactorUnit_structure Λ p s hs M) (purityFactorUnit_structure Λ p s hs N)
      hunit hf he


section FiniteBase

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k))

/-- The abelian factorization attached to the geometric Frobenius. -/
noncomputable def purityAbelianFrobeniusFactorIso :
    (a.geometricFiberProj)^*[Ab.{u + 1}] ⋙
        (a.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}] ≅
      (a.geometricFiberProj)^*[Ab.{u + 1}] :=
  purityAbelianFactorIso a.geometricFiberProj a.geometricGaloisFrobenius.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj

variable (M₀ N₀ : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
  (e₀ : ((a.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M₀ ≅
    ((a.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj N₀) (c₀ : ℤ)

/-- A scalar Frobenius relation descends from underlying sheaves to coefficient modules. -/
theorem purityExtendPullbackIso_weil
    (he : (a.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}].map e₀.hom.hom ≫
        (purityAbelianFrobeniusFactorIso a).hom.app N₀.X =
      c₀ • ((purityAbelianFrobeniusFactorIso a).hom.app M₀.X ≫ e₀.hom.hom)) :
    c₀ • ((CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app M₀ ≫
        (purityExtendPullbackIso Λ a.geometricFiberProj M₀ N₀ e₀).hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Λ⟧.map
          (purityExtendPullbackIso Λ a.geometricFiberProj M₀ N₀ e₀).hom ≫
        (CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app N₀ := by
  exact purityExtendPullbackIso_factor Λ a.geometricFiberProj
    a.geometricGaloisFrobenius.hom a.geometricGaloisFrobenius_hom_comp_geometricFiberProj
    M₀ N₀ e₀ c₀ he

end FiniteBase

end AlgebraicGeometry.ProEtale
