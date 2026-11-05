/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalTrivialization
public import WeilConjectures.WeilSheaf.SmoothPurityScalarFactorSquare
public import WeilConjectures.WeilSheaf.SmoothPurityPullbackForgetFactor
import WeilConjectures.Tactic.ExactModProofs

/-! # Transport of a scalar Frobenius law with abstract coefficients -/

@[expose] public section

universe u

set_option Elab.async false
set_option trace.profiler true
set_option trace.profiler.threshold 1000

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

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
  apply purity_scalarFactorSquare (Mod.forget (condensedRingObj Λ U))
    (s)^*⟦Λ⟧ (s)^*[Ab.{u + 1}] (CondensedRing.upperStarForgetIso Λ s)
    ((CondensedRing.upperStarForgetIso Λ p).app M)
    ((CondensedRing.upperStarForgetIso Λ p).app N)
    ((purityAbelianFactorIso p s hs).hom.app M.X)
    ((purityAbelianFactorIso p s hs).hom.app N.X)
    ((purityModuleFactorIso Λ p s hs).hom.app M)
    ((purityModuleFactorIso Λ p s hs).hom.app N)
    e.hom.hom (purityExtendPullbackIso Λ p M N e).hom c
  · have h := CondensedRing.purity_upperStarForgetIso_factor_hom Λ p s hs M
    simp only [Iso.app_hom, Category.assoc, purityModuleFactorIso, purityAbelianFactorIso] at h ⊢
    exact_mod_proofs h
  · have h := CondensedRing.purity_upperStarForgetIso_factor_hom Λ p s hs N
    simp only [Iso.app_hom, Category.assoc, purityModuleFactorIso, purityAbelianFactorIso] at h ⊢
    exact_mod_proofs h
  · have h := purityExtendPullbackIso_unit Λ p M N e
    simp only [Iso.app_hom, CondensedRing.upperStarForgetIso_hom_app,
      Mod.forget, purityPullbackUnit] at h ⊢
    exact_mod_proofs h
  · exact he



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
  have h := purityExtendPullbackIso_factor Λ a.geometricFiberProj
    a.geometricGaloisFrobenius.hom a.geometricGaloisFrobenius_hom_comp_geometricFiberProj
    M₀ N₀ e₀ c₀ he
  simp only [CondensedRing.geometricFiberProjUpperStarFrobeniusIso,
    purityModuleFactorIso, purityAbelianFrobeniusFactorIso] at h ⊢
  exact_mod_proofs h

end FiniteBase

end AlgebraicGeometry.ProEtale
