/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarWeilLaw
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCoherence

/-! # Changing coefficients in a scalar Frobenius relation -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

section Transport

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The (Pull) isomorphisms are compatible with the transport of pullbacks along an equation of
morphisms of schemes. -/
lemma purity_pullIso_hom_app_comp_upperStarCongr_hom_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (pullIso a f).hom.app M ≫
        (upperStarCongr Λ' h).hom.app ((Mod.extendScalars (coefficientMap a Y)).obj M) =
      (Mod.extendScalars (coefficientMap a X)).map ((upperStarCongr Λ h).hom.app M) ≫
        (pullIso a g).hom.app M := by
  subst h
  simp [upperStarCongr]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- **The Weil structures of pulled-back module objects are compatible with the extension of
scalars** along a change of coefficients `a : Λ ⟶ Λ'`: through the (Pull) isomorphisms
`Ext (p^* M) ≅ p^* (Ext M)` and `Ext (Fr^* N) ≅ Fr^* (Ext N)`, the extension of scalars of the
Weil structure `Fr^* p^* M ≅ p^* M` is the Weil structure of `p^* (Ext M)`. -/
lemma purity_extendScalars_map_geometricFiberProjUpperStarFrobeniusIso_hom_app_comp_pullIso_hom_app
    (M : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    (Mod.extendScalars (coefficientMap a f.geometricFiber)).map
          ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M) ≫
        (pullIso a f.geometricFiberProj).hom.app M =
      (pullIso a f.geometricGaloisFrobenius.hom).hom.app ((f.geometricFiberProj)^*⟦Λ⟧.obj M) ≫
        (f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧.map ((pullIso a f.geometricFiberProj).hom.app M) ≫
          (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
            ((Mod.extendScalars (coefficientMap a X₀)).obj M) := by
  have key : (Mod.extendScalars (coefficientMap a f.geometricFiber)).map
        ((upperStarComp Λ f.geometricGaloisFrobenius.hom f.geometricFiberProj).inv.app M) ≫
        (pullIso a (f.geometricGaloisFrobenius.hom ≫ f.geometricFiberProj)).hom.app M =
      (pullIso a f.geometricGaloisFrobenius.hom).hom.app ((f.geometricFiberProj)^*⟦Λ⟧.obj M) ≫
        (f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧.map ((pullIso a f.geometricFiberProj).hom.app M) ≫
          (upperStarComp Λ' f.geometricGaloisFrobenius.hom f.geometricFiberProj).inv.app
            ((Mod.extendScalars (coefficientMap a X₀)).obj M) := by
    rw [← cancel_mono ((upperStarComp Λ' f.geometricGaloisFrobenius.hom
      f.geometricFiberProj).hom.app ((Mod.extendScalars (coefficientMap a X₀)).obj M))]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_app, Category.comp_id, pullIso_hom_app_comp, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [geometricFiberProjUpperStarFrobeniusIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← purity_pullIso_hom_app_comp_upperStarCongr_hom_app a
    f.geometricGaloisFrobenius_hom_comp_geometricFiberProj M, reassoc_of% key]

/-- The Weil structure of `p^* (Ext M)`, expressed through the Weil structure of `p^* M` and
the (Pull) isomorphisms. -/
lemma purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_extendScalars_obj
    (M : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
        ((Mod.extendScalars (coefficientMap a X₀)).obj M) =
      (f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧.map ((pullIso a f.geometricFiberProj).inv.app M) ≫
        (pullIso a f.geometricGaloisFrobenius.hom).inv.app ((f.geometricFiberProj)^*⟦Λ⟧.obj M) ≫
          (Mod.extendScalars (coefficientMap a f.geometricFiber)).map
            ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M) ≫
          (pullIso a f.geometricFiberProj).hom.app M := by
  rw [purity_extendScalars_map_geometricFiberProjUpperStarFrobeniusIso_hom_app_comp_pullIso_hom_app,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Transport

section ScalarRelation

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))


variable (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (e : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
    ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj N)
  (c : ℤ)

/-- Changing coefficients preserves the scalar relation of an underlying trivialization. -/
theorem purityChangeCoefficientPullbackIso_weil
    (he : (f.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}].map e.hom.hom ≫
        (purityAbelianFrobeniusFactorIso f).hom.app N.X =
      c • ((purityAbelianFrobeniusFactorIso f).hom.app M.X ≫ e.hom.hom)) :
    c • ((geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
          ((Mod.extendScalars (coefficientMap a X)).obj M) ≫
        (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M N e).hom) =
      (f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧.map
          (purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M N e).hom ≫
        (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
          ((Mod.extendScalars (coefficientMap a X)).obj N) := by
  have hW := purityExtendPullbackIso_weil Λ f M N e c he
  have hnat := (pullIso a f.geometricGaloisFrobenius.hom).inv.naturality
    (purityExtendPullbackIso Λ f.geometricFiberProj M N e).hom
  simp only [Functor.comp_map] at hnat
  simp only [purityChangeCoefficientPullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_extendScalars_obj,
    purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_extendScalars_obj,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc
      ((f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧)
      ((pullIso a f.geometricFiberProj).hom.app N),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_comp_assoc
      (Mod.extendScalars (coefficientMap a f.geometricFiber)),
    ← Preadditive.comp_zsmul, ← Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    ← Functor.map_zsmul, hW, Functor.map_comp, Category.assoc, ← reassoc_of% hnat]

/-- The normalized trivialization obeys the same scalar Frobenius law. -/
theorem purityChangeCoefficientTrivialization_weil
    (e₁ : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _))
    (he : (f.geometricGaloisFrobenius.hom)^*[Ab.{u + 1}].map e₁.hom.hom ≫
        (purityAbelianFrobeniusFactorIso f).hom.app (condensedRingObj Λ X) =
      c • ((purityAbelianFrobeniusFactorIso f).hom.app M.X ≫ e₁.hom.hom)) :
    c • ((geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
          ((Mod.extendScalars (coefficientMap a X)).obj M) ≫
        (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁).hom) =
      (f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧.map
          (purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁).hom ≫
        (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app (𝟙_ _) := by
  letI := Mod.extendScalarsMonoidal (coefficientMap a X)
  let ε := (Functor.Monoidal.εIso (Mod.extendScalars (coefficientMap a X))).inv
  have h := purityChangeCoefficientPullbackIso_weil a f M (𝟙_ _) e₁ c he
  have hnat := (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.naturality ε
  simp only [Functor.comp_map] at hnat
  simp only [purityChangeCoefficientTrivialization, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← Preadditive.zsmul_comp, h, Category.assoc, ← hnat]

end ScalarRelation

end AlgebraicGeometry.ProEtale.CondensedRing
