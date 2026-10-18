/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalization
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit

/-!
# The rationalization formula for `ℤ_ℓ,X`
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- The naturality of the unit `M ⟶ S ⊗_R M`, `m ↦ 1 ⊗ m`. -/
@[reassoc]
lemma extendUnitHom_extendScalarsMap {M N : Mod C R} (f : M ⟶ N) :
    extendUnitHom φ M ≫ (extendScalarsMap φ f).hom = f.hom ≫ extendUnitHom φ N := by
  simp only [extendUnitHom, Category.assoc, extendπ_extendScalarsMap]
  rw [← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

end CategoryTheory.Mod

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [HasWeakSheafify J A] {K : Type*} [Category* K]

/-- A cocone `c` of sheaves is a colimit cocone if there is a colimit cocone `E` of the
underlying presheaves and a morphism `E.pt ⟶ c.pt` of presheaves compatible with the cocone
maps which becomes an isomorphism after sheafification. -/
noncomputable def isColimitOfW {F : K ⥤ Sheaf J A} (c : Cocone F)
    (E : Cocone (F ⋙ sheafToPresheaf J A)) (hE : IsColimit E) (ψ : E.pt ⟶ c.pt.obj)
    (hψ : ∀ k, E.ι.app k ≫ ψ = (c.ι.app k).hom) (hW : J.W ψ) : IsColimit c :=
  have : IsIso (((sheafificationAdjunction J A).homEquiv _ c.pt).symm ψ) := by
    rw [GrothendieckTopology.W_iff] at hW
    rw [Adjunction.homEquiv_counit]
    infer_instance
  IsColimit.ofIsoColimit (isColimitSheafifyCocone E hE)
    (Cocone.ext (asIso (((sheafificationAdjunction J A).homEquiv _ c.pt).symm ψ)) fun k ↦ by
      refine ObjectProperty.hom_ext _ ?_
      rw [ObjectProperty.FullSubcategory.comp_hom, sheafifyCocone_ι_app_val_assoc, asIso_hom]
      erw [toSheafify_sheafifyLift J ψ c.pt.property]
      exact hψ k)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

lemma adicSheafExtendScalarsUnitAb_regular_comp :
    adicSheafExtendScalarsUnitAb l X (Mod.regular (padicIntAbSheaf X l)) ≫
      (AdicSheaf.toAb l X).map (adicSheafExtendScalarsRegularIso l X).hom =
      padicIntSheafToAdicConstantSheaf X l := by
  have h : (Mod.extendHomEquiv (freePadicIntSheafToAdicConstantSheaf X l)
      (((weilCoefficientsFree X l).mapMod (padicIntAbSheaf X l)).obj
        (Mod.regular (padicIntAbSheaf X l))) (AdicSheaf.unit l X)
      (Mod.extendScalarsMap (freePadicIntSheafToAdicConstantSheaf X l)
        ((weilCoefficientsFree X l).mapModRegularIso (padicIntAbSheaf X l)).hom ≫
        Mod.extendHom (freePadicIntSheafToAdicConstantSheaf X l)
          (Mod.regularHomComap (freePadicIntSheafToAdicConstantSheaf X l)))).hom =
      freePadicIntSheafToAdicConstantSheaf X l := by
    rw [Mod.extendHomEquiv_apply, Mod.comp_hom', Mod.comap_map_hom, Mod.extendUnit_hom,
      Mod.comp_hom', Mod.extendUnitHom_extendScalarsMap_assoc, Mod.extendUnitHom_extendHom]
    erw [Category.id_comp]
    rfl
  have key : ((adicSheafExtendScalarsRestrictAdjunction X l).homEquiv _ _
      (adicSheafExtendScalarsRegularIso l X).hom).hom = padicIntSheafToAdicConstantSheaf X l := by
    rw [adicSheafExtendScalarsRestrictAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    dsimp [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv, Mod.extendHomEquiv,
      Adjunction.mapModAdjunction, adicSheafExtendScalarsRegularIso,
      Mod.extendScalarsObjRegularIso, comapMapModComapIsoRestrictPadicInt]
    simp only [Adjunction.mk'_homEquiv]
    simp only [Mod.extendScalars_map, Equiv.coe_fn_mk, Mod.Hom.mk'_hom, Mod.id_hom',
      Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom, Mod.comapComp_inv_app_hom,
      Category.id_comp]
    erw [h, Equiv.apply_symm_apply, Category.comp_id]
  exact (congrArg Mod.Hom.hom ((adicSheafExtendScalarsRestrictAdjunction X l).homEquiv_unit _ _
    (adicSheafExtendScalarsRegularIso l X).hom)).symm.trans key

end AlgebraicGeometry.ProEtale
