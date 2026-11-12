/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.ProjectionMap
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale
import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom

/-!
# The derived projection formula along a weakly étale morphism

Let `Λ` be a commutative condensed ring and `g : W ⟶ X` a weakly étale morphism. This file
shows that the derived extension by zero `Dg_!` (the exact extension by zero
`ProEtale.CondensedRing.weaklyEtaleLowerShriek` applied levelwise) is left adjoint to the
derived pullback `Lg^*` on derived categories of module objects over `Λ`, and that this
adjunction satisfies the projection formula: the projection map
`Dg_!(Lg^* M ⊗ᴸ T) ⟶ M ⊗ᴸ Dg_! T` is an isomorphism.

## The argument

* On module objects, `g^*` commutes with internal homs: it is the transport `mapMod(g^*)` of
  module objects along the pullback of sheaves, which commutes with internal homs
  (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`,
  `CategoryTheory.Mod.isIso_ihomComparison_mapMod`), followed by an extension of scalars along
  an isomorphism. Hence the projection maps of `g_! ⊣ g^*` are isomorphisms.
* On cochain complexes the projection maps are then isomorphisms degreewise
  (`CategoryTheory.Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex`).
* On a K-flat complex `K` (whose pullback `g^* K` is again K-flat), the derived projection
  map is the image of the projection map on cochain complexes, up to the tensor comparison
  maps of `Qh`, which are isomorphisms on K-flat complexes.

## Main results

- `ProEtale.CondensedRing.derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction`:
  the adjunction `Dg_! ⊣ Lg^*`.
- `ProEtale.CondensedRing.isIso_projectionMap_derivedWeaklyEtaleLowerShriek`: the derived
  projection formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {W X : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]

/-! ### The underived projection formula -/

/-- The pullback of module objects along a weakly étale morphism commutes with internal homs:
the comparison `g^* Hom_{Λ_X}(M, N) ⟶ Hom_{Λ_W}(g^* M, g^* N)` is an isomorphism. -/
instance isIso_ihomComparison_upperStar_of_weaklyEtale
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (Functor.LaxMonoidal.ihomComparison (g)^*⟦Λ⟧ M) := by
  have (Z : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      IsIso (Functor.LaxMonoidal.ihomComparison (g)^*[Ab.{u + 1}] Z) :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} g Z
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  erw [Functor.LaxMonoidal.ihomComparison_comp_app ((g)^*[Ab.{u + 1}].mapMod _)
    (Mod.extendScalars (condensedPullbackHom Λ g))]
  infer_instance

/-- The projection map `g_!(g^* M ⊗ T) ⟶ M ⊗ g_! T` of the adjunction `g_! ⊣ g^*` on module
objects along a weakly étale morphism is an isomorphism. -/
instance isIso_projectionMap_weaklyEtaleLowerShriekUpperStarAdjunction
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (Functor.Monoidal.projectionMap (weaklyEtaleLowerShriekUpperStarAdjunction Λ g) M) :=
  Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison _ M

/-! ### The derived adjunction -/

/-- The derived adjunction `Dg_! ⊣ Lg^*` along a weakly étale morphism `g`, with the right
adjoint the left derived functor `Lg^*` (isomorphic to the levelwise `D(g^*)`, `g^*` being
exact): the localization of the adjunction `g_! ⊣ g^*` on homotopy categories. -/
noncomputable def derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction :
    (weaklyEtaleLowerShriek Λ g).mapDerivedCategory ⊣ L((g)^*⟦Λ⟧) :=
  let _ : CatCommSq ((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh (weaklyEtaleLowerShriek Λ g).mapDerivedCategory :=
    ⟨(weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.symm⟩
  let _ : CatCommSq (((g)^*⟦Λ⟧).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh L((g)^*⟦Λ⟧) :=
    ⟨(asIso ((g)^*⟦Λ⟧).leftDerivedFunctorCounit).symm⟩
  ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomotopyCategory
    (.up ℤ)).localization DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ _

/-! ### The derived projection formula -/

/-- The pullback of module objects preserves the coproducts defining the tensor product of
cochain complexes, being a left adjoint. -/
instance preservesColimitsOfShape_upperStar_discrete_π (j : ℤ) :
    PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) (g)^*⟦Λ⟧ :=
  inferInstance

/-- The extension by zero of module objects preserves the coproducts defining the tensor
product of cochain complexes, being a left adjoint. -/
instance preservesColimitsOfShape_weaklyEtaleLowerShriek_discrete_π (j : ℤ) :
    PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) (weaklyEtaleLowerShriek Λ g) :=
  have : PreservesColimitsOfSize.{0, 0} (weaklyEtaleLowerShriek Λ g) :=
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ g).leftAdjoint_preservesColimits
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology X) Ab) _`
/-- The pullback of module objects is monoidal on cochain complexes. -/
noncomputable instance monoidal_upperStar_mapHomologicalComplex :
    ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)).Monoidal :=
  Functor.mapCochainComplexMonoidal _

set_option maxHeartbeats 3200000 in
-- the chase unfolds the derived unit, counit and tensor comparison on complexes of module objects
open HomotopyCategory DerivedCategory in
/-- On objects coming from cochain complexes, the derived projection map of `Dg_! ⊣ Lg^*` is
the image of the projection map on cochain complexes, up to the tensor comparison maps of
`Qh`. -/
lemma projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh
    (K₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (T₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) ℤ) :
    (Functor.Monoidal.projectionMap (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction
        Λ g) (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁)) ≫
      (Qh.obj ((quotient _ _).obj K₁) ◁
        (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app
          ((quotient _ _).obj T₁)) ≫
      Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
    (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map
        (((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ▷
          Qh.obj ((quotient _ _).obj T₁)) ≫
          Functor.LaxMonoidal.μ Qh _ ((quotient _ _).obj T₁)) ≫
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app _ ≫
        Qh.map ((quotient _ _).map ((Functor.Monoidal.projectionMap
          ((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomologicalComplex
            (.up ℤ)) K₁).app T₁)) := by
  simp only [Functor.Monoidal.projectionMap, Category.assoc]
  have hn := ((derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g).counit.naturality
    (Qh.obj ((quotient _ _).obj K₁) ◁
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app
        ((quotient _ _).obj T₁) ≫
      Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)))).symm
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction]
  erw [Adjunction.localization_counit_app, Adjunction.localization_unit_app]
  dsimp only [CatCommSq.iso, Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  conv_rhs => rw [Functor.map_comp, Functor.map_comp, ← Functor.mapHomotopyCategory_map]
  conv_rhs => simp only [Functor.map_comp, Category.assoc]
  have hφ : ∀ {Y Y' : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) (.up ℤ)} (f : Y ⟶ Y'),
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app Y ≫
        Qh.map (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).map f) =
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map (Qh.map f) ≫
        (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app Y' :=
    fun f ↦ ((weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.naturality f).symm
  rw [reassoc_of% hφ, reassoc_of% hφ]
  simp only [← Functor.map_comp_assoc, Category.assoc]
  congr 2
  have key : Functor.LaxMonoidal.μ L((g)^*⟦Λ⟧) (Qh.obj ((quotient _ _).obj K₁))
        (Qh.obj (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁))) ≫
      L((g)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁))) ≫
      (g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((quotient _ _).obj K₁ ⊗
        ((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
      ((g)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ⊗ₘ
        (g)^*⟦Λ⟧.leftDerivedFunctorCounit.app
          (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
            ((quotient _ _).obj T₁))) ≫
      Functor.LaxMonoidal.μ Qh (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj K₁))
        (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
          (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
            ((quotient _ _).obj T₁))) ≫
      Qh.map ((quotient _ _).map (Functor.LaxMonoidal.μ ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ))
        K₁ (((weaklyEtaleLowerShriek Λ g).mapHomologicalComplex (.up ℤ)).obj T₁))) := by
    have h := leftDerivedUpperStarTensor_laxSquare Λ g ((quotient _ _).obj K₁)
      (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
        ((quotient _ _).obj T₁))
    rw [← cancel_epi (Functor.OplaxMonoidal.δ L((g)^*⟦Λ⟧) _ _), Functor.Monoidal.δ_μ_assoc]
    erw [reassoc_of% h]
    rw [← Functor.map_comp DerivedCategory.Qh]
    have hδ : Functor.OplaxMonoidal.δ ((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ))
        ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) ≫
        (quotient _ _).map (Functor.LaxMonoidal.μ ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ)) K₁
          (((weaklyEtaleLowerShriek Λ g).mapHomologicalComplex (.up ℤ)).obj T₁)) =
        𝟙 _ := by
      change (quotient _ _).map (Functor.OplaxMonoidal.δ
        ((g)^*⟦Λ⟧.mapHomologicalComplex (.up ℤ))
        K₁ (((weaklyEtaleLowerShriek Λ g).mapHomologicalComplex (.up ℤ)).obj T₁)) ≫
        _ = _
      rw [← Functor.map_comp, Functor.Monoidal.δ_μ]
      exact CategoryTheory.Functor.map_id _ _
    erw [hδ, CategoryTheory.Functor.map_id]
    rw [Category.comp_id]
  have hφ' : (Qh.obj ((quotient _ _).obj K₁) ◁
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.inv.app
        ((quotient _ _).obj T₁)) ≫ (Qh.obj ((quotient _ _).obj K₁) ◁
      (weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.hom.app
        ((quotient _ _).obj T₁)) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app, MonoidalCategory.whiskerLeft_id]
  simp only [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  have hμ := Functor.LaxMonoidal.μ_natural_right L((g)^*⟦Λ⟧) (Qh.obj ((quotient _ _).obj K₁))
    ((weaklyEtaleLowerShriek Λ g).mapDerivedCategoryFactorsh.inv.app
      ((quotient _ _).obj T₁))
  rw [reassoc_of% hμ]
  rw [← Functor.map_comp_assoc L((g)^*⟦Λ⟧), hφ']
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  rw [key, MonoidalCategory.tensorHom_def, Category.assoc]
  erw [whisker_exchange_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    NatIso.isIso_inv_app, IsIso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    whisker_exchange_assoc]
  congr 1
  have hq := Functor.LaxMonoidal.μ_natural_right Qh
    (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K₁))
    ((quotient _ _).map (((weaklyEtaleLowerShriekUpperStarAdjunction Λ g).mapHomologicalComplex
      (.up ℤ)).unit.app T₁))
  erw [reassoc_of% hq]
  erw [← HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft']
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the K-flat derivability structure on complexes of module objects is found by instance search
/-- The lax monoidal structure `Qh K ⊗ᴸ Qh M ⟶ Qh (K ⊗ M)` of `Qh` on complexes of module
objects over `Λ_Z` is an isomorphism when `K` is K-flat. The case of a K-flat `M` is
`CategoryTheory.Functor.isIso_μNatTrans_Qh_app_app_of_kFlat`. -/
lemma isIso_μ_Qh_of_kFlat_left {Z : Scheme.{u}}
    (K M : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) (.up ℤ))
    (hK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat K) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh K M) := by
  have := isLeftDerivabilityStructure_localizerMorphismKFlat Λ Z
  have := DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
  exact (MorphismProperty.kFlat_prod_id_derives_curriedTensor
    (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh).isIso_of_isLeftDerivabilityStructure
      (LF := curriedTensor (DerivedCategory _)) (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      ⟨K, hK⟩ M

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
open HomotopyCategory DerivedCategory in
/-- The derived projection map of `Dg_! ⊣ Lg^*` is an isomorphism at `M = Qh K₁` for a K-flat
complex `K₁`: it is then the image of the projection map on cochain complexes, which is an
isomorphism degreewise, up to the tensor comparison maps of `Qh`, which are isomorphisms since
`K₁` and `g^* K₁` are K-flat. -/
lemma isIso_projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh
    (K₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (hK₁ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K₁)
    (T₁ : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W)) ℤ) :
    IsIso ((Functor.Monoidal.projectionMap
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g)
        (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁))) := by
  have h := projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh Λ g K₁ T₁
  have := isIso_μ_Qh_of_kFlat_left Λ ((quotient _ _).obj K₁)
    (((weaklyEtaleLowerShriek Λ g).mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj T₁))
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hK₁)
  have := isIso_μ_Qh_of_kFlat_left Λ
    (((g)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K₁))
    ((quotient _ _).obj T₁) (kFlat_upperStar_mapHomotopyCategory_obj Λ g hK₁)
  have := Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex (g)^*⟦Λ⟧
    (weaklyEtaleLowerShriekUpperStarAdjunction Λ g) K₁
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- **The derived projection formula along a weakly étale morphism**: the projection map
`Dg_!(Lg^* M ⊗ᴸ T) ⟶ M ⊗ᴸ Dg_! T` of the adjunction `Dg_! ⊣ Lg^*` is an isomorphism. -/
instance isIso_projectionMap_derivedWeaklyEtaleLowerShriek
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (Functor.Monoidal.projectionMap
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M) := by
  obtain ⟨P, hP, ⟨eM⟩⟩ := exists_kFlat_iso_Qh_obj Λ M
  obtain ⟨K₁, rfl⟩ := P.quotient_obj_surjective
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  let T₀ := DerivedCategory.Q.objPreimage T
  let eT : T ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀) :=
    (DerivedCategory.Q.objObjPreimageIso T).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app T₀
  have := isIso_projectionMap_derivedWeaklyEtaleLowerShriek_app_Qh Λ g K₁
    ((HomotopyCategory.kFlat_quotient_obj_iff _).1 hP) T₀
  have := Functor.Monoidal.isIso_projectionMap_app_of_iso
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) eM.symm
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀))
  have hn := (Functor.Monoidal.projectionMap
    (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M).naturality eT.hom
  have : IsIso ((Functor.Monoidal.projectionMap
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ g) M).app T ≫
      M ◁ (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map eT.hom) := by
    erw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (M ◁ (weaklyEtaleLowerShriek Λ g).mapDerivedCategory.map eT.hom)

end AlgebraicGeometry.ProEtale.CondensedRing
