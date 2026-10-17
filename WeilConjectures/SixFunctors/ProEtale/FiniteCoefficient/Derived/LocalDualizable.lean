/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor
public import WeilConjectures.Algebra.Homology.Monoidal.ProjectionMap
public import WeilConjectures.CategoryTheory.Functor.KanExtension.ProjectionFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-!
# Dualizability is local on the pro-étale site

This is the pro-étale counterpart of the section `Projection` of
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`.

For a weakly étale morphism `f : U ⟶ X`, the lower shriek `f_!` along the localization functor
`U_proét ⥤ X_proét` is exact, so it induces a left adjoint `D(f_!)` of the derived pullback `Lf^*`.
The projection formula for `f_! ⊣ f^*` holds for sheaves, `f^*` commuting with internal homs
(`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`), hence for complexes. It follows
that `Lf^*` commutes with the comparison `RHom(K, Λ) ⊗ᴸ K ⟶ RHom(K, K)` whenever `Lf^* K` is
dualizable; as derived pullbacks along a pro-étale cover jointly reflect isomorphisms, an object
which is dualizable on the members of a cover is dualizable.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_projectionMap_derivedLocalizationLowerShriek`: the derived
  projection formula.
- `AlgebraicGeometry.ProEtale.DerivedCategory.isDualizable_of_cover`: dualizability is local for
  the pro-étale topology.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {X : Scheme.{u}}

section LowerShriek

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U : Scheme.{u}} (f : U ⟶ X) (h : WeaklyEtale f)

/-- The lower shriek `f_!` along a weakly étale morphism `f : U ⟶ X`: the left Kan extension of
presheaves along the localization functor `U_proét ⥤ X_proét`, followed by sheafification. -/
noncomputable def weaklyEtaleLowerShriek :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The adjunction `f_! ⊣ f^*` for a weakly étale `f`. -/
noncomputable def localizationLowerShriekUpperStarAdjunction' :
    weaklyEtaleLowerShriek A f h ⊣ (f)^*[A] :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).ofNatIsoRight
    (ProEtale.upperStarIsoLocalizationRestriction A f h).symm

instance : (weaklyEtaleLowerShriek A f h).IsLeftAdjoint :=
  (localizationLowerShriekUpperStarAdjunction' A f h).isLeftAdjoint

/-- The lower shriek along a weakly étale morphism is left exact: the left Kan extension along
the localization functor is left exact, coproducts being exact in `A`. -/
instance : PreservesFiniteLimits (weaklyEtaleLowerShriek A f h) := by
  have := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A
    (P := @WeaklyEtale) h
  exact comp_preservesFiniteLimits (sheafToPresheaf _ A)
    (((MorphismProperty.Over.map ⊤ h).op.lan) ⋙ presheafToSheaf _ A)

instance : PreservesFiniteColimits (weaklyEtaleLowerShriek A f h) := by
  have := (localizationLowerShriekUpperStarAdjunction' A f h).leftAdjoint_preservesColimits
  infer_instance

instance : (weaklyEtaleLowerShriek A f h).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The projection formula for the lower shriek along a weakly étale morphism**, for sheaves:
the projection map of `f_! ⊣ f^*` is an isomorphism, being conjugate to the internal-hom comparison
of `f^*` (`AlgebraicGeometry.ProEtale.isIso_ihomComparison_upperStar`). -/
theorem isIso_projectionMap_localizationLowerShriek [MonoidalCategory A] [SymmetricCategory A]
    [MonoidalClosed A] [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
    [((Scheme.ProEt.topology X).W (A := A)).IsMonoidal]
    [((Scheme.ProEt.topology U).W (A := A)).IsMonoidal]
    (G : Sheaf (Scheme.ProEt.topology X) A) :
    IsIso (Functor.Monoidal.projectionMap
      (localizationLowerShriekUpperStarAdjunction' A f h) G) := by
  have := ProEtale.isIso_ihomComparison_upperStar A f G
  exact Functor.Monoidal.isIso_projectionMap_of_isIso_ihomComparison _ G

end LowerShriek

section Projection

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived adjunction `D(u_!) ⊣ Lu^*` for an étale morphism `u`, with the right adjoint
the left derived functor `Lu^*` (isomorphic to the levelwise `D(u^*)`, `u^*` being exact). -/
noncomputable def derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction {U : Scheme.{u}}
    (f : U ⟶ X) [WeaklyEtale f] :
    (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategory ⊣ L((f)^*[A]) :=
  let _ : CatCommSq ((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategory :=
    ⟨(weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.symm⟩
  let _ : CatCommSq (((f)^*[A]).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh
      DerivedCategory.Qh L((f)^*[A]) :=
    ⟨(asIso ((f)^*[A]).leftDerivedFunctorCounit).symm⟩
  ((localizationLowerShriekUpperStarAdjunction' A f inferInstance).mapHomotopyCategory
    (.up ℤ)).localization DerivedCategory.Qh (HomotopyCategory.quasiIso _ _)
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _ _

set_option maxHeartbeats 1000000 in
-- the chase unfolds the derived unit, counit and tensor comparison on large objects
open HomotopyCategory _root_.DerivedCategory in
/-- On objects coming from cochain complexes, the derived projection map of `D(u_!) ⊣ Lu^*` is
the image of the projection map on cochain complexes, up to the tensor comparison maps of `Qh`. -/
lemma projectionMap_derivedLocalizationLowerShriek_app_Qh {U : Scheme.{u}} (f : U ⟶ X) [WeaklyEtale f]
    [ProEtale.UpperStarPreservesFlat A] (K₁ : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ)
    (T₁ : CochainComplex (Sheaf (Scheme.ProEt.topology U) A) ℤ) :
    letI := leftDerivedUpperStarMonoidal A f
    (Functor.Monoidal.projectionMap (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction
        (A := A) f) (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁)) ≫
      (Qh.obj ((quotient _ _).obj K₁) ◁
        (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app
          ((quotient _ _).obj T₁)) ≫
      Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
    (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategory.map
        (((f)^*[A].leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ▷
          Qh.obj ((quotient _ _).obj T₁)) ≫
          Functor.LaxMonoidal.μ Qh _ ((quotient _ _).obj T₁)) ≫
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app _ ≫
        Qh.map ((quotient _ _).map ((Functor.Monoidal.projectionMap
          ((localizationLowerShriekUpperStarAdjunction' A f inferInstance).mapHomologicalComplex
            (.up ℤ)) K₁).app T₁)) := by
  let := leftDerivedUpperStarMonoidal A f
  simp only [Functor.Monoidal.projectionMap, Category.assoc]
  have hn := ((derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction (A := A) f).counit.naturality
    (Qh.obj ((quotient _ _).obj K₁) ◁
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app
        ((quotient _ _).obj T₁) ≫
      Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)))).symm
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction]
  erw [Adjunction.localization_counit_app, Adjunction.localization_unit_app]
  dsimp only [CatCommSq.iso, Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  conv_rhs => rw [Functor.map_comp, Functor.map_comp, ← Functor.mapHomotopyCategory_map]
  conv_rhs => simp only [Functor.map_comp, Category.assoc]
  have hφ : ∀ {Y Y' : HomotopyCategory (Sheaf (Scheme.ProEt.topology U) A) (.up ℤ)} (g : Y ⟶ Y'),
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app Y ≫
        Qh.map (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).map g) =
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategory.map (Qh.map g) ≫
        (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app Y' :=
    fun g ↦
      ((weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.naturality g).symm
  rw [reassoc_of% hφ, reassoc_of% hφ]
  simp only [← Functor.map_comp_assoc, Category.assoc]
  congr 2
  have key : Functor.LaxMonoidal.μ L((f)^*[A]) (Qh.obj ((quotient _ _).obj K₁))
        (Qh.obj (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁))) ≫
      L((f)^*[A]).map (Functor.LaxMonoidal.μ Qh ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁))) ≫
      (f)^*[A].leftDerivedFunctorCounit.app ((quotient _ _).obj K₁ ⊗
        ((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) =
      ((f)^*[A].leftDerivedFunctorCounit.app ((quotient _ _).obj K₁) ⊗ₘ
        (f)^*[A].leftDerivedFunctorCounit.app
          (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
            ((quotient _ _).obj T₁))) ≫
      Functor.LaxMonoidal.μ Qh (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K₁))
        (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj
          (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
            ((quotient _ _).obj T₁))) ≫
      Qh.map ((quotient _ _).map (Functor.LaxMonoidal.μ ((f)^*[A].mapHomologicalComplex (.up ℤ)) K₁
        (((weaklyEtaleLowerShriek A f inferInstance).mapHomologicalComplex (.up ℤ)).obj T₁))) := by
    have h := leftDerivedUpperStarTensorComparison_app_app_comp A f ((quotient _ _).obj K₁)
      (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
        ((quotient _ _).obj T₁))
    rw [← cancel_epi (Functor.OplaxMonoidal.δ L((f)^*[A]) _ _), Functor.Monoidal.δ_μ_assoc]
    erw [reassoc_of% h]
    rw [← Functor.map_comp _root_.DerivedCategory.Qh]
    have hδ : Functor.OplaxMonoidal.δ ((f)^*[A].mapHomotopyCategory (.up ℤ)) ((quotient _ _).obj K₁)
        (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
          ((quotient _ _).obj T₁)) ≫
        (quotient _ _).map (Functor.LaxMonoidal.μ ((f)^*[A].mapHomologicalComplex (.up ℤ)) K₁
          (((weaklyEtaleLowerShriek A f inferInstance).mapHomologicalComplex (.up ℤ)).obj T₁)) =
        𝟙 _ := by
      change (quotient _ _).map (Functor.OplaxMonoidal.δ ((f)^*[A].mapHomologicalComplex (.up ℤ))
        K₁ (((weaklyEtaleLowerShriek A f inferInstance).mapHomologicalComplex (.up ℤ)).obj T₁)) ≫
        _ = _
      rw [← Functor.map_comp, Functor.Monoidal.δ_μ]
      exact CategoryTheory.Functor.map_id _ _
    erw [hδ, CategoryTheory.Functor.map_id]
    rw [Category.comp_id]
  have hφ' : (Qh.obj ((quotient _ _).obj K₁) ◁
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.inv.app
        ((quotient _ _).obj T₁)) ≫ (Qh.obj ((quotient _ _).obj K₁) ◁
      (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.hom.app
        ((quotient _ _).obj T₁)) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app, MonoidalCategory.whiskerLeft_id]
  simp only [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  have hμ := Functor.LaxMonoidal.μ_natural_right L((f)^*[A]) (Qh.obj ((quotient _ _).obj K₁))
    ((weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategoryFactorsh.inv.app
      ((quotient _ _).obj T₁))
  rw [reassoc_of% hμ]
  rw [← Functor.map_comp_assoc L((f)^*[A]), hφ']
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  rw [key, tensorHom_def, Category.assoc]
  erw [whisker_exchange_assoc]
  rw [ ← MonoidalCategory.whiskerLeft_comp_assoc,
    NatIso.isIso_inv_app, IsIso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    whisker_exchange_assoc]
  congr 1
  have hq := Functor.LaxMonoidal.μ_natural_right Qh
    (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj ((quotient _ _).obj K₁))
    ((quotient _ _).map (((localizationLowerShriekUpperStarAdjunction' A f
      inferInstance).mapHomologicalComplex (.up ℤ)).unit.app T₁))
  erw [reassoc_of% hq]
  erw [← HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft']
  rfl

open HomotopyCategory _root_.DerivedCategory in
/-- The derived projection map of `D(u_!) ⊣ Lu^*` is an isomorphism at `K = Qh K₁` when `K₁`
and `u^*K₁` are K-flat and the projection maps on cochain complexes are isomorphisms. -/
lemma isIso_projectionMap_derivedLocalizationLowerShriek_app_Qh {U : Scheme.{u}} (f : U ⟶ X)
    [WeaklyEtale f] [ProEtale.UpperStarPreservesFlat A] (K₁ : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ)
    (hK₁ : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((quotient _ _).obj K₁))
    (hK₁' : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((quotient _ _).obj (((f)^*[A].mapHomologicalComplex (.up ℤ)).obj K₁)))
    (T₁ : CochainComplex (Sheaf (Scheme.ProEt.topology U) A) ℤ)
    [IsIso ((Functor.Monoidal.projectionMap
      ((localizationLowerShriekUpperStarAdjunction' A f inferInstance).mapHomologicalComplex
        (.up ℤ)) K₁).app T₁)] :
    letI := leftDerivedUpperStarMonoidal A f
    IsIso ((Functor.Monoidal.projectionMap (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction
        (A := A) f) (Qh.obj ((quotient _ _).obj K₁))).app (Qh.obj ((quotient _ _).obj T₁))) := by
  let := leftDerivedUpperStarMonoidal A f
  have h := projectionMap_derivedLocalizationLowerShriek_app_Qh (A := A) f K₁ T₁
  have := isIso_μ_Qh_of_kFlat ((quotient _ _).obj K₁)
    (((weaklyEtaleLowerShriek A f inferInstance).mapHomotopyCategory (.up ℤ)).obj
      ((quotient _ _).obj T₁)) hK₁
  have := isIso_μ_Qh_of_kFlat (((f)^*[A].mapHomotopyCategory (.up ℤ)).obj
    ((quotient _ _).obj K₁)) ((quotient _ _).obj T₁) hK₁'
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- **Derived projection formula for an étale morphism** `u : U ⟶ X`: the projection map
`D(u_!)(Lu^*K ⊗ᴸ T) ⟶ K ⊗ᴸ D(u_!)T` of the adjunction `D(u_!) ⊣ Lu^*`, for the monoidal
structure `leftDerivedUpperStarMonoidal` of `Lu^*`, is an isomorphism. -/
theorem isIso_projectionMap_derivedLocalizationLowerShriek {U : Scheme.{u}} (f : U ⟶ X) [WeaklyEtale f]
    [ProEtale.UpperStarPreservesFlat A]
    [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]
    [((Scheme.ProEt.topology U).W (A := A)).IsMonoidal] [((Scheme.ProEt.topology X).W (A := A)).IsMonoidal]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    letI := leftDerivedUpperStarMonoidal A f
    IsIso (Functor.Monoidal.projectionMap
      (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K) := by
  let := leftDerivedUpperStarMonoidal A f
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution
    (Sheaf (Scheme.ProEt.topology X) A)).some.reduced
  have hι := (ObjectProperty.flat (A := Sheaf (Scheme.ProEt.topology X) A)).essImage_ι_le
  let K₀ := _root_.DerivedCategory.Q.objPreimage K
  let K₁ := Λ.resolutionFunctor.obj K₀
  have : IsIso (_root_.DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀)) :=
    (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  let eK : K ≅ _root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K₁) :=
    (_root_.DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (_root_.DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).symm.app K₁
  have hK₁ := (HomotopyCategory.kFlat_quotient_obj_iff _).2 (Λ.kFlat_resolutionFunctor_obj hι K₀)
  have hK₁' := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A f Λ K₀
  have : ∀ G, IsIso (Functor.Monoidal.projectionMap
      (localizationLowerShriekUpperStarAdjunction' A f inferInstance) G) :=
    fun G ↦ isIso_projectionMap_localizationLowerShriek A f inferInstance G
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  let T₀ := _root_.DerivedCategory.Q.objPreimage T
  let eT : T ≅ _root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀) :=
    (_root_.DerivedCategory.Q.objObjPreimageIso T).symm ≪≫
      (_root_.DerivedCategory.quotientCompQhIso _).symm.app T₀
  have : PreservesColimitsOfSize.{0, 0} (weaklyEtaleLowerShriek A f inferInstance) :=
    (localizationLowerShriekUpperStarAdjunction' A f inferInstance).leftAdjoint_preservesColimits
  have := Functor.Monoidal.isIso_projectionMap_mapHomologicalComplex (f)^*[A]
    (localizationLowerShriekUpperStarAdjunction' A f inferInstance) K₁
  have := isIso_projectionMap_derivedLocalizationLowerShriek_app_Qh (A := A) f K₁ hK₁ hK₁' T₀
  have := Functor.Monoidal.isIso_projectionMap_app_of_iso
    (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) eK
    (_root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj T₀))
  have hn := (Functor.Monoidal.projectionMap
    (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K).naturality eT.hom
  have : IsIso ((Functor.Monoidal.projectionMap
      (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K).app T ≫
      K ◁ (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategory.map eT.hom) := by
    erw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (K ◁ (weaklyEtaleLowerShriek A f inferInstance).mapDerivedCategory.map eT.hom)

/-- For étale `u` and `K` with `Lu^*K` dualizable, `Lu^*` sends the comparison
`RHom(K, 𝟙) ⊗ᴸ K ⟶ RHom(K, K)` to an isomorphism. By
`CategoryTheory.Functor.Monoidal.isIso_map_ihomUnitTensorToIhom`, this follows from the derived
projection formula `isIso_projectionMap_derivedLocalizationLowerShriek`. -/
theorem isIso_leftDerivedUpperStar_map_ihomUnitTensorToIhom_of_isDualizable
    {U : Scheme.{u}} (f : U ⟶ X) [WeaklyEtale f] [ProEtale.UpperStarPreservesFlat A]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (hK : IsDualizable ((L((f)^*[A])).obj K)) :
    IsIso ((L((f)^*[A])).map (MonoidalClosed.ihomUnitTensorToIhom K K)) := by
  let := leftDerivedUpperStarMonoidal A f
  have := isIso_projectionMap_derivedLocalizationLowerShriek (A := A) f K
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology U) A)
  let := BraidedCategory.exactPairing_swap ((L((f)^*[A])).obj K) ((L((f)^*[A])).obj K)ᘁ
  have := MonoidalClosed.isIso_ihomUnitTensorToIhom ((L((f)^*[A])).obj K)ᘁ ((L((f)^*[A])).obj K)
    ((L((f)^*[A])).obj K)
  exact Functor.Monoidal.isIso_map_ihomUnitTensorToIhom
    (derivedLocalizationLowerShriekLeftDerivedUpperStarAdjunction (A := A) f) K K

end Projection

end ProEtale

end AlgebraicGeometry
