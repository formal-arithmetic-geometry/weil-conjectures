/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCocycle
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityDerivedFactors
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! # Units of the normalized derived ordinary square

The normalized derived ordinary square at an identity inclusion is compatible with the
ordinary derived unit and the ambient derived unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdIntegralScalarForward

section Abstract

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u₅

/-- The derived unit of an exact functor family, transported along an index equality, is
computed on representatives. -/
theorem derived_unit_transport {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory C]
    {K : Type u₂} (F : K → C ⥤ C) [∀ k, (F k).Additive] [∀ k, PreservesFiniteLimits (F k)]
    [∀ k, PreservesFiniteColimits (F k)] (k k₀ : K) (hk : k = k₀) (a : F k₀ ≅ 𝟭 C)
    (U : (F k₀).mapDerivedCategory ≅ 𝟭 (DerivedCategory C))
    (hU : ∀ P, U.hom.app (DerivedCategory.Q.obj P) =
      (F k₀).mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app P))
    (P : CochainComplex C ℤ) :
    (eqToIso (congrArg (fun k ↦ (F k).mapDerivedCategory) hk) ≪≫ U).hom.app
        (DerivedCategory.Q.obj P) =
      (F k).mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (eqToIso (congrArg F hk) ≪≫ a) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app P) := by
  subst hk
  simpa using hU P

/-- The unit equation of a normalized derived square, from its chain-level counterpart. -/
theorem unit_full {KE : Type u₁} {PE : Type u₂} {DE : Type u₃} {EE : Type u₄}
    [Category.{v₁} KE] [Category.{v₂} PE] [Category.{v₃} DE] [Category.{v₄} EE]
    (QE : KE ⥤ DE) [QE.EssSurj] (RE : PE ⥤ EE) (oh : KE ⥤ KE) (tE : KE ⥤ PE) (xh : PE ⥤ PE)
    (Oh Oh' : DE ⥤ DE) (TE : DE ⥤ EE) (Xh : EE ⥤ EE)
    (foh : QE ⋙ Oh ≅ oh ⋙ QE) (ftE : QE ⋙ TE ≅ tE ⋙ RE) (εh : RE ⋙ Xh ⟶ xh ⋙ RE)
    (ch : oh ⋙ tE ≅ tE ⋙ xh) (ou : oh ≅ 𝟭 KE) (xu : xh ≅ 𝟭 PE)
    (eh : Oh ⋙ TE ≅ TE ⋙ Xh) (e : Oh = Oh') (U : Oh' ≅ 𝟭 DE) (Xu : Xh ≅ 𝟭 EE)
    (heh : ∀ P, eh.hom.app (QE.obj P) ≫ Xh.map (ftE.hom.app P) ≫ εh.app (tE.obj P) =
      TE.map (foh.hom.app P) ≫ ftE.hom.app (oh.obj P) ≫ RE.map (ch.hom.app P))
    (hOu : ∀ P, (eqToIso e ≪≫ U).hom.app (QE.obj P) = foh.hom.app P ≫ QE.map (ou.hom.app P))
    (hXu : ∀ P, Xu.hom.app (RE.obj P) = εh.app P ≫ RE.map (xu.hom.app P))
    (hc : ∀ P, tE.map (ou.hom.app P) = ch.hom.app P ≫ xu.hom.app (tE.obj P))
    (Y : DE) :
    eh.inv.app Y ≫ TE.map (eqToHom (Functor.congr_obj e.symm.symm Y) ≫ U.hom.app Y) =
      Xu.hom.app (TE.obj Y) := by
  have h := unit_of_essSurj QE Oh TE Xh eh (eqToIso e ≪≫ U) Xu (fun P ↦ derived_unit QE RE oh tE
    xh Oh TE Xh foh ftE εh ch ou xu eh (eqToIso e ≪≫ U) Xu heh hOu hXu
    (fun P ↦ by rw [hc P, Iso.inv_hom_id_app_assoc]) P) Y
  simpa [eqToHom_app] using h

end Abstract

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u})

set_option hygiene false in
local notation "𝒪 " h:max => integralOrdinaryScalar l (pbcFiniteField.{u} l Ω _)
  (pbcFiniteField.{u} l Ω _) (pbcFiniteFieldInclusion l Ω h) T

set_option hygiene false in
local notation "𝓉 " E:max => fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T

set_option hygiene false in
local notation "𝒳 " h:max => pbcExtend (pbcCompletedScalarMap l Ω T h)

/-- The ordinary derived unit on representatives. -/
private theorem ods_unit_fac (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    (integralOrdinaryDerivedScalarUnit l E T).hom.app (DerivedCategory.Q.obj P) =
      (integralOrdinaryScalar l E E (AlgHom.id ℚ_[l] E) T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (integralOrdinaryScalarUnit l E T) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) :=
  podIdentityDerivedFactors _ _ P

variable [IsNoetherian T]

private theorem chain_unit_gen {V W : Type*} [Category V] [Category W] [Preadditive V]
    [Preadditive W] (o : V ⥤ V) (t : V ⥤ W) (x : W ⥤ W) [ho : o.Additive] [ht : t.Additive]
    [hx : x.Additive]
    (c : o ⋙ t ≅ t ⋙ x)
    (C : o.mapHomologicalComplex (.up ℤ) ⋙ t.mapHomologicalComplex (.up ℤ) ≅
      t.mapHomologicalComplex (.up ℤ) ⋙ x.mapHomologicalComplex (.up ℤ))
    (hC : ∀ P n, (C.hom.app P).f n = c.hom.app (P.X n)) (Ou : o ≅ 𝟭 V) (Xu : x ≅ 𝟭 W)
    (hmod : ∀ N, c.inv.app N ≫ t.map (Ou.hom.app N) = Xu.hom.app (t.obj N))
    (P : CochainComplex V ℤ) :
    (t.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex Ou (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso V (.up ℤ)).hom.app P) =
      C.hom.app P ≫ (NatIso.mapHomologicalComplex Xu (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso W (.up ℤ)).hom.app
          ((t.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := hmod (P.X n)
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom] at h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hC,
    Iso.trans_hom, NatTrans.comp_app, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  erw [Category.comp_id, Category.comp_id]
  exact h

/-- Chain-level unit equation of the ordinary transport comparison. -/
private theorem ordinary_unit_chain (E : Padic.FiniteCoefficientFields l Ω)
    (o : FdOrdinaryScalarTransport l Ω T (le_refl E))
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    letI := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
    ((𝓉 E).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (Ounit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) =
      (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T (le_refl E) o).hom.app P ≫
        (NatIso.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app
            (((𝓉 E).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact chain_unit_gen (ht := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T)
    (ho := integralOrdinaryScalar_additive l _ _ _ T)
    (hx := pbcExtend_additive (pbcCompletedScalarMap l Ω T (le_refl E)))
    _ _ _ (oc l Ω T (le_refl E) o) _ (otc_f l Ω T (le_refl E) o)
    (Ounit l Ω T E) (pbcOrdinaryScalarUnit l Ω T E)
    (comparison_unit l Ω T E (oc l Ω T (le_refl E) o) (Ounit l Ω T E)
      (pbcOrdinaryScalarUnit l Ω T E) (oc_inv_tensor l Ω T (le_refl E) o)
      (Ounit_tensor l Ω T E) (Xunit_tensor l Ω T E)) P

/-- The ambient derived unit on representatives. -/
private theorem ambient_unit_rep (E : Padic.FiniteCoefficientFields l Ω)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ) :
    (pbcAmbientScalarUnit l Ω T E).hom.app (DerivedCategory.Q.obj P) =
      (pbcCounitNT (pbcCompletedScalarMap l Ω T (le_refl E))).app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) := by
  rw [pbcCounitNT_app]
  refine ((pbcAmbientScalarUnit_exists l Ω T E).exists.choose_spec P).trans ?_
  congr 2

/-- The ordinary derived unit at the identity inclusion on representatives. -/
private theorem ods_unit_incl (E : Padic.FiniteCoefficientFields l Ω)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    (eqToIso (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω E) ι T) (inclusion_id l Ω E)) ≪≫
        integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app
        (DerivedCategory.Q.obj P) =
      (𝒪 (le_refl E)).mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Ounit l Ω T E) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.app P) :=
  -- TODO: the direct instantiation of `derived_unit_transport` times out in the kernel.
  sorry

/-- The normalized derived ordinary square is compatible with the units. -/
private theorem eD_unit (E : Padic.FiniteCoefficientFields l Ω)
    (o : FdOrdinaryScalarTransport l Ω T (le_refl E))
    (Y : DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) T)) :
    (eD l Ω T (le_refl E) o).inv.app Y ≫
        (integralDetailedTransport T l _).map
          (eqToHom (Functor.congr_obj (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l
            (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω E) ι T)
            (inclusion_id l Ω E).symm).symm Y) ≫
            (integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app Y) =
      (pbcAmbientScalarUnit l Ω T E).hom.app ((integralDetailedTransport T l _).obj Y) := by
  -- TODO: the instantiation below of `unit_full` times out in the kernel.
  sorry
  /-   let := fdCoefficientTransportAdditive l (pbcFiniteField.{u} l Ω E) T
  exact unit_full DerivedCategory.Q DerivedCategory.Q
    ((𝒪 (le_refl E)).mapHomologicalComplex (.up ℤ)) ((𝓉 E).mapHomologicalComplex (.up ℤ))
    ((𝒳 (le_refl E)).mapHomologicalComplex (.up ℤ)) _ _ _ _
    (𝒪 (le_refl E)).mapDerivedCategoryFactors
    (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T)
    (pbcCounitNT _) (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T _ o)
    (NatIso.mapHomologicalComplex (Ounit l Ω T E) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ))
    (NatIso.mapHomologicalComplex (pbcOrdinaryScalarUnit l Ω T E) (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ))
    (eD l Ω T (le_refl E) o) _ (integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T)
    (pbcAmbientScalarUnit l Ω T E) (eD_heh l Ω T (le_refl E) o)
    (ods_unit_incl l Ω T E)
    (ambient_unit_rep l Ω T E) (ordinary_unit_chain l Ω T E o) Y -/

end WeilConjectures.FdIntegralScalarForward
