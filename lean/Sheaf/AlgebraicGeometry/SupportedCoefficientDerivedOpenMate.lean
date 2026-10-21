/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientOpenMateQuotient
import Sheaf.CategoryTheory.DerivedExactMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Normalization of the derived supported coefficient restriction mate

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, step 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

/-- The supported coefficient comparison adjoint to canonical open restriction.
Source: Stacks Tag 09XP
(blueprint: lem-pur-supported-coefficient-derived-open-mate). -/
noncomputable def supportCoefficientOpenMate (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    (supportedCoefficients A d).mapDerivedCategory ⟶
      (supportedCoefficients A b).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory :=
  supportCoefficientMate (supportedCoefficientDerivedAdjunction A b)
    (supportedCoefficientDerivedAdjunction A d)
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
    (derivedSupportTransport A h b d hd)

private theorem exactMap_fac
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K) := by
  simp only [Functor.exactDerivedMap, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem derivedMate_eq
    {B C D : Type*} [Category B] [Category C] [Category D]
    [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    {F : B ⥤ C} {R : C ⥤ B} {F' : B ⥤ D} {R' : D ⥤ B}
    [F.Additive] [R.Additive] [F'.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (adj : F ⊣ R) (adj' : F' ⊣ R') (H : C ⥤ D) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (r : R ⟶ H ⋙ R') :
    supportCoefficientMate adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction H.mapDerivedCategory
        (Functor.rightDerivedPullback H r) =
      Functor.exactDerivedMap (supportCoefficientMate adj adj' H r) ≫
        (Functor.mapDerivedCategoryCompIso F H).hom := by
  let σ := (mateEquiv adj adj').symm
    (TwoSquare.mk _ _ _ _ ((Functor.rightUnitor R).hom ≫ r))
  let α := supportCoefficientMate adj adj' H r
  have hα : α = σ.natTrans := by
    ext M
    exact Category.id_comp _
  let γ := Functor.exactDerivedMap α ≫ (Functor.mapDerivedCategoryCompIso F H).hom
  let θ : TwoSquare (𝟭 B).mapDerivedCategory F.mapDerivedCategory F'.mapDerivedCategory
      H.mapDerivedCategory := TwoSquare.mk _ _ _ _
    (Functor.whiskerRight (Functor.mapDerivedCategoryIdIso B).hom F'.mapDerivedCategory ≫
      (Functor.leftUnitor F'.mapDerivedCategory).hom ≫ γ)
  have hθ (N : HomotopyCategory B (.up ℤ)) :
      θ.natTrans.app (DerivedCategory.Qh.obj N) ≫
          H.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app N) ≫
          H.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj N) =
        F'.mapDerivedCategory.map ((𝟭 B).mapDerivedCategoryFactorsh.hom.app N) ≫
          F'.mapDerivedCategoryFactorsh.hom.app (((𝟭 B).mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ.natTrans (.up ℤ)).app N) := by
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective N
    dsimp only [θ, γ, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    simp only [Category.assoc]
    erw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh, exactMap_fac,
      Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
    congr 1
    erw [Category.id_comp]
    rw [hα]
    congr 1
  let β := (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction θ).natTrans
  have hβ' : Functor.whiskerLeft R.rightDerivedFunctor
      (Functor.mapDerivedCategoryIdIso B).inv ≫ β = Functor.rightDerivedPullback H r := by
    apply R.rightDerivedFunctor.rightDerived_ext R.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ))
    ext K
    have e := Adjunction.derivedExact_mateEquiv_app_fac adj adj' σ θ hθ K
    have hm : (mateEquiv adj adj' σ).natTrans = (Functor.rightUnitor R).hom ≫ r := by
      exact congrArg TwoSquare.natTrans ((mateEquiv adj adj').apply_symm_apply _)
    rw [hm] at e
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    erw [(Functor.mapDerivedCategoryIdIso B).inv.naturality_assoc]
    erw [e]
    rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
    erw [Iso.inv_hom_id_app_assoc]
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [Functor.rightDerivedPullback_fac_app]
    congr 2
    change (HomotopyCategory.quotient B (.up ℤ)).map _ =
      (HomotopyCategory.quotient B (.up ℤ)).map _
    congr 1
    ext n
    change 𝟙 _ ≫ r.app (K.X n) = r.app (K.X n)
    exact Category.id_comp _
  have hβ : β = Functor.whiskerLeft R.rightDerivedFunctor
      (Functor.mapDerivedCategoryIdIso B).hom ≫
      Functor.rightDerivedPullback H r := by
    rw [← hβ']
    ext Z
    simp
  ext M
  apply (adj'.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).injective
  have e := unit_mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction θ M
  change (𝟭 B).mapDerivedCategory.map
      (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫ β.app _ = _ at e
  rw [hβ] at e
  dsimp only [θ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_hom_app] at e
  simp only [Functor.map_comp] at e
  erw [(Functor.mapDerivedCategoryIdIso B).hom.naturality_assoc] at e
  have hn := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    ((Functor.mapDerivedCategoryIdIso B).hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [← reassoc_of% hn] at e
  have e' := (cancel_epi ((Functor.mapDerivedCategoryIdIso B).hom.app M)).1 e
  simpa [γ, α, supportCoefficientMate, Adjunction.homEquiv_apply] using e'

private theorem composite_unit_eq
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : C' ⥤ D) [G.Additive] :
    Functor.rightDerivedFunctorCompUnit P G ≫
        Functor.whiskerLeft DerivedCategory.Qh (Functor.whiskerRight
          P.rightDerivedFunctorIsoMapDerivedCategory.hom G.rightDerivedFunctor) =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G := by
  apply NatTrans.ext
  funext X
  have h := congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [Functor.rightDerivedFunctorCompUnit,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rw [← Functor.map_comp, h]

private theorem pullback_eq_comparison
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C']
    (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (F : C ⥤ D) (G : C' ⥤ D) [F.Additive] [G.Additive]
    (α : F ⟶ P ⋙ G)
    (e : (P ⋙ G).rightDerivedFunctor ≅ P.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (he : (P ⋙ G).rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit P G) :
    Functor.rightDerivedPullback P α = Functor.rightDerivedFunctorNatTrans α ≫ e.hom := by
  apply Functor.rightDerived_ext F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
  simp only [Functor.whiskerLeft_comp, ← Category.assoc]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedPullback P α) =
      Functor.rightDerivedPullbackAux P α by simp [Functor.rightDerivedPullback]]
  rw [show F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorNatTrans α) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α (.up ℤ)) DerivedCategory.Qh ≫
        (P ⋙ G).rightDerivedFunctorUnit by
      exact Functor.rightDerivedNatTrans_fac _ _ _ _ _ _]
  rw [Category.assoc, he]
  apply NatTrans.ext
  funext X
  simp [Functor.rightDerivedPullbackAux,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit]


private theorem support_pullback_eq (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    Functor.rightDerivedPullback (upperStar (ModuleCat.{u + 1} A) h)
      (supportTransport A h b d hd) = derivedSupportTransport A h b d hd := by
  apply pullback_eq_comparison
  exact (exists_unique_supportTransportComparison A h d).choose_spec.1 |>.trans
    (composite_unit_eq _ _)

/-- On complex models the derived open-support coefficient mate is the degreewise
ordinary mate, with the exact-functor localization factors displayed.
Source: Tag 0F1E, normalization in the open restriction calculation of
lem-pur-supported-product-localization, step 11.
(blueprint: lem-pur-supported-coefficient-derived-open-mate).
Proof: the normalized composite unit identifies derived support restriction with
`rightDerivedPullback` of the ordinary restriction. The exact-derived mate calculation
identifies its left mate with the localization of the ordinary left mate followed by
the exact-functor composition comparison. The localization factorization for this
composition and the defining equation of the localized ordinary transformation give
the formula. This works on arbitrary unbounded complexes. -/
theorem supportedCoefficientDerivedOpenMate_fac (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement)
    (K : HomotopyCategory (ModuleCat.{u + 1} A) (.up ℤ)) :
    (supportCoefficientOpenMate A h b d hd).app (DerivedCategory.Qh.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
          ((supportedCoefficients A b).mapDerivedCategoryFactorsh.hom.app K) ≫
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryFactorsh.hom.app
          (((supportedCoefficients A b).mapHomotopyCategory (.up ℤ)).obj K) =
      (supportedCoefficients A d).mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (supportCoefficientMate (supportedCoefficientAdjunction A b)
              (supportedCoefficientAdjunction A d) (upperStar (ModuleCat.{u + 1} A) h)
              (supportTransport A h b d hd)) (.up ℤ)).app K) := by
  dsimp only [supportCoefficientOpenMate, supportedCoefficientDerivedAdjunction]
  rw [← support_pullback_eq, derivedMate_eq]
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  exact exactMap_fac _ K

end AlgebraicGeometry.Etale
