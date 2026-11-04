/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ZeroSectionPurity
public import WeilConjectures.AlgebraicGeometry.RelativeLineLowDegreeGeneral
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting

/-! # The finite Kummer class against the Kummer class of the Tate twist datum

The étale class `kummerEtale` of the purity conventions, built from the Kummer boundary at the
level `ℓ^N` and the finite root line, is the Kummer class of the Tate twist datum
(`AlgebraicGeometry.Etale.kummerClass`) up to identifications of the source and target
(blueprint: lem-pur-relative-kummer-arbitrary-base-maps, normalization of the Kummer class).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
universe u

namespace AlgebraicGeometry.Scheme

/-- The Kummer boundaries at levels `m = n d` and `n` are compatible with the power map
`μ_m ⟶ μ_n`, `u ↦ u^d`. -/
theorem sheafH_map_rootsOfUnityPow_kummerδ₀ (X : Scheme.{u}) (n d m : ℕ) (h : m = n * d)
    (hm : IsUnit (m : Γ(X, ⊤))) (hn : IsUnit (n : Γ(X, ⊤))) (t : Γ(X, ⊤)ˣ) :
    Sheaf.H.map (rootsOfUnityPow (X := X) n d m h) 1 (X.kummerδ₀ m hm (Additive.ofMul t)) =
      X.kummerδ₀ n hn (Additive.ofMul t) := by
  let φ : X.kummerSequence m ⟶ X.kummerSequence n :=
    { τ₁ := rootsOfUnityPow n d m h
      τ₂ := d • 𝟙 X.gmSheaf
      τ₃ := 𝟙 X.gmSheaf
      comm₁₂ := rootsOfUnityPow_ι n d m h
      comm₂₃ := by
        dsimp [kummerSequence]
        rw [Category.comp_id, nsmul_id_comp_nsmul_id, h, mul_comm] }
  have hφ := (X.kummerSequence_shortExact m hm).extClass_naturality
    (X.kummerSequence_shortExact n hn) φ
  rw [kummerδ₀_eq_comp_extClass, kummerδ₀_eq_comp_extClass, Sheaf.H.map_apply,
    Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by omega)]
  erw [hφ]
  congr 1
  exact Abelian.Ext.mk₀_id_comp _

/-- The comparison `A ⊗_{ℤ/N} M ≅ A ⊗_ℤ M` sends `1 ⊗ z` to `1 ⊗ z`. -/
private theorem zmodScalarExtensionIso_hom_app_one_tmul (N : ℕ) (A : Type (u + 1))
    [CommRing A] (hA : (N : A) = 0) (M : ModuleCat.{u + 1} (ZMod N)) (z : M) :
    ((zmodScalarExtensionIso N A hA).hom.app M).hom
        ((1 : A) ⊗ₜ[ZMod N, finiteEtaleTwistScalar N A hA] z) =
      ((ModuleCat.extendScalarsAddCommGrpAdj A).unit.app
        ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M)).hom z := by
  unfold zmodScalarExtensionIso
  dsimp only
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply.{u + 1, 0, u + 1},
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.mkOfHomEquiv_unit_app,
    Equiv.trans_apply]
  exact congrArg (fun g : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶ _ ↦
    AddCommGrpCat.Hom.hom g z) ((ModuleCat.extendScalarsAddCommGrpAdj A).homEquiv_id _)

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] coefficientNeZero

/-- The finite twist line is the scalar extension of the roots of unity. -/
private noncomputable def twistEtaleIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    P.twistEtale h T ≅
      (Etale.extendScalars P.Coefficient T).obj (T.rootsOfUnitySheaf P.exponent) :=
  Scheme.finiteEtaleLineAbIso T P.exponent P.Coefficient (P.exponent_coefficient_eq_zero h)

/-- The coefficient map `μ_m ⟶ μ_m ⊗ A` is the unit of the extension of scalars, through the
identification of the finite twist line with the scalar extension of `μ_m`. -/
private theorem rootCoefficientMap_comp_forgetEtale_map (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    P.rootCoefficientMap h T ≫ (P.forgetEtale T).map (twistEtaleIso P h T).hom =
      (Etale.extendScalarsAdjunction P.Coefficient T).unit.app
        (T.rootsOfUnitySheaf P.exponent) := by
  have hm := P.exponent_coefficient_eq_zero h
  apply Sheaf.hom_ext
  ext W z
  have h1 := (Classical.choose_spec (P.existsUnique_rootCoefficientMap h T)).1 W z
  have h2 := congrArg (fun g ↦ (g.app W).hom
    ((1 : P.Coefficient) ⊗ₜ[ZMod P.exponent, Scheme.finiteEtaleTwistScalar P.exponent
      P.Coefficient hm] (z : (T.rootsOfUnitySheaf P.exponent).obj.obj W)))
    (toSheafify_naturality T.smallEtaleTopology (Functor.whiskerLeft
      (Scheme.finiteEtaleMuModulePresheaf T P.exponent)
      (Scheme.zmodScalarExtensionIso P.exponent P.Coefficient hm).hom))
  have h3 := Scheme.zmodScalarExtensionIso_hom_app_one_tmul P.exponent P.Coefficient hm
    ((Scheme.finiteEtaleMuModulePresheaf T P.exponent).obj W) z
  refine (congrArg (fun x ↦ (((P.forgetEtale T).map (twistEtaleIso P h T).hom).hom.app W).hom x)
    h1).trans (h2.symm.trans ?_)
  refine (congrArg ((toSheafify T.smallEtaleTopology
    (Scheme.finiteEtaleMuModulePresheaf T P.exponent ⋙
      forget₂ (ModuleCat (ZMod P.exponent)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp P.Coefficient)).app W).hom h3).trans ?_
  rw [Etale.extendScalarsAdjunction, Sheaf.adjunction_unit_app_hom]
  rfl

/-- The constant sheaf `A` is the scalar extension of `ℤ`, compatibly with the unit sections. -/
theorem exists_constantEtale_iso (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ∃ ε : P.constantEtale T ≅
        (Etale.extendScalars P.Coefficient T).obj T.constantSheafInt,
      P.integerToConstant T ≫ (P.forgetEtale T).map ε.hom =
        Etale.unitIntToExtendScalars P.Coefficient T := by
  obtain ⟨f, hf⟩ := (integerToConstant_hom_bijective P T
    ((Etale.extendScalars P.Coefficient T).obj T.constantSheafInt)).2
      (Etale.unitIntToExtendScalars P.Coefficient T)
  obtain ⟨g, hg⟩ := (Etale.bijective_unitIntToExtendScalars_comp P.Coefficient T
    (P.constantEtale T)).2 (P.integerToConstant T)
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (integerToConstant_hom_bijective P T (P.constantEtale T)).1
    dsimp only at hf hg ⊢
    rw [Functor.map_comp, ← Category.assoc, hf]
    erw [hg]
    simp
  · apply (Etale.bijective_unitIntToExtendScalars_comp P.Coefficient T _).1
    dsimp only at hf hg ⊢
    rw [Functor.map_comp, ← Category.assoc]
    erw [hg, hf]
    simp

theorem exists_kummerEtale_hom_eq (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (hr : IsUnit (P.exponent : Γ(T, ⊤))) [HasInvertibleExponent P.Coefficient T]
    (t : Γ(T, ⊤)ˣ) :
    ∃ (e₁ : (DerivedCategory.singleFunctor _ 0).obj (P.constantEtale T) ≅
        Etale.constantComplex P.Coefficient T)
      (e₂ : Etale.tateObject P.Coefficient T 1 ≅
        (DerivedCategory.singleFunctor _ 0).obj (P.twistEtale h T)),
      (P.kummerEtale h T hr t).hom =
        e₁.hom ≫ Etale.kummerClass P.Coefficient t ≫ e₂.hom⟦(1 : ℤ)⟧' := by
  have hm := P.exponent_coefficient_eq_zero h
  obtain ⟨ε, hε⟩ := exists_constantEtale_iso P T
  obtain ⟨d, hd⟩ := (ringChar.spec P.Coefficient P.exponent).1 hm
  have hn := isUnit_ringChar_of_hasInvertibleExponent (Λ := P.Coefficient) T
  have hiso (c : ℕ) (hc : c = ringChar P.Coefficient * d) (hcu : IsUnit (c : Γ(T, ⊤))) :
      IsIso ((Etale.extendScalars P.Coefficient T).map
        (Scheme.rootsOfUnityPow (X := T) (ringChar P.Coefficient) d c hc)) := by
    subst hc
    exact Etale.isIso_extendScalars_map_rootsOfUnityPow P.Coefficient _ d
      ringChar.Nat.cast_ringChar hcu
  have := hiso P.exponent hd hr
  let τ : (Etale.extendScalars P.Coefficient T).obj
      (T.rootsOfUnitySheaf (ringChar P.Coefficient)) ≅ P.twistEtale h T :=
    (asIso ((Etale.extendScalars P.Coefficient T).map
      (Scheme.rootsOfUnityPow (X := T) (ringChar P.Coefficient) d P.exponent hd))).symm ≪≫
      (twistEtaleIso P h T).symm
  have hK := Etale.shortExact_kummerSequence_pullback_map_extendScalars P.Coefficient
    (Scheme.unitToGmSheaf t)
    (fun x ↦ Etale.projective_sheafFiber_constantSheafInt (T.uliftPointSmallEtale x))
  have hroot : P.rootCoefficientMap h T =
      (Scheme.rootsOfUnityPow (X := T) (ringChar P.Coefficient) d P.exponent hd ≫
        (Etale.extendScalarsAdjunction P.Coefficient T).unit.app
          (T.rootsOfUnitySheaf (ringChar P.Coefficient))) ≫
          ((P.forgetEtale T).mapIso τ).hom := by
    refine (Iso.comp_inv_eq _).1 ?_
    simp only [τ, Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, asIso_hom,
      Functor.map_comp, ← Category.assoc, rootCoefficientMap_comp_forgetEtale_map]
    exact ((Etale.extendScalarsAdjunction P.Coefficient T).unit.naturality _).symm
  have key : P.kummerEtale h T hr t = (Abelian.Ext.mk₀ ε.hom).comp
      (hK.extClass.comp (Abelian.Ext.mk₀ τ.hom) (add_zero 1)) (zero_add 1) := by
    refine (Equiv.symm_apply_eq _).2 ?_
    rw [hroot, Functor.mapIso_hom, Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply,
      Scheme.sheafH_map_rootsOfUnityPow_kummerδ₀ T _ d _ hd hr hn]
    refine (congrArg (Sheaf.H.map ((P.forgetEtale T).map τ.hom) 1)
      (Etale.extToSheafHOf_kummerExtClass P.Coefficient T t).symm).trans ?_
    refine (Etale.extToSheafHOf_comp_mk₀ P.Coefficient _ τ.hom 1 _).symm.trans ?_
    rw [Equiv.ofBijective_apply, moduleClassToAbelian, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀_assoc, hε]
    rfl
  refine ⟨(DerivedCategory.singleFunctor _ 0).mapIso ε ≪≫
      (Etale.constantComplexIsoSingleFunctorExtendScalarsInt T P.Coefficient).symm,
    Etale.tateTwistObjectOneIso T P.Coefficient ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso τ, ?_⟩
  have hk : Etale.kummerClass P.Coefficient t = Etale.kummerClassOf T P.Coefficient t := rfl
  rw [key, hk, Etale.kummerClassOf_def, Abelian.Ext.comp_hom, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    ShortComplex.ShortExact.extClass_hom]
  simp only [Etale.kummerδ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [Iso.map_inv_hom_id_assoc]
  rfl

end WeilConjectures.PurityFiniteSetting
