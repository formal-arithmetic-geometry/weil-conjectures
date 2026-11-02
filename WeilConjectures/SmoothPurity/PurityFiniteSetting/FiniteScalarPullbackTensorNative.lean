/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorFixedComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullbackCochainNormalization
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarSheafPullbackMonoidal
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProUpperStarTensorCochainRepresentative
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalRepresentative

/-! # The native scalar-extension/pullback tensor square

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2; Stacks Project, Tag 07A4.
(blueprint: lem-pur-finite-scalar-pullback-tensor-native)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

attribute [local implicit_reducible] WeilConjectures.PurityFiniteSetting.Coefficient
  Equivalence.mapDerivedCategory CategoryTheory.Equivalence.mk
  Scheme.sfIntrinsicDerivedEquivalence WeilConjectures.PurityFiniteSetting.coefficientCommRing
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor ProEtale.upperStar ProEtale.sheafExtendScalars
  Functor.leftDerivedFunctorCounit Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  HasDerivedCategory.standard

namespace WeilConjectures.PurityFiniteSetting

@[irreducible] private def coreTensorIso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (c : F.CoreMonoidal) :
    Functor.uncurry.obj (curriedTensor C) ⋙ F ≅
      F.prod F ⋙ Functor.uncurry.obj (curriedTensor D) := by
  letI := c.toOplaxMonoidal
  refine NatIso.ofComponents (fun Z ↦ (c.μIso Z.1 Z.2).symm) ?_
  rintro ⟨K, L⟩ ⟨K', L'⟩ ⟨f, g⟩
  simpa only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def,
    Functor.CoreMonoidal.toOplaxMonoidal_δ, Iso.symm_hom]
    using (Functor.OplaxMonoidal.δ_natural F f g).symm

private theorem coreTensorIso_app
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (c : F.CoreMonoidal) (K L : C) :
    (coreTensorIso F c).hom.app (K, L) = (c.μIso K L).inv := by
  unfold coreTensorIso
  rfl

private instance ordinaryLeftAdjoint
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (finiteVerdierOrdinaryExtension (ProEt.topology T) φ).IsLeftAdjoint :=
  (finiteVerdierOrdinaryAdjunction (ProEt.topology T) φ).isLeftAdjoint

private theorem model_normalized
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteVerdierOrdinaryExtension (ProEt.topology T) φ)
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T)
      (finiteVerdierScalarRepresentative (ProEt.topology T) φ)
      (coreTensorIso _ (finiteScalarMonoidalModel φ T)) := by
  intro C D
  refine Eq.mpr ?_ (finiteScalarMonoidalModel_representative φ T C D).symm
  simp only [coreTensorIso_app]
  unfold TensorRepresentativeData.source TensorRepresentativeData.obj finiteScalarTensorData
  unfold cochainLocalizationTensor finiteTensorCochainComparison
  unfold finiteVerdierScalarRepresentative finiteVerdierScalarRepresentativeAux
  unfold ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative
  unfold finiteVerdierOrdinaryExtension ProEtale.sheafExtendScalars
  unfold finiteVerdierOrdinaryAdjunction ProEtale.sheafExtendScalarsAdjunction
  rfl

private instance extensionDeltaIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
    IsIso (Functor.OplaxMonoidal.δ
      (finiteVerdierOrdinaryExtension (ProEt.topology T) φ) M N) :=
  isIso_δ_composeAndSheafify _ (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ) M N

private theorem native_cochain_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C D : CochainComplex (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C)
    (hD : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat D) :
    let SY := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ Y
    let SX := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ X
    let LA := (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let LB := (ProEtale.upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
    let a := ProEtale.scalarPullbackProEtaleIso φ f
    let K := DerivedCategory.Q.obj C
    let L := DerivedCategory.Q.obj D
    a.hom.app (K ⊗ L) ≫
        SX.map (((ProEtale.leftDerivedUpperStarTensorComparison
          (ModuleCat.{u + 1} A) f).app K).app L) ≫
        (coreTensorIso SX (finiteScalarMonoidalModel φ X)).hom.app (LA.obj K, LA.obj L) =
      LB.map ((coreTensorIso SY (finiteScalarMonoidalModel φ Y)).hom.app (K, L)) ≫
        ((ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f).app
          (SY.obj K)).app (SY.obj L) ≫ (a.hom.app K ⊗ₘ a.hom.app L) := by
  dsimp only
  let EY := finiteVerdierOrdinaryExtension (ProEt.topology Y) φ
  let EX := finiteVerdierOrdinaryExtension (ProEt.topology X) φ
  let FA := ProEtale.upperStar (ModuleCat.{u + 1} A) f
  let FB := ProEtale.upperStar (ModuleCat.{u + 1} B) f
  let SY := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ Y
  let SX := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ X
  let LA := FA.leftDerivedFunctor
  let LB := FB.leftDerivedFunctor
  let := (finiteVerdierOrdinaryAdjunction
    (ProEt.topology Y) φ).isLeftAdjoint
  let := (finiteVerdierOrdinaryAdjunction
    (ProEt.topology X) φ).isLeftAdjoint
  obtain ⟨rY, hrY, hYiso⟩ :=
    FiniteFreeCoefficients.pro_scalar_representative_transformation φ Y
  obtain ⟨rX, hrX, hXiso⟩ :=
    FiniteFreeCoefficients.pro_scalar_representative_transformation φ X
  let rA := FiniteFreeCoefficients.pro_geometric_representative A f
  let rB := FiniteFreeCoefficients.pro_geometric_representative B f
  exact normalized_cochain_square EY FB FA EX SY LB LA SX rY rB rA rX
    (finiteVerdierScalarRepresentative (ProEt.topology Y) φ)
    (fun K ↦ rB.app K) (fun K ↦ rA.app K)
    (finiteVerdierScalarRepresentative (ProEt.topology X) φ)
    hrY (fun _ ↦ rfl) (fun _ ↦ rfl) hrX
    (coreTensorIso _ (finiteScalarMonoidalModel φ Y))
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f)
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
    (coreTensorIso _ (finiteScalarMonoidalModel φ X))
    (model_normalized φ Y)
    (FiniteFreeCoefficients.pro_upperStar_tensor_cochain_representative B f)
    (FiniteFreeCoefficients.pro_upperStar_tensor_cochain_representative A f)
    (model_normalized φ X) (ProEtale.scalarPullbackProEtaleIso φ f)
    (FiniteFreeCoefficients.pro_scalar_sheaf_pullback_iso φ f)
    (FiniteFreeCoefficients.pro_scalar_sheaf_pullback_complex_iso φ f)
    rfl (FiniteFreeCoefficients.pro_scalar_sheaf_pullback_monoidal φ f)
    (fun K _ ↦ FiniteFreeCoefficients.pro_scalar_pullback_cochain_normalization φ f K)
    hYiso (FiniteFreeCoefficients.pro_geometric_representative_isIso B f) C D hC hD

private theorem native_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.ScalarPullbackTensorLaw
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ Y)
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ X)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (ProEtale.upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
      (ProEtale.scalarPullbackProEtaleIso φ f)
      (coreTensorIso _ (finiteScalarMonoidalModel φ Y))
      (coreTensorIso _ (finiteScalarMonoidalModel φ X))
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f)
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) f) := by
  let QY := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ Y
  let QX := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ X
  let LA := (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let LB := (ProEtale.upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor
  let TY := Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y)
  let TX := Functor.uncurry.obj (ProEtale.derivedTensor (ModuleCat.{u + 1} B) X)
  let dQY := coreTensorIso _ (finiteScalarMonoidalModel φ Y)
  let dQX := coreTensorIso _ (finiteScalarMonoidalModel φ X)
  let dLA := Etale.uncurryTensorComparison LA
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
  let dLB := Etale.uncurryTensorComparison LB
    (ProEtale.derivedTensor (ModuleCat.{u + 1} B) Y)
    (ProEtale.derivedTensor (ModuleCat.{u + 1} B) X)
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f)
  let a := ProEtale.scalarPullbackProEtaleIso φ f
  let α : TY ⋙ QY ⋙ LB ⟶
      (LA.prod LA) ⋙ (QX.prod QX) ⋙ TX :=
    Functor.whiskerLeft TY a.hom ≫
      Functor.whiskerRight dLA QX ≫
      Functor.whiskerLeft (LA.prod LA) dQX.hom
  let β : TY ⋙ QY ⋙ LB ⟶
      (LA.prod LA) ⋙ (QX.prod QX) ⋙ TX :=
    Functor.whiskerRight dQY.hom LB ≫
      Functor.whiskerLeft (QY.prod QY) dLB ≫
      Functor.whiskerRight (NatTrans.prod a.hom a.hom) TX
  have hab : α = β := by
    apply Etale.natTrans_ext_flat α β
    intro P R hP hR hPflat hRflat
    have h := native_cochain_square φ f P R hP hR
    simpa only [α, β, QY, QX, LA, LB, TY, TX, dQY, dQX, dLA, dLB, a,
      Etale.uncurryTensorComparison,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.comp_obj, Functor.prod_obj, ProEtale.derivedTensor,
      curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
      Functor.uncurry_obj_obj,
      Functor.uncurry_obj_map, NatTrans.prod, Etale.uncurryCurriedTensor_map,
      coreTensorIso_app, ProEtale.leftDerivedUpperStarTensorIso_hom,
      MonoidalCategory.tensorHom_def, Category.assoc] using h
  intro P R
  have hcomp := congrArg (fun t ↦ t.app (P, R)) hab
  simpa only [α, β, QY, QX, LA, LB, TY, TX, dQY, dQX, dLA, dLB, a,
    Etale.uncurryTensorComparison,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_obj, Functor.prod_obj, ProEtale.derivedTensor,
    curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map, Functor.uncurry_map_app,
    NatTrans.prod, Etale.uncurryCurriedTensor_map, ProEtale.leftDerivedUpperStarTensorIso_hom,
    MonoidalCategory.tensorHom_def,
    Category.assoc] using hcomp

private theorem finiteCore_eq_model (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    P.finiteTensorCore m hm hmn T =
      finiteScalarMonoidalModel (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T := by
  apply ((P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.2 _ ?_).symm
  intro C D _ _
  exact finiteScalarMonoidalModel_representative _ T C D

private theorem finiteTensorPullbackTensor_formula (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteTensorPullbackTensor f K L).hom =
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).inv.app (K ⊗ L) ≫
      (ProEtale.leftDerivedUpperStarTensorIso
        (ModuleCat.{u + 1} P.Coefficient) f K L).hom ≫
      ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).hom.app K ⊗ₘ
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) f).hom.app L) := by
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have h₁ := (Classical.choose_spec
    (existsUnique_compositionPullbackTensorFixed P.Ring f K L)).1
  have h₂ := (existsUnique_compositionPullbackTensor
    (ModuleCat.{u + 1} P.Coefficient) f K L).exists.choose_spec
  have h := eq_of_heq (h₁.trans h₂)
  simpa only [Iso.trans_hom, Iso.symm_hom, compositionTensorMapIso,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, ProEtale.derivedTensor,
    curriedTensor_map_app, curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Category.assoc, finiteTensorPullbackTensor, compositionPullbackTensorFixed,
    curriedTensor_obj_obj] using congrArg Iso.hom h

private theorem conjugate_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (SY : C ⥤ D) (SX : E ⥤ H) (LA MA : C ⥤ E) (LB MB : D ⥤ H)
    (c : SX.CoreMonoidal) (a : SY ⋙ LB ≅ LA ⋙ SX)
    (eA : LA ≅ MA) (eB : LB ≅ MB) (K L : C)
    (dA : LA.obj (K ⊗ L) ⟶ LA.obj K ⊗ LA.obj L)
    (dB : LB.obj (SY.obj K ⊗ SY.obj L) ⟶ LB.obj (SY.obj K) ⊗ LB.obj (SY.obj L))
    (δ : SY.obj (K ⊗ L) ⟶ SY.obj K ⊗ SY.obj L)
    (h : a.hom.app (K ⊗ L) ≫ SX.map dA ≫
        (c.μIso (LA.obj K) (LA.obj L)).inv =
      LB.map δ ≫ dB ≫ (a.hom.app K ⊗ₘ a.hom.app L)) :
    SX.map (eA.inv.app (K ⊗ L) ≫ dA ≫ (eA.hom.app K ⊗ₘ eA.hom.app L)) ≫
        (c.μIso (MA.obj K) (MA.obj L)).inv ≫
        ((SX.map (eA.inv.app K) ≫ a.inv.app K ≫ eB.hom.app (SY.obj K)) ⊗ₘ
          (SX.map (eA.inv.app L) ≫ a.inv.app L ≫ eB.hom.app (SY.obj L))) =
      (SX.map (eA.inv.app (K ⊗ L)) ≫ a.inv.app (K ⊗ L) ≫
        eB.hom.app (SY.obj (K ⊗ L))) ≫ MB.map δ ≫
        (eB.inv.app (SY.obj K ⊗ SY.obj L) ≫ dB ≫
          (eB.hom.app (SY.obj K) ⊗ₘ eB.hom.app (SY.obj L))) := by
  letI := c.toOplaxMonoidal
  have hn : SX.map (eA.hom.app K ⊗ₘ eA.hom.app L) ≫
      (c.μIso (MA.obj K) (MA.obj L)).inv =
    (c.μIso (LA.obj K) (LA.obj L)).inv ≫
      (SX.map (eA.hom.app K) ⊗ₘ SX.map (eA.hom.app L)) :=
    by simpa only [Functor.CoreMonoidal.toOplaxMonoidal_δ] using
      (Functor.OplaxMonoidal.δ_natural SX (eA.hom.app K) (eA.hom.app L)).symm
  have hi : SX.map dA ≫ (c.μIso (LA.obj K) (LA.obj L)).inv ≫
      (a.inv.app K ⊗ₘ a.inv.app L) =
      a.inv.app (K ⊗ L) ≫ LB.map δ ≫ dB := by
    have hi := congrArg (fun t ↦ a.inv.app (K ⊗ L) ≫ t ≫
      (a.inv.app K ⊗ₘ a.inv.app L)) h
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Functor.comp_obj] at hi
    simpa using hi
  simp only [SX.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have hc (Z : C) : SX.map (eA.hom.app Z) ≫ SX.map (eA.inv.app Z) = 𝟙 _ := by
    rw [← SX.map_comp, Iso.hom_inv_id_app, SX.map_id]
  simp only [tensorHom_comp_tensorHom, Category.assoc,
    reassoc_of% (hc K), reassoc_of% (hc L), Category.id_comp]
  rw [← tensorHom_comp_tensorHom, reassoc_of% hi]
  rw [← reassoc_of% eB.hom.naturality δ]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The finite tensor reduction square of `finiteTensorPullbackTensorReduction` in which all
three pullback comparisons are the native pro-étale scalar/pullback mate
`scalarPullbackProEtaleIso`, conjugated by `leftDerivedUpperStarIsoMapDerivedCategory`.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4
(blueprint: lem-pur-finite-scalar-pullback-tensor-native).
Proof: by naturality of every map in `K` and `L` and essential surjectivity of the
localization it suffices to treat `K = Q P` and `L = Q R` for flat-term K-flat complexes
`P`, `R`. Derived pullback and coefficient extension are computed on these
representatives (ringed pullback and change of coefficients preserve flat-term
K-flatness). There `finiteTensorCore` is the descent of the scalar balancing map and
`finiteTensorPullbackTensor` is the descent of the exact inverse-image tensor comparison,
so the square is the K-flat scalar/pullback tensor square of
`lem-pur-etale-scalar-pullback-tensor-kflat-representative`, transported to the pro-étale
site. Cancel the `leftDerivedUpperStarIsoMapDerivedCategory` conjugations by naturality.
No flatness of the coefficient quotient, no field structure on `X` or `Y` and no
finiteness on `K`, `L` is used. -/
theorem finiteScalarPullbackTensorNative (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (P.finiteTensorReduction m hm hmn X).map
          (P.finiteTensorPullbackTensor f K L).hom ≫
        ((P.finiteTensorCore m hm hmn X).μIso
          ((P.smoothPurityPullback f).obj K)
          ((P.smoothPurityPullback f).obj L)).inv ≫
        (((P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app K) ≫
          (ProEtale.scalarPullbackProEtaleIso
            (P.finiteReductionRingHom m hm hmn).ulift f).inv.app K ≫
          (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
            ((P.finiteTensorReduction m hm hmn Y).obj K)) ⊗ₘ
        ((P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app L) ≫
          (ProEtale.scalarPullbackProEtaleIso
            (P.finiteReductionRingHom m hm hmn).ulift f).inv.app L ≫
          (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
            ((P.finiteTensorReduction m hm hmn Y).obj L))) =
      ((P.finiteTensorReduction m hm hmn X).map
          ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) f).inv.app (K ⊗ L)) ≫
        (ProEtale.scalarPullbackProEtaleIso
          (P.finiteReductionRingHom m hm hmn).ulift f).inv.app (K ⊗ L) ≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).hom.app
          ((P.finiteTensorReduction m hm hmn Y).obj (K ⊗ L))) ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          ((P.finiteTensorCore m hm hmn Y).μIso K L).inv ≫
        ((P.finiteReductionSetting m hm).finiteTensorPullbackTensor f
          ((P.finiteTensorReduction m hm hmn Y).obj K)
          ((P.finiteTensorReduction m hm hmn Y).obj L)).hom := by
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite (P.finiteReductionSetting m hm).Ring :=
    Padic.finite_coefficientExtensionRing
      (P.finiteReductionSetting m hm).coefficients.l
      (P.finiteReductionSetting m hm).extension
      (P.finiteReductionSetting m hm).level (P.finiteReductionSetting m hm).level_pos
  letI : IsNoetherianRing P.Coefficient := compositionCoefficientNoetherian P.Ring
  letI : IsNoetherianRing (P.finiteReductionSetting m hm).Coefficient :=
    compositionCoefficientNoetherian (P.finiteReductionSetting m hm).Ring
  rw [finiteTensorPullbackTensor_formula, finiteTensorPullbackTensor_formula,
    finiteCore_eq_model, finiteCore_eq_model]
  exact conjugate_square
    (P.finiteTensorReduction m hm hmn Y) (P.finiteTensorReduction m hm hmn X)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
    (P.smoothPurityPullback f)
    (ProEtale.upperStar
      (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f).leftDerivedFunctor
    ((P.finiteReductionSetting m hm).smoothPurityPullback f)
    (finiteScalarMonoidalModel (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} X)
    (ProEtale.scalarPullbackProEtaleIso (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} P.Coefficient) f)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) f) K L
    _ _ _ (by
      have h := native_square (A := P.Coefficient)
        (B := (P.finiteReductionSetting m hm).Coefficient)
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} f K L
      rw [coreTensorIso_app, coreTensorIso_app] at h
      exact h)

end WeilConjectures.PurityFiniteSetting
