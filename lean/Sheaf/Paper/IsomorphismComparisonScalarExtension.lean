/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.PurInverseImageTensorHom
public import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Paper.IntegralPullbackComparisonRealization

/-!
# Coefficient compatibility of the specified integral inverse-image comparison

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51.
The scalar compatibility formula is the agent calculation from the specified
quotient-cone maps (blueprint: lem-weil-isomorphism-comparison-scalar-extension).
The ordinary tensor is expressed in its exact finite-free model. Its completion
comparison is identified with the specified universal derived-tensor comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem tensorModel_hom_ext (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) (f g : A ⟶ B)
    (h : ∀ (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      g.val.app U ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))) : f = g := by
  subst A
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact h U a x
  | add z z' hz hz' => simp only [map_add, hz, hz']

private theorem tensorModel_transport (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A B : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom ((hA.trans (congrArg
      (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans hB.symm)).val.app U
      ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom hB.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} ψ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(ψ.hom.app U).hom] x)) := by
  subst ψ
  subst A
  subst B
  rfl

private theorem tensorModel_natural (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : M ⟶ N)
    (A B C D : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hB : B = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N)
    (hC : C = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (hD : D = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ N)
    (a : A ⟶ B) (b : C ⟶ D)
    (ha : a = eqToHom hA ≫ SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom hB.symm)
    (hb : b = eqToHom hC ≫ SheafOfModules.changeOfRingsHom ψ M f ≫ eqToHom hD.symm) :
    a ≫ eqToHom ((hB.trans (congrArg
      (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N) hφ)).trans hD.symm) =
    eqToHom ((hA.trans (congrArg
      (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans hC.symm) ≫ b := by
  subst ψ
  subst A
  subst B
  subst C
  subst D
  simpa using ha.trans hb.symm

private theorem tensorModel_iso (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ)
    (F G : (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ⥤ (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)))
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (hG : ∀ M, G.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} ψ M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hF N).symm)
    (hmG : ∀ {M N} (f : M ⟶ N), G.map f = eqToHom (hG M) ≫
      SheafOfModules.changeOfRingsHom ψ M f ≫ eqToHom (hG N).symm) :
    ∃! e : F ≅ G, ∀ (M : (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) (U : W.ProEtᵒᵖ)
      (a : S.obj.obj U) (x : M.val.obj U),
      (e.hom.app M).val.app U ((eqToHom (hF M).symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) =
      (eqToHom (hG M).symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf ψ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(ψ.hom.app U).hom] x)) := by
  let hobj (M) := ((hF M).trans (congrArg
    (fun φ ↦ SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M) hφ)).trans (hG M).symm
  let e : F ≅ G := NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) (by
    intro M N f
    exact tensorModel_natural W φ ψ hφ M N f _ _ _ _ (hF M) (hF N) (hG M) (hG N)
      _ _ (hmF f) (hmG f))
  have he (M) (U) (a) (x) := tensorModel_transport W φ ψ hφ M _ _ (hF M) (hG M) U a x
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply tensorModel_hom_ext W φ M _ _ (hF M)
  intro U a x
  exact (he' M U a x).trans (he M U a x).symm

/-- The two ordinary tensor models have the same pure tensors, with their canonical
coefficient actions. Source: the quotient-cone calculation at Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the two coefficient maps agree after every quotient projection, so are equal.
The sheafified balanced tensor constructions therefore have identical generators
and relations. Send each displayed generator to the other displayed generator.
This gives inverse natural maps, uniquely determined by local tensor generation. -/
theorem isomorphismScalarSheafModel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! e : integralOrdinaryScalar l E L ι W ≅ completedOrdinaryScalarExtension l E L ι W,
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
        (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
        (x : M.val.obj U),
        (e.hom.app M).val.app U (integralOrdinaryTensorSection l E L ι W M U a x) =
          completedScalarTensorSection l E L ι W M U a x := by
  have hφ : integralCompletedScalarMap l E L ι W = completedCoefficientMap l E L ι W := by
    apply (completedCoefficientMap_existsUnique l E L ι W).unique
    · exact (integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec
    · exact (completedCoefficientMap_existsUnique l E L ι W).exists.choose_spec
  exact tensorModel_iso W (integralCompletedScalarMap l E L ι W)
    (completedCoefficientMap l E L ι W) hφ (integralOrdinaryScalar l E L ι W)
    (completedOrdinaryScalarExtension l E L ι W)
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose)
    ((completedScalarChangeData l E L ι W).choose_spec.choose)
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose)
    ((completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose)

/-- The actual identity on pure tensors between the two recorded ordinary models.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarSheafModel (W : AlgebraicGeometry.Scheme.{u}) :=
  (isomorphismScalarSheafModel_existsUnique l E L ι W).exists.choose

section DerivedComparison

attribute [local irreducible] integralScalarReductionWitness integralScalarReduction
  integralScalarTensorSection

private theorem scalarChainModel (W : AlgebraicGeometry.Scheme.{u}) :
    NatTrans.mapHomologicalComplex (isomorphismScalarSheafModel l E L ι W).hom
        (ComplexShape.up ℤ) ≫ completedScalarChainComparison l E L ι W =
      integralScalarCompletionChain l E L ι W := by
  apply (integralScalarCompletionChain_existsUnique l E L ι W).unique
  · constructor
    · intro P i n U a x
      dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f,
        NatTrans.mapHomologicalComplex_app_f]
      simp only [Category.assoc, SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
      change (((completedScalarChainComparison l E L ι W).app P).f i ≫
        (CochainComplex.mappingCocone.fst
          (completedScalarRoosEndomorphism l E L ι W P)).f i ≫
        (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op n)) n).f i
        ).val.app U
          (((isomorphismScalarSheafModel l E L ι W).hom.app (P.X i)).val.app U
            (integralOrdinaryTensorSection l E L ι W (P.X i) U a x)) = _
      exact (congrArg (fun z ↦
        (((completedScalarChainComparison l E L ι W).app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E L ι W P)).f i ≫
          (Pi.π (fun n ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op n)) n).f i
          ).val.app U z)
        ((isomorphismScalarSheafModel_existsUnique l E L ι W).exists.choose_spec
          (P.X i) U a x)).trans
        ((completedScalarChainComparison_existsUnique l E L ι W).exists.choose_spec.1
          P i n U a x)
    · intro P i j hij
      dsimp only [NatTrans.comp_app, HomologicalComplex.comp_f]
      have hj : j = i - 1 := by omega
      subst j
      change ((NatTrans.mapHomologicalComplex
        (isomorphismScalarSheafModel l E L ι W).hom (.up ℤ)).app P).f i ≫
          (((completedScalarChainComparison l E L ι W).app P).f i ≫
            (CochainComplex.mappingCocone.snd
              (completedScalarRoosEndomorphism l E L ι W P)).v i (i - 1) (by omega)) = 0
      have h := (completedScalarChainComparison_existsUnique l E L ι W).exists.choose_spec.2 P i
      change ((completedScalarChainComparison l E L ι W).app P).f i ≫ _ = 0 at h
      rw [h]
      simp
  · exact (integralScalarCompletionChain_existsUnique l E L ι W).exists.choose_spec

attribute [local irreducible] completedScalarChangeData

private theorem exactDerivedModel
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (es : F ≅ G) (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    ∃! e : F.mapDerivedCategory ≅ LF,
      ∀ P : CochainComplex C ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient _ _).obj P) =
        F.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex es (.up ℤ)).hom.app P) := by
  let V := HomotopyCategory.quasiIso C (.up ℤ)
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ G.mapDerivedCategoryFactorsh
  let j : G.mapDerivedCategory ≅ LF :=
    Functor.leftDerivedUnique _ _ G.mapDerivedCategoryFactorsh.hom ε V
  let e := Functor.mapDerivedCategoryNatIso es ≪≫ j
  have he (P : CochainComplex C ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient _ _).obj P) =
        F.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex es (.up ℤ)).hom.app P) := by
    have hj := Functor.leftDerivedNatTrans_app G.mapDerivedCategory LF
      G.mapDerivedCategoryFactorsh.hom ε V (𝟙 _) ((HomotopyCategory.quotient _ _).obj P)
    change j.hom.app _ ≫ ε.app _ = _ at hj
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app]
    rw [Category.assoc]
    erw [hj]
    have hg : G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ _).obj P) =
        G.mapDerivedCategoryFactors.hom.app P := by
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      change G.mapDerivedCategory.map (𝟙 _) ≫
        G.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
      erw [CategoryTheory.Functor.map_id, Category.id_comp,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    rw [hg]
    simp only [NatTrans.id_app, Category.comp_id]
    exact Functor.mapDerivedCategoryNatIso_fac es P
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply LF.leftDerived_ext ε V
  apply NatTrans.ext
  funext P
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  exact (he' P).trans (he P).symm

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

attribute [-instance] SheafOfModules.instPreadditive in
/-- Identify the exact finite-free tensor model with the universal derived tensor
model, retaining its counit and the SPECIFIED completion comparison χ.
Source: the quotient-cone calculation accompanying Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: both completed coefficient maps have the same finite residue projections,
so they coincide. Their ordinary functors are canonically identified on sheafified
pure tensors. Finite freeness makes ordinary extension exact on every complex.
The universal left-derived counit therefore identifies its localization with
completedDerivedScalarExtension on every complex. The displayed normalization
uniquely determines that natural isomorphism by localization. On a good resolution,
both completion maps have the same quotient augmentation and zero shifted-product
coordinate. Their normalized descent proves the second equation. -/
theorem isomorphismScalarModel_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! e : integralOrdinaryDerivedScalar l E L ι W ≅
        completedDerivedScalarExtension l E L ι W,
      (∀ P : CochainComplex (integralTowerModules l E W) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι W P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (isomorphismScalarSheafModel l E L ι W)
                (ComplexShape.up ℤ)).hom.app P)) ∧
      e.hom ≫ completedScalarComparison l E L ι W = scalarCompletion l E L ι W := by
    let F := integralOrdinaryScalar l E L ι W
    let G := completedOrdinaryScalarExtension l E L ι W
    let es : F ≅ G := isomorphismScalarSheafModel l E L ι W
    let LF := completedDerivedScalarExtension l E L ι W
    let ε : DerivedCategory.Qh ⋙ LF ⟶
        G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
      (completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose_spec.choose_spec.2.2
        |>.choose_spec.choose
    let : PreservesFiniteLimits G := preservesFiniteLimits_of_natIso es
    let : PreservesFiniteColimits G := preservesFiniteColimits_of_natIso es
    let V := HomotopyCategory.quasiIso (integralTowerModules l E W) (.up ℤ)
    let : LF.IsLeftDerivedFunctor ε V :=
      (completedScalarChangeData l E L ι W).choose_spec.choose_spec.choose_spec.choose_spec.2.2
        |>.choose_spec.choose_spec.1
    obtain ⟨e, he0, heuniq⟩ := exactDerivedModel F G es LF ε
    have hε (P : CochainComplex (integralTowerModules l E W) ℤ) :
        completedScalarCounit l E L ι W P = ε.app
          ((HomotopyCategory.quotient (integralTowerModules l E W) (.up ℤ)).obj P) := by
      rfl
    have he (P : CochainComplex (integralTowerModules l E W) ℤ) :
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E L ι W P =
          F.mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (isomorphismScalarSheafModel l E L ι W) (.up ℤ)).hom.app P) := by
      rw [hε]
      exact he0 P
    have hc : e.inv ≫ scalarCompletion l E L ι W =
        completedScalarComparison l E L ι W := by
      apply (completedScalarComparison_existsUnique l E L ι W).unique
      · intro P
        dsimp only [NatTrans.comp_app]
        rw [Category.assoc]
        erw [(scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P]
        rw [← scalarChainModel l E L ι W]
        dsimp only [NatTrans.comp_app]
        erw [CategoryTheory.Functor.map_comp]
        apply (cancel_epi (e.hom.app (DerivedCategory.Q.obj P.obj))).mp
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
        erw [he P.obj]
        rfl
      · exact (completedScalarComparison_existsUnique l E L ι W).exists.choose_spec
    have hec : e.hom ≫ completedScalarComparison l E L ι W =
        scalarCompletion l E L ι W := by
      rw [← hc]
      simp
    refine ⟨e, ⟨he, hec⟩, ?_⟩
    intro e' he'
    apply heuniq e'
    intro P
    rw [← hε P]
    exact he'.1 P

end DerivedComparison

section TensorComparison

open AlgebraicGeometry

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem constantTransport_natural
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a)) ≫
        isoSectionwiseConstantMap.{u, u} g B =
      isoSectionwiseConstantMap.{u, u} g A ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  let W := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let I := isoSectionwiseInverseImage g RingCat.{u + 1}
  let cA := isoSectionwiseConstantMap.{u, u} g A
  let cB := isoSectionwiseConstantMap.{u, u} g B
  let aY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map a)
  let aX := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map a
  change I.map aY ≫ cB = cA ≫ W.map aX
  apply (cancel_epi (inv cA)).1
  rw [IsIso.inv_hom_id_assoc]
  let f := inv cA ≫ I.map aY ≫ cB
  change f = W.map aX
  rw [← W.map_preimage f]
  apply congrArg W.map
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj B).property
  ext U x
  change (W.map (W.preimage f)).hom.app U _ = _
  rw [W.map_preimage]
  have hcA := (isoSectionwiseConstantMap_existsUnique.{u, u} g A).exists.choose_spec
  have hcB := (isoSectionwiseConstantMap_existsUnique.{u, u} g B).exists.choose_spec
  have hi := congrArg (fun k ↦ k.hom.app U) (IsIso.hom_inv_id cA)
  have hi' := ConcreteCategory.congr_hom hi
    ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x)
  change (inv cA).hom.app U (cA.hom.app U _) = _ at hi'
  erw [hcA U.unop x] at hi'
  have hy := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app (op ((proEtaleIsoPostcompose g).obj U.unop)))
      (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))) x
  have hx := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app U)
      (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))) x
  change cB.hom.app U (aY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
    ((inv cA).hom.app U _)) = _
  erw [hi']
  change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app
      (op ((proEtaleIsoPostcompose g).obj U.unop)) (a x) =
    aY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
        (op ((proEtaleIsoPostcompose g).obj U.unop)) x) at hy
  erw [← hy, hcB U.unop (a x)]
  exact hx
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarTransport_square
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι Y)) ≫
        inverseImageCompletedCoefficientMap l L g =
      inverseImageCompletedCoefficientMap l E g ≫
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (integralCompletedScalarMap l E L ι X) := by
  let I := isoSectionwiseInverseImage g RingCat.{u + 1}
  let WX := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let WY := sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted l F W n) =
        limit.π (integralCoefficientSheafSystem l F W) (op n) := by
    ext U x
    rfl
  have hscalar (W : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
      (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W) ≫
          limit.π (integralCoefficientSheafSystem l L W) (op n) =
        limit.π (integralCoefficientSheafSystem l E W) (op n) ≫
          (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (integralScalarQuotientSheafMap l E L ι W n) := by
    have h := congrArg
      (fun a ↦ (sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)
      ((integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n)
    simpa only [integralScalarRho, integralCompletedScalarMap,
      CategoryTheory.Functor.map_comp, hproj] using h
  have hc (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      inverseImageCompletedCoefficientMap l F g ≫
          limit.π (integralCoefficientSheafSystem l F X) (op n) =
        I.map (limit.π (integralCoefficientSheafSystem l F Y) (op n)) ≫
          inverseImageFiniteCoefficientMap l F g n := by
    exact limit.lift_π _ (op n)
  apply limit.hom_ext
  intro n
  change (I.map (WY.map (integralCompletedScalarMap l E L ι Y)) ≫
      inverseImageCompletedCoefficientMap l L g) ≫
      limit.π (integralCoefficientSheafSystem l L X) (op n.unop) =
    (inverseImageCompletedCoefficientMap l E g ≫
      WX.map (integralCompletedScalarMap l E L ι X)) ≫
      limit.π (integralCoefficientSheafSystem l L X) (op n.unop)
  rw [Category.assoc, hc L n.unop, ← Category.assoc, ← I.map_comp,
    hscalar Y n.unop, I.map_comp, Category.assoc]
  rw [Category.assoc, hscalar X n.unop]
  have hce := hc E n.unop
  erw [reassoc_of% hce]
  congr 1
  exact constantTransport_natural g _

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
attribute [local irreducible] integralCompletedScalarMap inverseImageCompletedCoefficientMap

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryScalarAdjunction (W : AlgebraicGeometry.Scheme.{u}) :
    ∃ a : integralOrdinaryScalar l E L ι W ⊣
      SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralCompletedScalarMap l E L ι W)),
      ∀ (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = integralOrdinaryTensorSection l E L ι W M U 1 x := by
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralCompletedScalarMap l E L ι W)
  obtain ⟨a, ha⟩ := h (integralOrdinaryScalar l E L ι W)
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose
  refine ⟨a, ?_⟩
  intro M U x
  have h := ha M ((integralOrdinaryScalar l E L ι W).obj M)
    (eqToHom ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M).symm) U x
  simp only [eqToHom_trans, eqToHom_refl] at h
  rw [Adjunction.homEquiv_id] at h
  exact h
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem sectionwiseModuleAdjunctionNormalized {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj RY ⟶ RX)
    [IsIso c] :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    ∃ a : isoSectionwiseModuleInverseImage.{u, u} g c ⊣
      SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g)
        (shAdj.unit.app RY ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map c),
      ∀ (M : SheafOfModules.{u + 1} RY) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = M.val.map (adj.counit.app U.unop).op x := by
  dsimp only
  let F := proEtaleIsoPostcompose g
  let G := proEtaleBaseChange g
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := inv c
  let ψ := shAdj.unit.app RY ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map c
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, proEtaleSheafDirectImage, ProEtale.lowerStar, G,
      proEtaleBaseChange]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (F.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((F.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((F.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  exact ⟨SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂, fun _ _ _ ↦ rfl⟩

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem sectionwiseRestrictionSquare
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY SY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX SX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (φY : RY ⟶ SY) (φX : RX ⟶ SX)
    (cR : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        RY ⟶
      RX)
    (cS : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        SY ⟶
      SX)
    (hφ : (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        φY ≫ cS =
      cR ≫ φX) :
    let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial
    let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (ProEt.topology X) (ProEt.topology Y)
    let H := proEtaleSheafDirectImage g RingCat.{u + 1}
    let ψR := shAdj.unit.app RY ≫ H.map cR
    let ψS := shAdj.unit.app SY ≫ H.map cS
    ∃ e : SheafOfModules.restrictScalars
          φX ⋙
          SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψR ≅
        SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψS ⋙
          SheafOfModules.restrictScalars
            φY,
      ∀ (M : SheafOfModules.{u + 1} SX)
        (V : Y.ProEtᵒᵖ) (x : M.val.obj ((proEtaleBaseChange g).op.obj V)),
        (e.hom.app M).val.app V x = x := by
  dsimp only
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let H := proEtaleSheafDirectImage g RingCat.{u + 1}
  let WY := 𝟭 (Sheaf (ProEt.topology Y) RingCat.{u + 1})
  let WX := 𝟭 (Sheaf (ProEt.topology X) RingCat.{u + 1})
  let ψR := shAdj.unit.app (WY.obj RY) ≫ H.map cR
  let ψS := shAdj.unit.app (WY.obj SY) ≫ H.map cS
  have hψ : ψR ≫ H.map (WX.map φX) = WY.map φY ≫ ψS := by
    dsimp only [ψR, ψS, WY, WX, Functor.id_obj, Functor.id_map]
    rw [Category.assoc, ← H.map_comp, ← hφ, H.map_comp, ← Category.assoc]
    erw [← shAdj.unit.naturality]
    rfl
  let A := SheafOfModules.restrictScalars (WX.map φX) ⋙
    SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψR
  let B := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange g) ψS ⋙
    SheafOfModules.restrictScalars (WY.map φY)
  let e : A ≅ B := NatIso.ofComponents (fun M ↦ by
    refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
    · let P := (A.obj M).val.obj V
      let Q := (B.obj M).val.obj V
      refine
        { hom := ModuleCat.ofHom (X := P) (Y := Q)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          inv := ModuleCat.ofHom (X := Q) (Y := P)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          hom_inv_id := by ext; rfl
          inv_hom_id := by ext; rfl }
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change (WX.map φX).hom.app ((proEtaleBaseChange g).op.obj V)
            (ψR.hom.app V r) • m' = ψS.hom.app V ((WY.map φY).hom.app V r) • m'
        congr 1
        exact congrArg (fun k ↦ k.hom.app V r) hψ
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change ψS.hom.app V ((WY.map φY).hom.app V r) • m' =
          (WX.map φX).hom.app ((proEtaleBaseChange g).op.obj V) (ψR.hom.app V r) • m'
        congr 1
        exact (congrArg (fun k ↦ k.hom.app V r) hψ).symm
    · intro V W i
      ext m
      rfl) (by
        intro M N f
        ext V m
        rfl)
  exact ⟨e, fun _ _ _ ↦ rfl⟩

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem tensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (A : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hA : A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
    (U : W.ProEtᵒᵖ) (a : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)) =
      a • ((eqToHom hA.symm).val.app U
        ((toSheafify (ProEt.topology W)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x))) := by
  subst A
  let k := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)).app U ≫
      (ModuleCat.restrictScalarsId (S.obj.obj U)).hom.app _
  change k (a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) =
    a • k ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)
  have ht : a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      a • ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x) := by
    change a ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x =
      (a * 1) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x
    rw [mul_one]
  rw [ht]
  exact k.hom.map_smul a _

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_smul (W : AlgebraicGeometry.Scheme.{u})
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    integralOrdinaryTensorSection l E L ι W M U a x =
      a • integralOrdinaryTensorSection l E L ι W M U 1 x := by
  exact tensorSection_smul W (integralCompletedScalarMap l E L ι W) M _
    ((integralOrdinaryScalarWitness l E L ι W).choose_spec.choose M) U a x

universe v

private theorem unit_triangle_normalization
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (H : D ⥤ C) (a : F ⊣ H)
    (M N : Dᵒᵖ ⥤ Type v) (τ : F.op ⋙ M ⟶ F.op ⋙ N)
    (v : ∀ V : Dᵒᵖ, M.obj V → N.obj V)
    (hbase : ∀ (V : Dᵒᵖ) (x : M.obj V),
      τ.app (op (H.obj V.unop)) (M.map (a.counit.app V.unop).op x) =
        N.map (a.counit.app V.unop).op (v V x)) :
    ∀ (U : C) (y : M.obj (op (F.obj U))), τ.app (op U) y = v (op (F.obj U)) y := by
  intro U y
  let h := a.unit.app U
  let y' := M.map (a.counit.app (F.obj U)).op y
  have hn := ConcreteCategory.congr_hom (τ.naturality h.op) y'
  change τ.app (op U) (M.map (F.map h).op y') =
    N.map (F.map h).op (τ.app (op (H.obj (F.obj U))) y') at hn
  rw [hbase (op (F.obj U)) y] at hn
  have ht : (a.counit.app (F.obj U)).op ≫ (F.map h).op = 𝟙 _ := by
    dsimp only [h, Functor.id_obj, Functor.comp_obj]
    rw [← op_comp]
    change (F.map (a.unit.app U) ≫ a.counit.app (F.obj U)).op = (𝟙 (F.obj U)).op
    exact congrArg (fun f : F.obj U ⟶ F.obj U ↦ f.op) (a.left_triangle_components U)
  have hm := ConcreteCategory.congr_hom
    (M.map_comp (a.counit.app (F.obj U)).op (F.map h).op) y
  have hn' := ConcreteCategory.congr_hom (N.map_comp (a.counit.app (F.obj U)).op (F.map h).op)
    (v (op (F.obj U)) y)
  rw [ht, M.map_id] at hm
  rw [ht, N.map_id] at hn'
  change y = M.map (F.map h).op y' at hm
  change v (op (F.obj U)) y =
    N.map (F.map h).op (N.map (a.counit.app (F.obj U)).op (v (op (F.obj U)) y)) at hn'
  rw [← hm, ← hn'] at hn
  exact hn

private theorem adjointSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    {R₁ : B ⥤ A} {R₂ : D ⥤ B} {S₁ : C ⥤ A} {S₂ : D ⥤ C}
    (aR : F₁ ⊣ R₁) (aX : F₂ ⊣ R₂) (aY : G₁ ⊣ S₁) (aS : G₂ ⊣ S₂)
    (s : R₂ ⋙ R₁ ≅ S₂ ⋙ S₁) :
    ∃ b : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂, ∀ M,
      ((aR.comp aX).ofNatIsoRight s).unit.app M ≫
        (S₂ ⋙ S₁).map (b.hom.app M) = (aY.comp aS).unit.app M := by
  let a := (aR.comp aX).ofNatIsoRight s
  exact ⟨a.leftAdjointUniq (aY.comp aS), fun M ↦
    a.unit_leftAdjointUniq_hom_app (aY.comp aS) M⟩

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem sectionwiseTensorUnit
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (RY SY : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (RX SX : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (φY : RY ⟶ SY) (φX : RX ⟶ SX)
    (cR : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        RY ⟶
      RX)
    [IsIso cR]
    (cS : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        SY ⟶
      SX)
    [IsIso cS]
    (hφ : (isoSectionwiseInverseImage g RingCat.{u + 1}).map
        φY ≫ cS =
      cR ≫ φX)
    (FX : SheafOfModules.{u + 1} RX ⥤
      SheafOfModules.{u + 1} SX)
    (FY : SheafOfModules.{u + 1} RY ⥤
      SheafOfModules.{u + 1} SY)
    (aX : FX ⊣ SheafOfModules.restrictScalars φX)
    (aY : FY ⊣ SheafOfModules.restrictScalars φY) :
    ∃ b : isoSectionwiseModuleInverseImage.{u, u} g cR ⋙ FX ≅
        FY ⋙ isoSectionwiseModuleInverseImage.{u, u} g cS,
      ∀ (M : SheafOfModules.{u + 1} RY) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app
            (op U) y) =
          (aY.unit.app M).val.app (op ((proEtaleIsoPostcompose g).obj U)) y := by
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  obtain ⟨aR, haR⟩ := sectionwiseModuleAdjunctionNormalized g
    RY
    RX cR
  obtain ⟨aS, haS⟩ := sectionwiseModuleAdjunctionNormalized g
    SY
    SX cS
  obtain ⟨s, hs⟩ := sectionwiseRestrictionSquare g RY SY RX SX φY φX cR cS hφ
  obtain ⟨b, hb⟩ := adjointSquare aR aX aY aS s
  have hOne (M : SheafOfModules.{u + 1} RY)
      (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
      (b.hom.app M).val.app ((proEtaleBaseChange g).op.obj V)
        ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app
          ((proEtaleBaseChange g).op.obj V) (M.val.map (adj.counit.app V.unop).op x)) =
      (FY.obj M).val.map (adj.counit.app V.unop).op ((aY.unit.app M).val.app V x) := by
    have h := hb M
    have h' := congrArg (fun k ↦ k.val.app V x) h
    change (b.hom.app M).val.app ((proEtaleBaseChange g).op.obj V)
      ((s.hom.app (FX.obj ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M))).val.app V
        ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app
          ((proEtaleBaseChange g).op.obj V) ((aR.unit.app M).val.app V x))) =
      (aS.unit.app (FY.obj M)).val.app V ((aY.unit.app M).val.app V x) at h'
    rw [hs, haR, haS] at h'
    exact h'
  refine ⟨b, ?_⟩
  intro M U y
  let F := proEtaleIsoPostcompose g
  let M' := M.val.presheaf ⋙ forget Ab
  let N' := (FY.obj M).val.presheaf ⋙ forget Ab
  let τ : F.op ⋙ M' ⟶ F.op ⋙ N' :=
    { app := fun V ↦ TypeCat.ofHom (fun x ↦ (b.hom.app M).val.app V
        ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app V x))
      naturality := by
        intro V V' f
        apply ConcreteCategory.hom_ext
        intro x
        have hu := PresheafOfModules.naturality_apply
          (aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val f x
        have hb' := PresheafOfModules.naturality_apply (b.hom.app M).val f
          ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app V x)
        change (b.hom.app M).val.app V'
          ((aX.unit.app ((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M)).val.app V'
            (((isoSectionwiseModuleInverseImage.{u, u} g cR).obj M).val.map f x)) = _
        erw [hu]
        exact hb' }
  exact unit_triangle_normalization F (proEtaleBaseChange g) adj M' N' τ
    (fun V x ↦ (aY.unit.app M).val.app V x) (hOne M) U y

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem tensorIso_one_exists
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃ b : inverseImageIntegralModules l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U) 1 y) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) 1 y := by
  obtain ⟨aY, haY⟩ := ordinaryScalarAdjunction l E L ι Y
  obtain ⟨aX, haX⟩ := ordinaryScalarAdjunction l E L ι X
  obtain ⟨b, hb⟩ := sectionwiseTensorUnit g
    (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficientSheafUnrestricted l L Y)
    (completedIntegralCoefficientSheafUnrestricted l E X)
    (completedIntegralCoefficientSheafUnrestricted l L X)
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap l E L ι Y))
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralCompletedScalarMap l E L ι X))
    (inverseImageCompletedCoefficientMap l E g) (inverseImageCompletedCoefficientMap l L g)
    (scalarTransport_square l E L ι g)
    (integralOrdinaryScalar l E L ι X) (integralOrdinaryScalar l E L ι Y) aX aY
  refine ⟨b, ?_⟩
  intro M U y
  have h := hb M U y
  erw [haX, haY] at h
  exact h


attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
/-- The sectionwise tensor comparison is uniquely fixed on every local pure tensor.
Here U maps to (U,g∘u), so the underlying section y is literally y₀, and the target
scalar c_L(g⁻¹a₀) is the displayed completed coefficient map applied to a₀.
Source: inverse-image tensor comparison and Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: inverse-image tensor compatibility sends the transported pure tensor to the
same tensor on (U,g∘u). The coefficient projection equations make it balanced over
R_E, and c_L gives its R_L-linearity. The reverse tensor rule is its inverse.
Restrictions and module maps commute with the formula. Sheafification extends
these maps; local generation by pure tensors proves uniqueness. -/
theorem isomorphismScalarTensor_existsUnique
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! b : inverseImageIntegralModules l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U)
            ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a) y) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a y := by
  obtain ⟨b, hb⟩ := tensorIso_one_exists l E L ι g
  refine ⟨b, ?_, ?_⟩
  · intro M U y a
    let c := inverseImageCompletedCoefficientMap l L g
    let z : (((inverseImageIntegralModules l L g).obj
        ((integralOrdinaryScalar l E L ι Y).obj M)).val.obj (op U)) :=
      integralOrdinaryTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U)) 1 y
    calc
      _ = c.hom.app (op U) a • ((b.hom.app M).val.app (op U)
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U) 1 y)) := by
        rw [ordinaryTensorSection_smul]
        exact ((b.hom.app M).val.app (op U)).hom.map_smul _ _
      _ = c.hom.app (op U) a • z := congrArg (fun z ↦ c.hom.app (op U) a • z) (hb M U y)
      _ = a • integralOrdinaryTensorSection l E L ι Y M
          (op ((proEtaleIsoPostcompose g).obj U)) 1 y := by
        change (inv c).hom.app (op U) (c.hom.app (op U) a) •
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) 1 y = _
        have hi := congrArg (fun f ↦ f.hom.app (op U) a) (IsIso.hom_inv_id c)
        change (inv c).hom.app (op U) (c.hom.app (op U) a) = a at hi
        rw [hi]
      _ = _ := (ordinaryTensorSection_smul l E L ι Y M _ a y).symm
  · intro b' hb'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply tensorModel_hom_ext X (integralCompletedScalarMap l E L ι X)
      ((inverseImageIntegralModules l E g).obj M) _ _
      ((integralOrdinaryScalarWitness l E L ι X).choose_spec.choose _)
    intro U a x
    change (b'.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) U a x) =
      (b.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) U a x)
    have h' : (b'.hom.app M).val.app U
        (integralOrdinaryTensorSection l E L ι X
          ((inverseImageIntegralModules l E g).obj M) U 1 x) =
      integralOrdinaryTensorSection l E L ι Y M
        (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x := by
      simpa only [map_one] using hb' M U.unop x 1
    calc
      _ = a • ((b'.hom.app M).val.app U
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)) := by
        rw [ordinaryTensorSection_smul]
        exact ((b'.hom.app M).val.app U).hom.map_smul a
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)
      _ = a • ((b.hom.app M).val.app U
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)) := by
        rw [h', hb]
      _ = _ := by
        conv_rhs => rw [ordinaryTensorSection_smul]
        exact (((b.hom.app M).val.app U).hom.map_smul a
          (integralOrdinaryTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) U 1 x)).symm

end TensorComparison

/-- The actual tensor isomorphism b on sheaves, fixed by its local tensor rule.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarTensor {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :=
  (isomorphismScalarTensor_existsUnique l E L ι g).exists.choose

/-- Exact inverse image and finite-free extension descend this same tensor isomorphism.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismScalarTensorDerived {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralDerived l E g ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ inverseImageIntegralDerived l L g :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
    (integralOrdinaryScalar l E L ι X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (isomorphismScalarTensor l E L ι g) ≪≫
    Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L ι Y)
      (inverseImageIntegralModules l L g)

/-- Both inputs to the X-side completion comparisons lie in the recorded bounded
constructible, derived-complete category. Source: Bhatt--Scholze 6.5.9(4), and the
isomorphism-derived-pullback assertion
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the sectionwise inverse-image equivalence transports the coefficient actions,
finite quotient reductions, and their constructible partitions. Exactness transports
cohomology and its common finite interval. It commutes with the quotient-unit Roos
triangle, giving completeness of inverse image. The recorded completed pullback is
naturally identified with that inverse image on these objects by
lem-weil-isomorphism-derived-pullback. This identification preserves the constructible
and completeness predicates, giving the second clause. -/
theorem isomorphismComparisonInputs_constructible
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (_hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((inverseImageIntegralDerived l E g).obj K) ∧
      sfIntegralConstructible l E X ((integralDerivedPullback l E g).obj K) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (_hX x).map (IsLocalRing.residue (X.presheaf.stalk x)) |>.invertible
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (_hY y).map (IsLocalRing.residue (Y.presheaf.stalk y)) |>.invertible
  have hF := ((integralOperations_preserve_constructible l E g).1 K _hK).1
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨D, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let T := (D.coefficient E).system Y
  let := (D.coefficient E).complete Y ⟨K, _hK⟩
  have hu : IsIso (S.adjunction.unit.app K) := by
    have h := T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction K
    rw [← h]
    infer_instance
  let := hu
  obtain ⟨κ, hk, _, hn, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g _hX _hY
  obtain ⟨θ, hθ⟩ := hn S hS
  have : IsIso (κ.app K) := by
    rw [hθ K]
    infer_instance
  let := sfIntegralConstructible_isClosedUnderIsomorphisms l E X
  exact ⟨(sfIntegralConstructible l E X).prop_of_iso (asIso (κ.app K)).symm hF, hF⟩

/-- α is tensor associativity followed by the strict quotient completion comparisons:
the recorded `scalarPullbackCompleted` of the scalar-operation lemma, whose completeness
inputs come from hK and the constructibility theorem above.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismComparisonScalarAlpha {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).obj ((integralDerivedPullback l E g).obj K) ⟶
      (integralDerivedPullback l L g).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarPullbackCompleted l E L ι g K hK.1
    (isomorphismComparisonInputs_constructible l E g hX hY K hK).2.1).hom

/-- β = G_L(χ_Y) ∘ b ∘ χ_X⁻¹, using the specified completion comparison.
Source: Bhatt--Scholze 6.5.9(4)
(blueprint: lem-weil-isomorphism-comparison-scalar-extension). -/
def isomorphismComparisonScalarBeta {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).obj ((inverseImageIntegralDerived l E g).obj K) ⟶
      (inverseImageIntegralDerived l L g).obj ((integralScalarExtension l E L ι Y).obj K) :=
  (scalarCompletionIso l E L ι X ((inverseImageIntegralDerived l E g).obj K)
    ((isomorphismComparisonInputs_constructible l E g hX hY K hK).1.1)).inv ≫
    (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
    (inverseImageIntegralDerived l L g).map ((scalarCompletion l E L ι Y).app K)

section ComparisonSquare

universe r s
open AlgebraicGeometry

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_map (W : Scheme.{u})
    {M N : integralTowerModules l E W} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U) :
    (((integralOrdinaryScalar l E L ι W).map f).val.app U)
        (integralOrdinaryTensorSection l E L ι W M U 1 x) =
      integralOrdinaryTensorSection l E L ι W N U 1 (f.val.app U x) := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  have h := congrArg (fun k ↦ k.val.app U x) (a.unit.naturality f)
  change ((a.unit.app N).val.app U) (f.val.app U x) =
    (((integralOrdinaryScalar l E L ι W).map f).val.app U)
      ((a.unit.app M).val.app U x) at h
  rw [ha, ha] at h
  exact h.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem ordinaryTensorSection_restrict (W : Scheme.{u})
    (M : integralTowerModules l E W) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) :
    (((integralOrdinaryScalar l E L ι W).obj M).val.map f)
        (integralOrdinaryTensorSection l E L ι W M U 1 x) =
      integralOrdinaryTensorSection l E L ι W M V 1 (M.val.map f x) := by
  obtain ⟨a, ha⟩ := ordinaryScalarAdjunction l E L ι W
  have h := PresheafOfModules.naturality_apply (a.unit.app M).val f x
  change (a.unit.app M).val.app V (M.val.map f x) =
    (((integralOrdinaryScalar l E L ι W).obj M).val.map f)
      ((a.unit.app M).val.app U x) at h
  rw [ha, ha] at h
  exact h.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarThetaSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (inverseImageReductionTheta l E g n P) ≫
        (scalarPullbackLevel l E L ι g n).app P =
      ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
        (.up ℤ)).hom.app P) ≫ inverseImageReductionTheta l L g n
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply tensorModel_hom_ext X (integralCompletedScalarMap l E L ι X)
    ((inverseImageIntegralModules l E g).obj (P.X i)) _ _
    ((integralOrdinaryScalarWitness l E L ι X).choose_spec.choose _)
  intro U a x
  let M := ((inverseImageIntegralModules l E g).obj (P.X i))
  let f := (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
    (inverseImageReductionTheta l E g n P) ≫ (scalarPullbackLevel l E L ι g n).app P).f i
  let h := (((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
    (.up ℤ)).hom.app P) ≫ inverseImageReductionTheta l L g n
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)).f i
  change f.val.app U (integralOrdinaryTensorSection l E L ι X M U a x) =
    h.val.app U (integralOrdinaryTensorSection l E L ι X M U a x)
  suffices hf : f.val.app U (integralOrdinaryTensorSection l E L ι X M U 1 x) =
      h.val.app U (integralOrdinaryTensorSection l E L ι X M U 1 x) by
    rw [ordinaryTensorSection_smul]
    simpa only [map_smul] using congrArg (fun z ↦ a • z) hf
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let q := (proEtaleIsoCommaArrow g U.unop).op
  have hθ := (inverseImageReductionTheta_existsUnique l E g n P).exists.choose_spec
    i U.unop x
  have hb := (isomorphismScalarTensor_existsUnique l E L ι g).exists.choose_spec
    (P.X i) U.unop x 1
  simp only [map_one] at hb
  have hθ' := (inverseImageReductionTheta_existsUnique l L g n
    (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)
    ).exists.choose_spec i U.unop
      (integralOrdinaryTensorSection l E L ι Y (P.X i) (op V) 1 x)
  change (((scalarPullbackLevel l E L ι g n).app P).f i).val.app U
      ((((integralOrdinaryScalar l E L ι X).map
        ((inverseImageReductionTheta l E g n P).f i)).val.app U)
          (integralOrdinaryTensorSection l E L ι X M U 1 x)) =
    ((inverseImageReductionTheta l L g n
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P)).f i
      ).val.app U (((isomorphismScalarTensor l E L ι g).hom.app (P.X i)).val.app U
        (integralOrdinaryTensorSection l E L ι X M U 1 x))
  erw [ordinaryTensorSection_map, hθ, hb, hθ']
  erw [← ordinaryTensorSection_restrict]
  have hn := PresheafOfModules.naturality_apply
    (((scalarPullbackLevel l E L ι g n).app P).f i).val q
      (integralOrdinaryTensorSection l E L ι X
        (((integralOperationsPullbackLevel l E g n).obj P).X i)
        (op ((proEtaleBaseChange g).obj V)) 1
          (integralOperationsPullbackGenerator l E g n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
            (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x)))
  erw [hn]
  congr 1
  exact (scalarPullbackLevel_existsUnique l E L ι g n).exists.choose_spec P i V x

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem zero_lift_f
    {A : Type r} [Category.{s} A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (α : M ⟶ K)
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0) (i : ℤ) :
    (CochainComplex.mappingCocone.lift φ α 0 h).f i = α.f i ≫
      HomologicalComplex.homotopyCofiber.inlX φ i (i + (-1))
        (by change i + (-1) + 1 = i; omega) := by
  simp only [CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ i _ _ (i + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  erw [Category.comp_id]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem zero_lift_naturality
    {A : Type r} [Category.{s} A] [Abelian A]
    {K L M N : CochainComplex A ℤ} (φ : K ⟶ K) (ψ : L ⟶ L)
    (a : K ⟶ L) (ha : φ ≫ a = a ≫ ψ) (f : M ⟶ N) (α : M ⟶ K) (β : N ⟶ L)
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M K (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ φ) = 0)
    (hβ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain N L (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (β ≫ ψ) = 0)
    (hn : f ≫ β = α ≫ a) :
    f ≫ CochainComplex.mappingCocone.lift ψ β 0 hβ =
      CochainComplex.mappingCocone.lift φ α 0 hα ≫
        (shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom φ ψ
            (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
            (Arrow.homMk a a ha.symm)) := by
  ext i : 1
  dsimp only [HomologicalComplex.comp_f]
  rw [zero_lift_f, zero_lift_f, CochainComplex.shiftFunctor_map_f']
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  simpa only [HomologicalComplex.comp_f, Category.assoc, Arrow.homMk_left] using
    congrArg (fun k ↦ k.f i ≫ HomologicalComplex.homotopyCofiber.inlX ψ
      i (i + (-1)) (by change i + (-1) + 1 = i; omega)) hn


attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem cocone_hom_ext
    {A : Type*} [Category A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L) (f h : M ⟶ CochainComplex.mappingCocone φ)
    (hf : f ≫ CochainComplex.mappingCocone.fst φ = h ≫ CochainComplex.mappingCocone.fst φ)
    (hs : ∀ i j (hij : i + -1 = j),
      f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i j hij =
        h.f i ≫ (CochainComplex.mappingCocone.snd φ).v i j hij) : f = h := by
  ext i : 1
  have hfi := congrArg (fun z ↦ z.f i) hf
  change f.f i ≫ _ = h.f i ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  have hfid := congrArg (fun z ↦ f.f i ≫ z) hid
  have hhid := congrArg (fun z ↦ h.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at hfid hhid
  rw [hfi, hs i (i - 1) (by omega)] at hfid
  exact hfid.symm.trans hhid

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem roos_additive_augmentation
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (P : CochainComplex A ℤ) (α : P ⟶ ∏ᶜ fun n ↦ C.obj (op n))
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ fun n ↦ C.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ scalarRoosBoundary C) = 0)
    (lam : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
      ∏ᶜ fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n))
    (hlam : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain ((F.mapHomologicalComplex (.up ℤ)).obj P)
          (∏ᶜ fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (lam ≫ scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) = 0)
    (hlamn : ∀ n, lam ≫ Pi.π _ n =
      (F.mapHomologicalComplex (.up ℤ)).map (α ≫ Pi.π _ n)) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα) ≫
        scalarRoosMap F C =
      CochainComplex.mappingCocone.lift
        (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) lam 0 hlam := by
  apply cocone_hom_ext
  · apply Pi.hom_ext
    intro n
    erw [Category.assoc, Category.assoc,
      (scalarRoosMap_existsUnique F C).exists.choose_spec.1 n]
    erw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
      CochainComplex.mappingCocone.lift_fst]
    erw [CochainComplex.mappingCocone.lift_fst]
    exact (hlamn n).symm
  · intro i j hij
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval B (.up ℤ) j)
      (fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n))).hom_ext
    rintro ⟨n⟩
    simp only [HomologicalComplex.comp_f, Category.assoc]
    change ((F.mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα)).f i ≫
      (scalarRoosMap F C).f i ≫
      (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v i j hij ≫
      (Pi.π (fun n ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n)) n).f j = _
    erw [(scalarRoosMap_existsUnique F C).exists.choose_spec.2 i j hij n]
    change F.map ((CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα).f i) ≫
      F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j hij ≫
        (Pi.π (fun n ↦ C.obj (op n)) n).f j) = _
    erw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
      CochainComplex.mappingCocone.lift_f_snd_v]
    simp


attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem roos_natural_augmentation
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (C' : ℕᵒᵖ ⥤ CochainComplex B ℤ) (P : CochainComplex A ℤ)
    (P' : CochainComplex B ℤ) (α : P ⟶ ∏ᶜ fun n ↦ C.obj (op n))
    (β : P' ⟶ ∏ᶜ fun n ↦ C'.obj (op n))
    (hα : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ fun n ↦ C.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (α ≫ scalarRoosBoundary C) = 0)
    (hβ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P' (∏ᶜ fun n ↦ C'.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (β ≫ scalarRoosBoundary C') = 0)
    (b : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ P')
    (d : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C')
    (hf : ∀ n, (F.mapHomologicalComplex (.up ℤ)).map (α ≫ Pi.π _ n) ≫ d.app (op n) =
      b ≫ β ≫ Pi.π _ n) :
    (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 hα) ≫
        scalarRoosMap F C ≫ integralOperationsRoosMap d =
      b ≫ CochainComplex.mappingCocone.lift (scalarRoosBoundary C') β 0 hβ := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let lam : FC.obj P ⟶ ∏ᶜ fun n ↦ (C ⋙ FC).obj (op n) :=
    Pi.lift (fun n ↦ FC.map (α ≫ Pi.π _ n))
  have hlamn (n : ℕ) : lam ≫ Pi.π _ n = FC.map (α ≫ Pi.π _ n) := Pi.lift_π _ n
  have hα₀ : α ≫ scalarRoosBoundary C = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
      CochainComplex.HomComplex.Cochain.ofHom_zero] using hα
  have hcompat (n : ℕ) : α ≫ Pi.π _ n =
      α ≫ Pi.π _ (n + 1) ≫ integralOperationsTowerStep C n := by
    have h := congrArg (fun z ↦ z ≫ Pi.π (fun n ↦ C.obj (op n)) n) hα₀
    have h' : α ≫ Pi.π _ n - α ≫ Pi.π _ (n + 1) ≫
        integralOperationsTowerStep C n = 0 := by
      simpa only [scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Category.comp_id,
        Category.assoc, Pi.lift_π, Limits.zero_comp] using h
    exact sub_eq_zero.mp h'
  have hlamφ : lam ≫ scalarRoosBoundary (C ⋙ FC) = 0 := by
    apply Pi.hom_ext
    intro n
    have hφ := (towerTransitionEndomorphism_eq_iff
      (K := fun n ↦ (C ⋙ FC).obj (op n))
      (integralOperationsTowerStep (C ⋙ FC)) (scalarRoosBoundary (C ⋙ FC))).mp rfl n
    erw [Category.assoc, hφ, Preadditive.comp_sub, ← Category.assoc, hlamn, hlamn]
    have hc : FC.map (α ≫ Pi.π _ (n + 1)) ≫ FC.map (integralOperationsTowerStep C n) =
        FC.map (α ≫ Pi.π _ n) := by
      rw [← CategoryTheory.Functor.map_comp, Category.assoc, ← hcompat]
    simp only [Limits.zero_comp]
    dsimp only [integralOperationsTowerStep, Functor.comp_map]
    change FC.map (α ≫ Pi.π _ n) -
      FC.map (α ≫ Pi.π _ (n + 1)) ≫ FC.map (integralOperationsTowerStep C n) = 0
    rw [hc, sub_self]
  have hlam : CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain (FC.obj P)
        (∏ᶜ fun n ↦ (C ⋙ FC).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom (lam ≫ scalarRoosBoundary (C ⋙ FC)) = 0 := by
    simp [hlamφ]
  have h₁ := roos_additive_augmentation F C P α hα lam hlam hlamn
  have hlamd : lam ≫ Limits.Pi.map (fun n ↦ d.app (op n)) = b ≫ β := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π]
    erw [← Category.assoc, hlamn]
    exact hf n
  have h₂ := zero_lift_naturality (scalarRoosBoundary (C ⋙ FC)) (scalarRoosBoundary C')
    (Limits.Pi.map (fun n ↦ d.app (op n))) (integralOperationsRoos_square d)
    b lam β hlam hβ hlamd.symm
  rw [← Category.assoc, h₁]
  exact h₂.symm

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarRoosSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (inverseImageRoosComparisonComplex l E g P) ≫ scalarPullbackChain l E L ι g P =
      ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
        (.up ℤ)).hom.app P) ≫ inverseImageRoosComparisonComplex l L g
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  let F := integralOrdinaryScalar l E L ι X
  let FC := F.mapHomologicalComplex (.up ℤ)
  let C := (integralOperationsPullbackTowerFunctor l E g).obj P
  let Q := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P
  let C' := (integralOperationsPullbackTowerFunctor l L g).obj Q
  let d := (scalarPullbackTower l E L ι g).app P
  let b := ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
    (.up ℤ)).hom.app P)
  change FC.map (inverseImageRoosComparisonComplex l E g P) ≫
    scalarRoosMap F C ≫ integralOperationsRoosMap d = _
  apply roos_natural_augmentation F C C'
    (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P)
    (((inverseImageIntegralModules l L g).mapHomologicalComplex (.up ℤ)).obj Q)
    (inverseImageReductionProduct l E g P) (inverseImageReductionProduct l L g Q)
    (inverseImageReductionProduct_lift_condition l E g P)
    (inverseImageReductionProduct_lift_condition l L g Q) b d
  intro n
  have h := scalarThetaSquare l E L ι g n P
  have hd := (scalarPullbackTower_existsUnique l E L ι g).exists.choose_spec P n
  erw [inverseImageReductionProduct, Pi.lift_π, hd,
    inverseImageReductionProduct, Pi.lift_π]
  exact h


attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem derivedSquare_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ C) (G₂ : C ⥤ D)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app
    (DerivedCategory.Q.obj P))).1
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc,
    ← Functor.mapDerivedCategoryNatIso_fac e P]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem completionSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (GE PE : A ⥤ B) (Gₗ Pₗ : C ⥤ D) (CX TX : B ⥤ D) (CY TY : A ⥤ C)
    (κE : GE ⟶ PE) (κL : Gₗ ⟶ Pₗ) (χX : CX ⟶ TX) (χY : CY ⟶ TY)
    (α : PE ⋙ CX ⟶ CY ⋙ Pₗ) (b : GE ⋙ CX ⟶ CY ⋙ Gₗ) (K : A)
    [IsIso (χX.app (GE.obj K))] [IsIso (χX.app (PE.obj K))]
    (h : CX.map (κE.app K) ≫ α.app K = b.app K ≫ κL.app (CY.obj K)) :
    TX.map (κE.app K) ≫ inv (χX.app (PE.obj K)) ≫ α.app K ≫ Pₗ.map (χY.app K) =
      inv (χX.app (GE.obj K)) ≫ b.app K ≫ Gₗ.map (χY.app K) ≫ κL.app (TY.obj K) := by
  apply (cancel_epi (χX.app (GE.obj K))).1
  simp only [← Category.assoc]
  rw [← χX.naturality (κE.app K)]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, κL.naturality]

attribute [-instance] SheafOfModules.instPreadditive in
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem goodRepresentative_exists (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (integralTowerModules.{u, u} l E W)) :
    ∃ P : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let A : CochainComplex (integralTowerModules.{u, u} l E W) ℤ :=
    DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
    (C := W.ProEt) (J := ProEt.topology W)
    (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) A
  let P := h.choose
  let p := h.choose_spec.choose
  let hp := h.choose_spec.choose_spec
  let : QuasiIso p := hp.2.2.1
  exact ⟨⟨P, hp.1, fun i ↦
    (exactFunctor (integralTowerModules.{u, u} l E W)
      (integralTowerModules.{u, u} l E W)).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (P.X i)).symm
      (hp.2.1 i)⟩,
    ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩


attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem natTrans_eq_of_representatives
    {A B D : Type*} [Category A] [Category B] [Category D]
    (Q : A ⥤ B) (hQ : ∀ K : B, ∃ P : A, Nonempty (Q.obj P ≅ K))
    {F G : B ⥤ D} (α β : F ⟶ G) (h : ∀ P : A, α.app (Q.obj P) = β.app (Q.obj P)) :
    α = β := by
  ext K
  obtain ⟨P, ⟨e⟩⟩ := hQ K
  apply (cancel_epi (F.map e.hom)).mp
  rw [α.naturality, β.naturality, h P]

attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarDerivedSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hstrict : ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
      ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
          (inverseImageRoosComparisonComplex l E g P) ≫ scalarPullbackChain l E L ι g P =
        ((NatIso.mapHomologicalComplex (isomorphismScalarTensor l E L ι g)
          (.up ℤ)).hom.app P) ≫ inverseImageRoosComparisonComplex l L g
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P))
    (K : DerivedCategory (integralTowerModules l E Y)) :
    (integralOrdinaryDerivedScalar l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
        (scalarPullbackOrdinary l E L ι g).hom.app K =
      (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
        inverseImagePullbackComparisonDerived l L g hX hY
          ((integralOrdinaryDerivedScalar l E L ι Y).obj K) := by
  obtain ⟨κE, hκE, hresE, -, -⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  obtain ⟨κL, hκL, hresL, -, -⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l L g hX hY
  let FX := integralOrdinaryScalar l E L ι X
  let FY := integralOrdinaryScalar l E L ι Y
  let GE := inverseImageIntegralModules l E g
  let Gₗ := inverseImageIntegralModules l L g
  let α := (scalarPullbackOrdinary l E L ι g).hom
  let b := (isomorphismScalarTensorDerived l E L ι g).hom
  let A := Functor.whiskerRight κE FX.mapDerivedCategory ≫ α
  let B := b ≫ Functor.whiskerLeft FY.mapDerivedCategory κL
  have hAB : A = B := by
    apply natTrans_eq_of_representatives (integralOperationsGoodLocalization l E Y)
      (goodRepresentative_exists l E Y) A B
    intro P
    change FX.mapDerivedCategory.map (κE.app (DerivedCategory.Q.obj P.obj)) ≫
        α.app (DerivedCategory.Q.obj P.obj) =
      b.app (DerivedCategory.Q.obj P.obj) ≫
        κL.app (FY.mapDerivedCategory.obj (DerivedCategory.Q.obj P.obj))
    let Q := (FY.mapHomologicalComplex (.up ℤ)).obj P.obj
    let Qgood : (integralOperationsGoodComplex l L Y).FullSubcategory :=
      ⟨Q, scalarGood l E L ι Y P⟩
    have hkE : κE.app (DerivedCategory.Q.obj P.obj) =
        GE.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
            (integralDerivedPullbackComparison l E g).inv.app P := by
      rw [hresE P.obj P (𝟙 _)]
      dsimp only [inverseImagePullbackComparison, integralOperationsPullbackOnGood,
        integralOperationsGoodLocalization, Functor.comp_obj, GE]
      simp only [CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    have hkL : κL.app (DerivedCategory.Q.obj Q) =
        Gₗ.mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q) ≫
            (integralDerivedPullbackComparison l L g).inv.app Qgood := by
      rw [hresL Q Qgood (𝟙 _)]
      dsimp only [inverseImagePullbackComparison, integralOperationsPullbackOnGood,
        integralOperationsGoodLocalization, Functor.comp_obj, Gₗ, Qgood]
      simp only [CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    have heκ : FX.mapDerivedCategory.map (κE.app (DerivedCategory.Q.obj P.obj)) ≫
        FX.mapDerivedCategory.map ((integralDerivedPullbackComparison l E g).hom.app P) =
      FX.mapDerivedCategory.map (GE.mapDerivedCategoryFactors.hom.app P.obj) ≫
        FX.mapDerivedCategory.map
          (DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj)) := by
      rw [hkE]
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have hlκ : κL.app (DerivedCategory.Q.obj Q) ≫
        (integralDerivedPullbackComparison l L g).hom.app Qgood =
      Gₗ.mapDerivedCategoryFactors.hom.app Q ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q) := by
      rw [hkL]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have hα := (scalarPullbackOrdinary_existsUnique l E L ι g).exists.choose_spec P
    have hf := FX.mapDerivedCategoryFactors.hom.naturality
      (inverseImageRoosComparisonComplex l E g P.obj)
    dsimp only [Functor.comp_map] at hf
    have hb := derivedSquare_factors GE FX FY Gₗ (isomorphismScalarTensor l E L ι g) P.obj
    have hQ := congrArg DerivedCategory.Q.map (hstrict P.obj)
    simp only [CategoryTheory.Functor.map_comp] at hQ
    have hn := κL.naturality (FY.mapDerivedCategoryFactors.hom.app P.obj)
    apply (cancel_mono ((integralDerivedPullback l L g).map
      (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫
      (integralDerivedPullbackComparison l L g).hom.app Qgood)).1
    simp only [Category.assoc]
    erw [← hα]
    erw [← Category.assoc, ← Category.assoc, heκ]
    simp only [Category.assoc]
    erw [reassoc_of% hf]
    have hQ' := congrArg (fun z ↦
      FX.mapDerivedCategory.map (GE.mapDerivedCategoryFactors.hom.app P.obj) ≫
        FX.mapDerivedCategoryFactors.hom.app ((GE.mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
          z) hQ
    refine hQ'.trans ?_
    calc
      _ = b.app (DerivedCategory.Q.obj P.obj) ≫
          Gₗ.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫
          Gₗ.mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q) := by
        dsimp only [b, isomorphismScalarTensorDerived, Functor.mapDerivedCategorySquareIso,
          FX, FY, GE, Gₗ, Q] at hb ⊢
        simpa only [Category.assoc] using! congrArg
          (fun z ↦ z ≫ DerivedCategory.Q.map (inverseImageRoosComparisonComplex l L g Q)) hb
      _ = b.app (DerivedCategory.Q.obj P.obj) ≫
          Gₗ.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫
          κL.app (DerivedCategory.Q.obj Q) ≫
          (integralDerivedPullbackComparison l L g).hom.app Qgood :=
        congrArg (fun z ↦ b.app (DerivedCategory.Q.obj P.obj) ≫
          Gₗ.mapDerivedCategory.map (FY.mapDerivedCategoryFactors.hom.app P.obj) ≫ z) hlκ.symm
      _ = _ := by
        dsimp only [Gₗ, Q, FY, inverseImageIntegralDerived, Functor.comp_obj] at hn ⊢
        simpa only [Category.assoc] using! congrArg
          (fun z ↦ b.app (DerivedCategory.Q.obj P.obj) ≫ z ≫
            (integralDerivedPullbackComparison l L g).hom.app Qgood) hn
  have h := congr_app hAB K
  change FX.mapDerivedCategory.map (κE.app K) ≫ α.app K =
    b.app K ≫ κL.app (FY.mapDerivedCategory.obj K) at h
  rw [hκE, hκL] at h
  exact h


attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
private theorem scalarCompletedSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (hOrd : ∀ K : DerivedCategory (integralTowerModules l E Y),
      (integralOrdinaryDerivedScalar l E L ι X).map
          (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
          (scalarPullbackOrdinary l E L ι g).hom.app K =
        (isomorphismScalarTensorDerived l E L ι g).hom.app K ≫
          inverseImagePullbackComparisonDerived l L g hX hY
            ((integralOrdinaryDerivedScalar l E L ι Y).obj K))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  obtain ⟨κE, hκE, _, _, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  obtain ⟨κL, hκL, _, _, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l L g hX hY
  have hc := isomorphismComparisonInputs_constructible l E g hX hY K hK
  let : IsIso ((scalarCompletion l E L ι X).app
      ((inverseImageIntegralDerived l E g).obj K)) :=
    (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _ hc.1.1
  let : IsIso ((scalarCompletion l E L ι X).app
      ((integralDerivedPullback l E g).obj K)) :=
    (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _ hc.2.1
  have h := completionSquare
    (inverseImageIntegralDerived l E g) (integralDerivedPullback l E g)
    (inverseImageIntegralDerived l L g) (integralDerivedPullback l L g)
    (integralOrdinaryDerivedScalar l E L ι X) (integralScalarExtension l E L ι X)
    (integralOrdinaryDerivedScalar l E L ι Y) (integralScalarExtension l E L ι Y)
    κE κL (scalarCompletion l E L ι X) (scalarCompletion l E L ι Y)
    (scalarPullbackOrdinary l E L ι g).hom
    (isomorphismScalarTensorDerived l E L ι g).hom K
    (by simpa only [hκE, hκL] using hOrd K)
  rw [hκE, hκL] at h
  simpa only [isomorphismComparisonScalarAlpha, isomorphismComparisonScalarBeta,
    scalarPullbackCompleted, scalarCompletionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Category.assoc] using h


end ComparisonSquare

/-- The specified integral comparison commutes with finite coefficient extension.
Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50--51; the compatibility
itself is the agent calculation of the specified quotient-cone maps
(blueprint: lem-weil-isomorphism-comparison-scalar-extension).
Proof: the ordinary tensor unit and the finite scalar-pullback generator formula
prove the square at every finite level. Product extensionality and the two actual
Roos cocone coordinates give the strict augmentation square, with zero shifted
coordinate. On good representatives its localization is the ordinary derived square,
by the normalizations of the specified comparison and scalarPullbackOrdinary.
Naturality and good representative isomorphisms give that square on every derived
object. Finally precompose with the specified completion comparison chi on G_E K.
Naturality of chi and kappa reduces to the ordinary square. Constructibility makes
this completion comparison invertible, so it cancels to give the stated identity. -/
theorem isomorphismComparison_scalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  exact scalarCompletedSquare l E L ι g hX hY
    (scalarDerivedSquare l E L ι g hX hY (scalarRoosSquare l E L ι g)) K hK

end WeilConjectures
