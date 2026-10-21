/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralUniformCoefficient
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Basic

import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompletedConstantSheafReduction
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Sheaf.Paper.AdicReductionCohomologySequence
import all Sheaf.Paper.AdicReductionTriangle
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Uniformizer cone comparison and uniform reduction bound

Source: literature/stacks-project/sites-modules.tex, Tags 093J and 093M; derived.tex Tag 05RS
(blueprint: lem-cbc-finite-extension-reduction-cone-bound).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

set_option backward.isDefEq.respectTransparency false in
private theorem natural_scalar_triangle
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A : Type*} [CommRing A] [Linear A C] (r : A)
    (U : C ⥤ C) [U.Additive] (η : 𝟭 C ⟶ U)
    (P : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (F : DerivedCategory C ⥤ DerivedCategory C)
    (e : P ⋙ DerivedCategory.Q ≅ DerivedCategory.Q)
    (k : P ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ F)
    (β : 𝟭 (DerivedCategory C) ⟶ F)
    (hz : ∀ X, (r • 𝟙 (P.obj X)) ≫
      (NatTrans.mapHomologicalComplex η (.up ℤ)).app (P.obj X) = 0)
    (hs : ∀ X, (ShortComplex.mk _ _ (hz X)).ShortExact)
    (hn : ∀ X, DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex η (.up ℤ)).app (P.obj X)) ≫ (k.app X).hom =
      (e.app X).hom ≫ β.app (DerivedCategory.Q.obj X)) :
    ∃ γ : F ⟶ shiftFunctor (DerivedCategory C) (1 : ℤ),
      ∀ N, Triangle.mk (r • 𝟙 N) (β.app N) (γ.app N) ∈ distTriang _ := by
  classical
  let δ : P ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      (P ⋙ DerivedCategory.Q) ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ) :=
    { app := fun X ↦ DerivedCategory.triangleOfSESδ (hs X)
      naturality := by
        intro X Y f
        let t : ShortComplex.mk _ _ (hz X) ⟶ ShortComplex.mk _ _ (hz Y) :=
          { τ₁ := P.map f
            τ₂ := P.map f
            τ₃ := (U.mapHomologicalComplex (.up ℤ)).map (P.map f)
            comm₁₂ := by simp [Linear.comp_smul, Linear.smul_comp]
            comm₂₃ := (NatTrans.mapHomologicalComplex η (.up ℤ)).naturality (P.map f) }
        exact (DerivedCategory.triangleOfSESδ_naturality (hs X) (hs Y) t).symm }
  let τ : DerivedCategory.Q ⋙ F ⟶
      DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory C) (1 : ℤ) :=
    k.inv ≫ δ ≫ Functor.whiskerRight e.hom _
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q W (DerivedCategory C)
  let γ := ff.preimage τ
  have hγ (X : CochainComplex C ℤ) : γ.app (DerivedCategory.Q.obj X) = τ.app X :=
    congrArg (fun t ↦ t.app X) (ff.map_preimage τ)
  have ht (X : CochainComplex C ℤ) :
      Triangle.mk (r • 𝟙 (DerivedCategory.Q.obj X))
        (β.app (DerivedCategory.Q.obj X)) (γ.app (DerivedCategory.Q.obj X)) ∈
          distTriang _ := by
    apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (hs X)) _
    refine Triangle.isoMk _ _ (e.app X).symm (e.app X).symm (k.app X).symm ?_ ?_ ?_
    · change (r • 𝟙 _) ≫ (e.app X).inv =
        (e.app X).inv ≫ DerivedCategory.Q.map (r • 𝟙 _)
      rw [Functor.map_smul]
      rw [CategoryTheory.Functor.map_id]
      rw [Linear.smul_comp, Linear.comp_smul]
      simp only [Category.id_comp]
      exact congrArg (r • ·) (Category.comp_id (e.app X).inv).symm
    · change β.app _ ≫ (k.app X).inv =
        (e.app X).inv ≫ DerivedCategory.Q.map _
      apply (cancel_mono (k.app X).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hn X,
        Iso.inv_hom_id_assoc]
    · rw [hγ]
      simp [τ, δ, ← Functor.map_comp, Category.assoc]
  refine ⟨γ, fun N ↦ ?_⟩
  let j := DerivedCategory.Q.objObjPreimageIso N
  apply isomorphic_distinguished _ (ht (DerivedCategory.Q.objPreimage N)) _
  refine Triangle.isoMk _ _ j.symm j.symm (F.mapIso j).symm ?_ ?_ ?_
  · change (r • 𝟙 _) ≫ j.inv = j.inv ≫ (r • 𝟙 _)
    rw [Linear.smul_comp, Linear.comp_smul]
    simp only [Category.id_comp, Category.comp_id]
  · exact (β.naturality j.inv).symm
  · exact (γ.naturality j.inv).symm

-- Express the universal homotopy-category counit on cochain complexes.
private def complex_extension_comparison
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv L ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) ε ≫
    Functor.whiskerRight (U.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (U.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom

private def restricted_complex_comparison
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] (V : D ⥤ C) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ (L ⋙ V.mapDerivedCategory) ⟶
      (U ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app X := V.mapDerivedCategory.map ((complex_extension_comparison U L ε).app X) ≫
    V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj X)
  naturality {X Y} f := by
    have h := (complex_extension_comparison U L ε).naturality f
    dsimp only [Functor.comp_map] at h ⊢
    rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc, Category.assoc,
      V.mapDerivedCategoryFactors_hom_naturality]
    rfl

-- Cancel the comparison counit, then use naturality of the derived unit.
private theorem normalized_iso_comparison
    {B C : Type*} [Category B] [Category C]
    {L Q G : B ⥤ C} {F : C ⥤ C} (e : L ≅ Q) (κ : L ⋙ F ⟶ G) [IsIso κ]
    (β : 𝟭 C ⟶ F) (X : B) (f : L.obj X ⟶ G.obj X)
    (hf : β.app (L.obj X) ≫ κ.app X = f) :
    f ≫ (((asIso κ).symm ≪≫ Functor.isoWhiskerRight e F).app X).hom =
      (e.app X).hom ≫ β.app (Q.obj X) := by
  simp only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [NatIso.isIso_inv_app, ← hf]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (β.naturality (e.app X).hom).symm

private theorem short_exact_of_first_eq
    {C : Type*} [Category C] [Abelian C] {X Y Z : C}
    {f f' : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0)
    (hs : (ShortComplex.mk f g h).ShortExact) (hf : f = f') :
    ∃ h' : f' ≫ g = 0, (ShortComplex.mk f' g h').ShortExact := by
  subst f'
  exact ⟨h, hs⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
open scoped ZeroObject in
private theorem generic_functorial_flat_models
    (C : Type*) [Category C] [Abelian C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C]
    [HasExactColimitsOfShape ℤ C] [Abelian.HasFunctorialFlatResolution C] :
    ∃ (P : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (ρ : P ⟶ 𝟭 _),
      (∀ X, QuasiIso (ρ.app X)) ∧
      (∀ X Z, Z.Acyclic → ((MonoidalCategory.tensorRight (P.obj X)).obj Z).Acyclic) ∧
      (∀ X i, exactFunctor C C (MonoidalCategory.tensorRight ((P.obj X).X i))) := by
  classical
  have (X : C) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft X)
      (BraidedCategory.tensorLeftIsoTensorRight X)
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ C))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat :=
    ObjectProperty.flat.essImage_ι_le
  have hflat (X : CochainComplex C ℤ) (i : ℤ) :
      ObjectProperty.flat ((Λ.resolutionFunctor.obj X).X i) := by
    have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj X
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) c.isColimit)
      (fun j ↦ hι _ ((c.prop_diag_obj j).1 i))
  refine ⟨Λ.resolutionFunctor, Λ.resolutionNatTrans, fun X ↦ inferInstance, ?_,
    fun X i ↦ (hflat X i).2⟩
  intro X Z hZ
  have hk := Λ.kFlat_resolutionFunctor_obj hι X
  let H := MonoidalCategory.tensorRight (Λ.resolutionFunctor.obj X)
  have hz : QuasiIso (0 : (0 : CochainComplex C ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (H.map (0 : (0 : CochainComplex C ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (H.obj (0 : CochainComplex C ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (H.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (H.map (0 : (0 : CochainComplex C ℤ) ⟶ Z)) i).1 (htzero i)

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] CompletedConstantReduction.constantChange_unit
  pbcPadicCoefficientDatum

set_option backward.isDefEq.respectTransparency false in
private theorem completed_scalar_comparison (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    pbcCompletedScalar T d = CompletedConstantReduction.base T d.ideal ≫
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite := by
  have hb : adicDatumScalar T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } = CompletedConstantReduction.base T d.ideal := by
    apply (CompletedConstantReduction.base_exists T d.ideal).choose_spec.2
    exact (adicDatumScalar_exists T
        { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
          quotientFinite := d.quotientFinite }).exists.choose_spec
  have he (n : ℕ) : (pbcLevelConstantComparison T d n).hom =
      @AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
    change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
      toSheafify _ _ ≫ sheafifyMap _ _
    rw [← toSheafify_naturality]
    ext U b
    exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b
  have hc : (pbcCompletedComparison T d).hom =
      CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite := by
    apply limit.hom_ext
    intro n
    dsimp only [pbcCompletedComparison, CompletedConstantReduction.completedComparison]
    rw [HasLimit.isoOfNatIso_hom_π]
    change _ = limMap _ ≫ _
    rw [limMap_π]
    change _ ≫ (pbcLevelConstantComparison T d n.unop).hom = _
    rw [he]
    rfl
  unfold pbcCompletedScalar
  rw [hb, hc]

set_option backward.isDefEq.respectTransparency false in
private theorem constant_scalar_conjugate (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (c : adicLisseConstantRing T A ⟶ R) (a : A) (V : T.ProEtᵒᵖ) :
    let F := adicLisseConstantModules T A ⋙ completedAdicChange T c
    let e := CompletedConstantReduction.constantChange_unit T c
    (e.inv ≫ F.map (ModuleCat.ofHom (LinearMap.mulLeft A a)) ≫ e.hom).val.app V
      (1 : R.obj.obj V) =
        c.hom.app V ((adicLisseConstantUnit T A).app V a) := by
  dsimp only
  let M := (adicLisseConstantModules T A).obj (ModuleCat.of A A)
  let e := CompletedConstantReduction.constantChange_unit T c
  let μ := ModuleCat.ofHom (LinearMap.mulLeft A a)
  let f := ((completedAdicChange T c).map ((adicLisseConstantModules T A).map μ)).val.app V
  let t (x : A) := completedAdicChangeTensor T c M V 1
    (constantGenerator T (ModuleCat.of A A) V x)
  let b := c.hom.app V ((adicLisseConstantUnit T A).app V a)
  let q (x : M.val.obj V) : ((completedAdicChange T c).obj M).val.obj V :=
    ((pbcScalarAdjunction c).unit.app M).val.app V x
  let eh (x : ((completedAdicChange T c).obj M).val.obj V) : R.obj.obj V :=
    e.hom.val.app V x
  let ei (x : R.obj.obj V) : ((completedAdicChange T c).obj M).val.obj V :=
    e.inv.val.app V x
  have hμ : ((adicLisseConstantModules T A).map μ).val.app V
      (constantGenerator T (ModuleCat.of A A) V 1) =
      constantGenerator T (ModuleCat.of A A) V a :=
    (constantGenerator_naturality T μ V (1 : A)).trans
      (congrArg (constantGenerator T (ModuleCat.of A A) V) (mul_one a))
  have hm : f (t 1) = t a :=
    (completed_map_tensor_one T c ((adicLisseConstantModules T A).map μ) V
      (constantGenerator T (ModuleCat.of A A) V 1)).trans
        (congrArg (completedAdicChangeTensor T c M V 1) hμ)
  have hg : constantGenerator T (ModuleCat.of A A) V a =
      ((adicLisseConstantUnit T A).app V a) •
        constantGenerator T (ModuleCat.of A A) V 1 := by
    have h := ((PresheafOfModules.sheafificationAdjunction
      (adicLisseConstantUnit T A)).unit.app
        ((constantPresheaves T A).obj (ModuleCat.of A A))).app V |>.hom.map_smul a
          (show ((constantPresheaves T A).obj (ModuleCat.of A A)).obj V from (1 : A))
    change constantGenerator T (ModuleCat.of A A) V (a * 1) =
      ((adicLisseConstantUnit T A).app V a) •
        constantGenerator T (ModuleCat.of A A) V 1 at h
    exact (congrArg (constantGenerator T (ModuleCat.of A A) V) (mul_one a)).symm.trans h
  have hη (x : M.val.obj V) : completedAdicChangeTensor T c M V 1 x =
      q x :=
    ((pbcScalarAdjunction_exists c).exists.choose_spec M V x).symm
  have hb : t a = b • t 1 := by
    calc
      t a = q (constantGenerator T (ModuleCat.of A A) V a) := hη _
      _ = q (((adicLisseConstantUnit T A).app V a) •
          constantGenerator T (ModuleCat.of A A) V 1) := congrArg q hg
      _ = b • q (constantGenerator T (ModuleCat.of A A) V 1) :=
        (((pbcScalarAdjunction c).unit.app M).val.app V).hom.map_smul
          ((adicLisseConstantUnit T A).app V a) _
      _ = b • t 1 := congrArg (b • ·) (hη _).symm
  have he := congrArg (fun k ↦ k.val.app V (1 : R.obj.obj V)) e.inv_hom_id
  change eh (ei 1) = (1 : R.obj.obj V) at he
  have ht : eh (t 1) = (1 : R.obj.obj V) :=
    (congrArg eh (constant_unit_inv_one T c V).symm).trans he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    CategoryTheory.Functor.comp_map]
  change eh (f (ei 1)) = b
  calc
    _ = eh (f (t 1)) :=
      congrArg (fun x ↦ eh (f x)) (constant_unit_inv_one T c V)
    _ = eh (t a) := congrArg eh hm
    _ = eh (b • t 1) := congrArg eh hb
    _ = b * eh (t 1) := (e.hom.val.app V).hom.map_smul b (t 1)
    _ = b * 1 := congrArg (b * ·) ht
    _ = b := mul_one b

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_sequence_flat
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (M : pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))
    (hflat : exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))
      M)) :
    ∃ hz : (Padic.coefficientExtensionUniformizer l E ^ (n + 1) • 𝟙 M) ≫
        (pbcScalarAdjunction (pbcAdicProjection T (pbcPadicCoefficientDatum l E) n)).unit.app
          M = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  let d := pbcPadicCoefficientDatum l E
  let R := pbcAdicCompletion T d
  let c := CompletedConstantReduction.base T d.ideal ≫
    CompletedConstantReduction.completedComparison T d.ideal d.quotientFinite
  let F := adicLisseConstantModules T (Padic.coefficientExtensionIntegers l E) ⋙
    completedAdicChange T c
  let e := CompletedConstantReduction.constantChange_unit T c
  let a := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
  let f := e.inv ≫ F.map (ModuleCat.ofHom
    (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E) a)) ≫ e.hom
  obtain ⟨p, hz, hs, hp⟩ := coefficient_resolution T l E n
  have hm : (ReductionTensor.multiplicationNatural T R f).app M = a • 𝟙 M := by
    ext V x
    change (ReductionTensor.tensorMultiplication T R f M).val.app V x = _
    rw [ReductionTensor.tensorMultiplication_apply]
    have hf : f.val.app V (1 : R.obj.obj V) = pbcCompletedSection T d V a := by
      rw [constant_scalar_conjugate]
      change _ = (pbcCompletedScalar T d).hom.app V
        ((adicLisseConstantUnit T (Padic.coefficientExtensionIntegers l E)).app V a)
      rw [completed_scalar_comparison]
    rw [hf]
    rfl
  obtain ⟨hw, _, hseq⟩ := ReductionTensor.tensor_complex_exact T R
    (pbcAdicProjection T d n) p f hz hs hp M
  exact short_exact_of_first_eq hw (hseq hflat) hm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
private theorem functorial_flat_models (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ∃ (P : CochainComplex (pbcModules T R) ℤ ⥤ CochainComplex (pbcModules T R) ℤ)
      (ρ : P ⟶ 𝟭 _),
      (∀ X, QuasiIso (ρ.app X)) ∧
      (∀ X, CochainComplex.IsKFlatIndependentCoefficients (R := R) (P.obj X)) ∧
      (∀ X i, exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory R) ((P.obj X).X i))) := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let C := pbcModules T R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  obtain ⟨P, ρ, hρ, hP, hflat⟩ := generic_functorial_flat_models C
  exact ⟨P, ρ, hρ, hP, hflat⟩

private abbrev restricted_counit_natural (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ (pbcDerivedExtend φ ⋙ pbcDerivedRestrict φ) ⟶
      (pbcExtend φ ⋙ pbcRestrict φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  restricted_complex_comparison (pbcExtend φ) (pbcRestrict φ)
    (pbcDerivedExtend φ) (pbcExtensionCounit φ)

private theorem restricted_counit_app (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (X : CochainComplex (pbcModules T R) ℤ) :
    (restricted_counit_natural T φ).app X =
      (pbcDerivedRestrict φ).map (pbcComplexCounit φ X) ≫
        (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj X) := rfl

/-- The completed finite-extension module category is abelian by the standard sheaf-of-modules
instance. Source: Stacks Project, Modules on Sites, Tag 093J (blueprint:
lem-cbc-finite-extension-reduction-cone-bound). -/
noncomputable instance finiteExtensionCompletedModulesAbelian
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    Abelian (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) :=
  SheafOfModules.instAbelian _

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 4096 in
/--
Source: literature/stacks-project/sites-modules.tex, Tags 093J and 093M; derived.tex Tag 05RS
(blueprint: lem-cbc-finite-extension-reduction-cone-bound).

For the completed coefficient datum of a finite extension, reduction modulo every positive
power of the uniformizer is the cone of uniformizer multiplication.  The same distinguished
triangle is natural in the derived module, and the long exact homology sequence gives the
uniform interval `[a - 1, b]` from an interval `[a, b]` for the original object.
-/
theorem finiteExtensionReductionConeBound
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (M : PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) (a b : ℤ) (hab : a ≤ b)
    (hM : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) q).obj M)) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ (β : 𝟭 (PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) ⟶
          (pbcCompletedReduction T (pbcPadicCoefficientDatum l E) (n - 1) ⋙
            pbcDerivedRestrict (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n - 1))))
        (γ : (pbcCompletedReduction T (pbcPadicCoefficientDatum l E) (n - 1) ⋙
              pbcDerivedRestrict
                (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n - 1))) ⟶
          𝟭 (PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) ⋙ shiftFunctor
            (PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) (1 : ℤ)),
        (∀ N : PbcCompletedDerived T (pbcPadicCoefficientDatum l E),
          Triangle.mk
              ((Padic.coefficientExtensionUniformizer l E) ^ n • 𝟙 N)
              (β.app N) (γ.app N) ∈
            distTriang (PbcCompletedDerived T (pbcPadicCoefficientDatum l E))) ∧
        (∀ q : ℤ, q < a - 1 ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor
            (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) q).obj
            ((pbcCompletedReduction T (pbcPadicCoefficientDatum l E) (n - 1) ⋙
              pbcDerivedRestrict
                (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n - 1))).obj M)))  := by
  classical
  intro n hn
  let d := pbcPadicCoefficientDatum l E
  let R := pbcAdicCompletion T d
  let φ := pbcAdicProjection T d (n - 1)
  let U := pbcExtend φ ⋙ pbcRestrict φ
  let F := pbcDerivedExtend φ ⋙ pbcDerivedRestrict φ
  let r := Padic.coefficientExtensionUniformizer l E ^ ((n - 1) + 1)
  have hn' : (n - 1) + 1 = n := by omega
  obtain ⟨P, ρ, hρ, hP, hflat⟩ := functorial_flat_models T R
  have (X : CochainComplex (pbcModules T R) ℤ) : QuasiIso (ρ.app X) := hρ X
  have : IsIso (Functor.whiskerRight ρ DerivedCategory.Q) := by
    have (X : CochainComplex (pbcModules T R) ℤ) :
        IsIso ((Functor.whiskerRight ρ DerivedCategory.Q).app X) := by
      dsimp only [Functor.whiskerRight_app]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let e : P ⋙ DerivedCategory.Q ≅ DerivedCategory.Q :=
    asIso (Functor.whiskerRight ρ DerivedCategory.Q)
  let κ := Functor.whiskerLeft P (restricted_counit_natural T φ)
  have : IsIso κ := by
    have (X : CochainComplex (pbcModules T R) ℤ) : IsIso (κ.app X) := by
      change IsIso ((restricted_counit_natural T φ).app (P.obj X))
      rw [restricted_counit_app]
      have := complexCounit_isIso T φ (P.obj X) (hP X)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let k : P ⋙ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ F :=
    (asIso κ).symm ≪≫ Functor.isoWhiskerRight e F
  let β := (pbcDerivedScalarAdjunction φ).unit
  have hz (X : CochainComplex (pbcModules T R) ℤ) :
      (r • 𝟙 (P.obj X)) ≫
        (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app
          (P.obj X) = 0 := by
    ext i : 1
    exact (scalar_sequence_flat T l E (n - 1) ((P.obj X).X i) (hflat X i)).choose
  have hs (X : CochainComplex (pbcModules T R) ℤ) :
      (ShortComplex.mk _ _ (hz X)).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    exact (scalar_sequence_flat T l E (n - 1) ((P.obj X).X i) (hflat X i)).choose_spec
  have hnorm (X : CochainComplex (pbcModules T R) ℤ) :
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app
          (P.obj X)) ≫ (k.app X).hom =
      (e.app X).hom ≫ β.app (DerivedCategory.Q.obj X) := by
    have hunit := (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec (P.obj X) (hP X)
    have hη : β.app (DerivedCategory.Q.obj (P.obj X)) ≫ κ.app X =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app
            (P.obj X)) := by
      rw [Functor.whiskerLeft_app, restricted_counit_app]
      exact hunit
    exact normalized_iso_comparison (F := F) e κ β X _ hη
  obtain ⟨γ, htri⟩ := natural_scalar_triangle r U (pbcScalarAdjunction φ).unit P F e k
    β hz hs hnorm
  refine ⟨β, γ, ?_, ?_⟩
  · intro N
    have hr : r = Padic.coefficientExtensionUniformizer l E ^ n :=
      congrArg (fun m : ℕ ↦ Padic.coefficientExtensionUniformizer l E ^ m) hn'
    exact (congrArg (fun c : Padic.coefficientExtensionIntegers l E ↦
      Triangle.mk (c • 𝟙 N) (β.app N) (γ.app N) ∈ distTriang _) hr).mp (htri N)
  · intro q hq
    have hq₀ : q < a ∨ b < q := by omega
    have hq₁ : q + 1 < a ∨ b < q + 1 := by omega
    exact (DerivedCategory.HomologySequence.exact₃
      (Triangle.mk (r • 𝟙 M) (β.app M) (γ.app M)) (htri M) q (q + 1) rfl).isZero_of_both_isZero
        (hM q hq₀) (hM (q + 1) hq₁)


end AlgebraicGeometry.Scheme

