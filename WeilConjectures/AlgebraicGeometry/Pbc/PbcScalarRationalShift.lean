/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTriangulation
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientShift
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Exactness and shift descent for rational scalar extension

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-rational-exactness)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section ScalarShift
variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) (T : Scheme.{u})
variable [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The integral restriction retains the actual ambient functor through its inclusion.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness). -/
@[irreducible] def pbcIntegralScalarInclusionIso :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F)) ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
        pbcEmbeddingAmbientTensor l E F i T := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCommShift_unique
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    {J : C ⥤ D} {I : D ⥤ B} {H : C ⥤ B} [I.Full] [I.Faithful]
    [I.CommShift ℤ] [H.CommShift ℤ] (e : J ⋙ I ≅ H)
    (q q' : J.CommShift ℤ)
    (hq : (fun [_s : J.CommShift ℤ] ↦ NatTrans.CommShift e.hom ℤ) (_s := q))
    (hq' : (fun [_s : J.CommShift ℤ] ↦ NatTrans.CommShift e.hom ℤ) (_s := q')) :
    q = q' := by
  have square (s : J.CommShift ℤ)
      (hs : letI := s; NatTrans.CommShift e.hom ℤ) (n : ℤ) (K : C) :
      I.map ((CategoryTheory.Functor.commShiftIso J (self := s) n).hom.app K) ≫
          (I.commShiftIso n).hom.app (J.obj K) ≫
            (shiftFunctor B n).map (e.hom.app K) =
        e.hom.app (K⟦n⟧) ≫ (H.commShiftIso n).hom.app K := by
    let := s
    have := hs
    simpa only [CategoryTheory.Functor.commShiftIso_comp_hom_app, Category.assoc]
      using NatTrans.shift_app_comm e.hom n K
  have he (n : ℤ) : CategoryTheory.Functor.commShiftIso J (self := q) n =
      CategoryTheory.Functor.commShiftIso J (self := q') n := by
    apply Iso.ext
    ext K
    apply I.map_injective
    apply (cancel_mono ((I.commShiftIso n).hom.app (J.obj K))).mp
    apply (cancel_mono ((shiftFunctor B n).map (e.hom.app K))).mp
    simpa only [Category.assoc] using (square q hq n K).trans (square q' hq' n K).symm
  cases q
  cases q'
  congr
  funext n
  exact he n

set_option linter.unusedVariables false in
/-- Faithful full inclusions uniquely transport the ambient tensor shift.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness).
Proof: conjugate the ambient comparison by the inherited inclusion's shift
comparisons. Fullness lifts it to the integral subcategory; faithfulness lifts
its inverse, naturality and zero/addition coherence. Faithfulness also proves
uniqueness, with the stated commuting inclusion equation. -/
theorem pbcIntegralScalarShift_exists :
    ∃! q : (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ,
      (fun [qInst : (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ] ↦
        NatTrans.CommShift (pbcIntegralScalarInclusionIso l E F i T).hom ℤ) (qInst := q) := by
  let e := pbcIntegralScalarInclusionIso l E F i T
  let q := CategoryTheory.Functor.CommShift.ofComp e ℤ
  have hq : (fun [s : (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out
      ).CommShift ℤ] ↦ NatTrans.CommShift e.hom ℤ) (s := q) :=
    CategoryTheory.Functor.CommShift.ofComp_compatibility e ℤ
  exact ⟨q, hq, fun q' hq' ↦ pbcCommShift_unique e q' q hq' hq⟩

/-- The inherited integral shift, fixed by the ambient inclusion equation.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness). -/
instance pbcIntegralScalarShift :
    (pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).CommShift ℤ :=
  (pbcIntegralScalarShift_exists l E F i T).exists.choose

/-- The actual tensor Hom formula agrees with tensoring integral arrows by one.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness).
Proof: put the scalar equal to one in pbcRationalScalarHom_exists. The normalized
coefficient isomorphisms and the algebra inclusion send one to one, yielding the
displayed naturality equation of identity components. -/
theorem pbcScalarLocalization_naturality
    {K L : PbcIntegralCategory l E T dim.out inv.out} (f : K ⟶ L) :
    (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (pbcRationalScalarExtension l E F i T dim.out inv.out).map
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) := by
  have h := (pbcRationalScalarHom_exists l E F i T dim.out inv.out K L).exists.choose_spec
    (1 : Localization.Away (pbcUniformizer l E)) f
  simp only [Category.comp_id, Category.id_comp]
  change _ = pbcRationalScalarHom l E F i T dim.out inv.out K L _
  dsimp only [pbcRationalScalarHom]
  simpa only [one_smul, map_one] using h.symm

/-- The integral-to-rational tensor square has identity components on objects.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness). -/
@[irreducible] def pbcScalarLocalizationIso :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F) ≅
      pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        pbcRationalScalarExtension l E F i T dim.out inv.out :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ pbcScalarLocalization_naturality l E F i T f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcPrecompCommShift_unique
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (Q : C ⥤ D) (hQ : Function.Surjective Q.obj) [Q.CommShift ℤ]
    (J : D ⥤ B) (H : C ⥤ B) [H.CommShift ℤ] (e : Q ⋙ J ≅ H)
    (q q' : J.CommShift ℤ)
    (hq : letI := q; NatTrans.CommShift e.hom ℤ)
    (hq' : letI := q'; NatTrans.CommShift e.hom ℤ) : q = q' := by
  have square (s : J.CommShift ℤ) (hs : letI := s; NatTrans.CommShift e.hom ℤ)
      (n : ℤ) (K : C) :
      J.map ((Q.commShiftIso n).hom.app K) ≫
          (CategoryTheory.Functor.commShiftIso J (self := s) n).hom.app (Q.obj K) ≫
          (shiftFunctor B n).map (e.hom.app K) =
        e.hom.app (K⟦n⟧) ≫ (H.commShiftIso n).hom.app K := by
    let := s
    have := hs
    simpa only [CategoryTheory.Functor.commShiftIso_comp_hom_app, Category.assoc]
      using NatTrans.shift_app_comm e.hom n K
  apply pbcKanCommShift_ext
  intro n
  apply Iso.ext
  ext K
  obtain ⟨M, rfl⟩ := hQ K
  apply (cancel_epi (J.map ((Q.commShiftIso n).hom.app M))).mp
  apply (cancel_mono ((shiftFunctor B n).map (e.hom.app M))).mp
  simpa only [Category.assoc] using
    (square q hq n M).trans (square q' hq' n M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- The rational shift comparison is precisely the localized ambient tensor comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness).
Proof: the inherited integral shift changes no underlying completed complex. On
pure tensor Hom modules localization extends the ambient shift comparison. The
balancing formula makes it natural for all rational morphisms. The ambient zero
and addition coherence descend, and generation by pure tensors gives uniqueness. -/
theorem pbcRationalScalarShift_exists :
    ∃! q : (pbcRationalScalarExtension l E F i T dim.out inv.out).CommShift ℤ,
      (fun [qInst : (pbcRationalScalarExtension l E F i T dim.out inv.out).CommShift ℤ] ↦
        NatTrans.CommShift (pbcScalarLocalizationIso l E F i T).hom ℤ) (qInst := q) := by
  let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let P := pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)
  let I := pbcEmbeddingIntegralTensor l E F i T dim.out inv.out
  let J := pbcRationalScalarExtension l E F i T dim.out inv.out
  let e := pbcScalarLocalizationIso l E F i T
  let W := Rationalization.W (Submonoid.powers (pbcUniformizer l E))
    (PbcIntegralCategory l E T dim.out inv.out)
  have : Q.IsLocalization W :=
    ScalarLocalization.pbcScalarLocalization_isLocalization _ _ _
  let : Localization.Lifting Q W (I ⋙ P) J := ⟨e.symm⟩
  let q : J.CommShift ℤ :=
    CategoryTheory.Functor.commShiftOfLocalization Q W ℤ (I ⋙ P) J
  have hq : letI := q; NatTrans.CommShift e.hom ℤ := by
    let := q
    have : NatTrans.CommShift e.symm.hom ℤ := by
      change NatTrans.CommShift e.inv ℤ
      exact NatTrans.commShift_iso_hom_of_localization Q W ℤ (I ⋙ P) J
    exact NatTrans.CommShift.of_iso_inv e.symm ℤ
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have hinv (s : J.CommShift ℤ) (hs : letI := s; NatTrans.CommShift e.hom ℤ) :
      letI := s; NatTrans.CommShift e.inv ℤ := by
    let := s
    have := hs
    exact NatTrans.CommShift.of_iso_inv e ℤ
  exact pbcPrecompCommShift_unique Q (fun K ↦ ⟨K.obj, rfl⟩) J (I ⋙ P) e.symm
    q' q (hinv q' hq') (hinv q hq)

/-- The canonical rational tensor shift with its integral normalization retained.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness). -/
instance pbcRationalScalarShift :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).CommShift ℤ :=
  (pbcRationalScalarShift_exists l E F i T).exists.choose

attribute [local irreducible] pbcRationalScalarHom

private def scalarIntegralComp
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (j : F →ₐ[Padic l] G) :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        pbcEmbeddingIntegralTensor l F G j T dim.out inv.out ≅
      pbcEmbeddingIntegralTensor l E G (j.comp i) T dim.out inv.out :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk
    (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l G))
      ((pbcAmbientScalarComp l E F G i j T).app K.obj)) (fun f ↦ by
    apply ObjectProperty.hom_ext
    exact (pbcAmbientScalarComp l E F G i j T).hom.naturality f.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarIntegralComp_shift
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (j : F →ₐ[Padic l] G) :
    NatTrans.CommShift (scalarIntegralComp l E F i T G j).hom ℤ := by
  let IEF := pbcEmbeddingIntegralTensor l E F i T dim.out inv.out
  let IFG := pbcEmbeddingIntegralTensor l F G j T dim.out inv.out
  let IEG := pbcEmbeddingIntegralTensor l E G (j.comp i) T dim.out inv.out
  let JG := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l G))
  let JF := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F))
  let JE := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
  let AEF := pbcEmbeddingAmbientTensor l E F i T
  let AFG := pbcEmbeddingAmbientTensor l F G j T
  let eEF := pbcIntegralScalarInclusionIso l E F i T
  let eFG := pbcIntegralScalarInclusionIso l F G j T
  let eEG := pbcIntegralScalarInclusionIso l E G (j.comp i) T
  have : NatTrans.CommShift eEF.hom ℤ :=
    (pbcIntegralScalarShift_exists l E F i T).exists.choose_spec
  have : NatTrans.CommShift eFG.hom ℤ :=
    (pbcIntegralScalarShift_exists l F G j T).exists.choose_spec
  have : NatTrans.CommShift eEG.hom ℤ :=
    (pbcIntegralScalarShift_exists l E G (j.comp i) T).exists.choose_spec
  have : NatTrans.CommShift (pbcAmbientScalarComp l E F G i j T).hom ℤ :=
    scalarAmbientComp_shift l E F i T G j
  have he : whiskerRight (scalarIntegralComp l E F i T G j).hom JG =
      (Functor.associator IEF IFG JG).hom ≫ whiskerLeft IEF eFG.hom ≫
      (Functor.associator IEF JF AFG).inv ≫ whiskerRight eEF.hom AFG ≫
      (Functor.associator JE AEF AFG).hom ≫
      whiskerLeft JE (pbcAmbientScalarComp l E F G i j T).hom ≫ eEG.inv := by
    ext K
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      eEF, eFG, eEG, pbcIntegralScalarInclusionIso, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app]
    change (pbcAmbientScalarComp l E F G i j T).hom.app K.obj =
      𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ AFG.map (𝟙 _) ≫ 𝟙 _ ≫
        (pbcAmbientScalarComp l E F G i j T).hom.app K.obj ≫ 𝟙 _
    rw [AFG.map_id]
    simp only [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (scalarIntegralComp l E F i T G j).hom JG) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ JG

private theorem scalarMapIdComposite
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X : C)
    {Y : D} (f : F.obj X ⟶ Y) :
    𝟙 _ ≫ F.map (𝟙 X) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ f ≫ 𝟙 _ = f := by
  rw [F.map_id]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarRationalComp_shift
    (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (j : F →ₐ[Padic l] G) :
    NatTrans.CommShift (pbcRationalScalarComp l E F G i j T dim.out inv.out).hom ℤ := by
  let IEF := pbcEmbeddingIntegralTensor l E F i T dim.out inv.out
  let IFG := pbcEmbeddingIntegralTensor l F G j T dim.out inv.out
  let QE := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let QF := pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)
  let QG := pbcRationalization T (pbcIntegralDatum l G) (pbcUniformizer l G)
  let REF := pbcRationalScalarExtension l E F i T dim.out inv.out
  let RFG := pbcRationalScalarExtension l F G j T dim.out inv.out
  let eEF := pbcScalarLocalizationIso l E F i T
  let eFG := pbcScalarLocalizationIso l F G j T
  let eEG := pbcScalarLocalizationIso l E G (j.comp i) T
  have : NatTrans.CommShift eEF.hom ℤ :=
    (pbcRationalScalarShift_exists l E F i T).exists.choose_spec
  have : NatTrans.CommShift eFG.hom ℤ :=
    (pbcRationalScalarShift_exists l F G j T).exists.choose_spec
  have : NatTrans.CommShift eEG.hom ℤ :=
    (pbcRationalScalarShift_exists l E G (j.comp i) T).exists.choose_spec
  have : NatTrans.CommShift (scalarIntegralComp l E F i T G j).hom ℤ :=
    scalarIntegralComp_shift l E F i T G j
  have he : whiskerLeft QE
      (pbcRationalScalarComp l E F G i j T dim.out inv.out).hom =
      (Functor.associator QE REF RFG).inv ≫ whiskerRight eEF.inv RFG ≫
      (Functor.associator IEF QF RFG).hom ≫ whiskerLeft IEF eFG.inv ≫
      (Functor.associator IEF IFG QG).inv ≫
      whiskerRight (scalarIntegralComp l E F i T G j).hom QG ≫ eEG.hom := by
    ext K
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      eEF, eFG, eEG, pbcScalarLocalizationIso, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv]
    change (pbcRationalScalarComp l E F G i j T dim.out inv.out).hom.app (QE.obj K) =
      𝟙 _ ≫ RFG.map (𝟙 ((IEF ⋙ QF).obj K)) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
        QG.map ((scalarIntegralComp l E F i T G j).hom.app K) ≫ 𝟙 _
    calc
      _ = QG.map ((scalarIntegralComp l E F i T G j).hom.app K) := by
        unfold pbcRationalScalarComp pbcRationalScalarCompComponent scalarIntegralComp
        rfl
      _ = _ := (scalarMapIdComposite RFG ((IEF ⋙ QF).obj K)
        (QG.map ((scalarIntegralComp l E F i T G j).hom.app K))).symm
  have : NatTrans.CommShift (whiskerLeft QE
      (pbcRationalScalarComp l E F G i j T dim.out inv.out).hom) ℤ := by
    rw [he]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ QE (fun K ↦ ?_)
  exact ⟨K.obj, 𝟙 _, by infer_instance⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherian T] dim inv in
private theorem pbcAmbientScalarExact :
    (pbcEmbeddingAmbientTensor l E F i T).Additive ∧
      (pbcEmbeddingAmbientTensor l E F i T).IsTriangulated := by
  let φ := pbcScalarCoefficientMap l E F i T
  have := pbcDerivedExtension_universal φ
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨σ, hσ, huniq, hadd, htri⟩ :=
    SheafOfModules.derivedScalarExtension_counitShift.{u + 1, u, u + 1, u + 2, u + 2}
      φ (pbcExtend φ)
      (pbcExtensionExistence φ).choose_spec.choose
      (pbcExtensionExistence φ).choose_spec.choose_spec.choose
      (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  have : NatTrans.CommShift (pbcExtensionCounit φ) ℤ :=
    (pbcAmbientScalarShift_exists l E F i T).exists.choose_spec
  have he : (CategoryTheory.Functor.commShiftIso
      (pbcEmbeddingAmbientTensor l E F i T) (1 : ℤ)) = σ := by
    apply huniq
    intro P
    simpa only [CategoryTheory.Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm (pbcExtensionCounit φ) (1 : ℤ) P
  constructor
  · exact hadd
  · constructor
    intro Δ hΔ
    simpa only [CategoryTheory.Functor.mapTriangle_obj, he] using htri Δ hΔ

private theorem scalarRationalization_triangulated :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).IsTriangulated := by
  exact ((pbcRationalTriangulationData l E T dim.out inv.out).choose_spec.choose_spec.2
    ).choose_spec.choose_spec.2.choose_spec.2.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual raw rational tensor functor is additive and triangulated.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness).
Proof: ambient derived tensor preserves the termwise cone differential and its
canonical shift. Its integral restriction preserves inherited triangles because
it preserves the actual uniform complete property. Every raw rational triangle
is isomorphic to an integral image triangle. The scalar Hom formula sends that
image to the integral tensor image. It therefore preserves distinguished triangles
with the normalized last arrow; additivity follows on the tensor Hom generators. -/
theorem pbcRationalScalarExact :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).Additive ∧
      (pbcRationalScalarExtension l E F i T dim.out inv.out).IsTriangulated := by
  have ha := pbcAmbientScalarExact l E F i T
  have := ha.1
  have := ha.2
  let I := pbcEmbeddingIntegralTensor l E F i T dim.out inv.out
  let Q := pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)
  let P := pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)
  let J := pbcRationalScalarExtension l E F i T dim.out inv.out
  have hinc : NatTrans.CommShift (pbcIntegralScalarInclusionIso l E F i T).hom ℤ :=
    (pbcIntegralScalarShift_exists l E F i T).exists.choose_spec
  have : I.IsTriangulated :=
    (CategoryTheory.Functor.isTriangulated_iff_comp_right
      (pbcIntegralScalarInclusionIso l E F i T)).2 inferInstance
  have hQ : Q.IsTriangulated :=
    scalarRationalization_triangulated l E T
  have hP : P.IsTriangulated :=
    scalarRationalization_triangulated l F T
  let W := Rationalization.W (Submonoid.powers (pbcUniformizer l E))
    (PbcIntegralCategory l E T dim.out inv.out)
  have : Q.IsLocalization W := ScalarLocalization.pbcScalarLocalization_isLocalization _ _ _
  have := Localization.essSurj_mapArrow Q W
  have : NatTrans.CommShift (pbcScalarLocalizationIso l E F i T).hom ℤ :=
    (pbcRationalScalarShift_exists l E F i T).exists.choose_spec
  constructor
  · constructor
    intros K L f g
    exact (pbcRationalScalarHom l E F i T dim.out inv.out K.obj L.obj).map_add f g
  · exact CategoryTheory.Functor.isTriangulated_of_precomp_iso
      (pbcScalarLocalizationIso l E F i T).symm

/-- Additivity from the actual rational Hom formula.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness). -/
instance pbcRationalScalarAdditive :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).Additive :=
  (pbcRationalScalarExact l E F i T).1

/-- Exactness with the normalized tensor shift.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-rational-exactness). -/
instance pbcRationalScalarTriangulated :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).IsTriangulated :=
  (pbcRationalScalarExact l E F i T).2
end ScalarShift
end AlgebraicGeometry.Scheme
