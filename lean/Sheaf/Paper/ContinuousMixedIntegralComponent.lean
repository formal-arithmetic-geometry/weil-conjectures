/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H8 and U5
-/
module

public import Sheaf.Paper.ContinuousAmbientMixedCoherence
import Sheaf.Paper.ContinuousMixedOrdinaryBalance
import all Sheaf.Paper.CompletedPullbackReductionCoherence
import all Sheaf.Paper.PbcScalarAmbientOperations

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-mixed-integral-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F]

private theorem normalization_cancel {C : Type*} [Category C] {A B U V : C}
    (i : A ≅ B) (j : U ≅ V) (c : U ≅ A) (f : B ⟶ V)
    (h : f ≫ j.inv = i.inv ≫ c.inv) : i.hom ≫ f = c.inv ≫ j.hom := by
  apply (cancel_mono j.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

private theorem pull_normalization {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) (ag : Along l E g aX aY)
    (K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E)) :
    (derivedPull g ag.coefficient).map (aY.integral.hom.app K) ≫
        ag.ambient.hom.app K.obj ≫
        (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
          ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj) =
      ag.comparison.inv.app
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
        aX.integral.hom.app ((integralPull l E g ag.integral_mem).obj K) := by
  exact normalization_cancel
    ((derivedPull g ag.coefficient).mapIso (aY.integral.app K))
    (aX.integral.app ((integralPull l E g ag.integral_mem).obj K))
    (ag.comparison.app
      ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))
    _ (by simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using ag.completion_unit K)

private theorem scalar_normalization (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (b : FieldChange l E F i X aE aF)
    (K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) :
    b.comparison.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
        (pbcDerivedExtend b.coefficient).map (aE.integral.hom.app K) =
      aF.integral.hom.app
          ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (b.integralBalance l E F i X aE aF K.obj).hom := by
  apply (cancel_mono (pbcReductionNormalization (aE.integralIso.hom ≫ aE.inclusion)
    b.coefficient (aE.integralIso.hom ≫ aE.inclusion ≫ b.coefficient) rfl K.obj).hom).1
  simpa only [FieldChange.integralBalance, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using b.integral_normalization K

private theorem iso_pair_naturality {C : Type*} [Category C]
    {A A' B B' D D' : C} (α : A ≅ B) (α' : A' ≅ B') (β : D ≅ B) (β' : D' ≅ B')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D')
    (hα : a ≫ α'.hom = α.hom ≫ b) (hβ : c ≫ β'.hom = β.hom ≫ b) :
    a ≫ (α'.hom ≫ β'.inv) = (α.hom ≫ β.inv) ≫ c := by
  apply (cancel_mono β'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hβ, Iso.inv_hom_id_assoc]
  exact hα

private theorem balance_naturality (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (b : FieldChange l E F i X aE aF)
    {K L : PbcCompletedDerived X.scheme (pbcIntegralDatum l E)} (f : K ⟶ L) :
    (pbcDerivedExtend (aF.integralIso.hom ≫ aF.inclusion)).map
        ((pbcEmbeddingAmbientTensor l E F i X.scheme).map f) ≫
        (b.integralBalance l E F i X aE aF L).hom =
      (b.integralBalance l E F i X aE aF K).hom ≫
        (pbcDerivedExtend b.coefficient).map
          ((pbcDerivedExtend (aE.integralIso.hom ≫ aE.inclusion)).map f) := by
  let eE := aE.integralIso.hom ≫ aE.inclusion
  let eF := aF.integralIso.hom ≫ aF.inclusion
  let χ := eE ≫ b.coefficient
  let φ := pbcScalarCoefficientMap l E F i X.scheme
  let nI := pbcReductionNormalization φ eF χ b.square
  let nE := pbcReductionNormalization eE b.coefficient χ rfl
  change _ ≫ ((nI L).hom ≫ (nE L).inv) = ((nI K).hom ≫ (nE K).inv) ≫ _
  have hE := norm_natural eE b.coefficient χ rfl f
  have hI := norm_natural φ eF χ b.square f
  exact iso_pair_naturality (nI K) (nI L) (nE K) (nE L) _ _ _ hI hE

/-- The balanced mixed square realizes the specified completed scalar/pullback map
on one integral representative. There is no natural transformation to construct here.
Source: BS Remark 6.8.15; Stacks 0D6D, 0A0E, 0A0G
(blueprint: lem-per-continuous-mixed-integral-component).

Proof: rationalize the published integral component. The raw functor object formulas
identify its endpoints definitionally, so its heterogeneous normalization is reflexive.
Solve the two Along.completion_unit equations and the two
FieldChange.integral_normalization equations for the forward integral comparisons.
Postcompose by the scalar extension of the E pullback comparison inverse followed by
the integral comparison; this is an isomorphism and can be canceled. Naturality of
the realization and of the pair of scalar associators moves these comparisons to
the outside. Apply continuousMixedOrdinaryBalance for the ordinary tensor cube.
The published scalarCompletedPull_unit equation then replaces the ordinary scalar
comparison followed by the E completion unit with the F completion unit followed
by the published completed component. Apply the F normalization and cancel its
comparison with its inverse. This proves the equation for the chosen raw arrow,
without asserting a natural transformation on raw objects. -/
theorem continuousMixedIntegralComponent (i : E →ₐ[ℚ_[l]] F)
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF)
    (m : AmbientMixed l E F i g aXE aYE aXF aYF agE agF bX bY)
    (K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E)) :
    ∃ t : (agF.raw l F).obj
        ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) ⟶
      (pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj
        ((agE.raw l E).obj
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)),
    HEq t
      ((pbcRationalization X.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk
          (X := (integralPull l F g agF.integral_mem).obj
            ((pbcEmbeddingIntegralTensor l E F i Y.scheme Y.dimension Y.prime_unit).obj K))
          (Y := (pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj
            ((integralPull l E g agE.integral_mem).obj K))
          ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj))) ∧
    aXF.J.map t ≫
        bX.comparison.hom.app ((agE.raw l E).obj
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.comparison.hom.app
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) =
      agF.comparison.hom.app
          ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj
            ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) ≫
        (derivedPull g agF.coefficient).map (bY.comparison.hom.app
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) ≫
        m.ambient.hom.app (aYE.J.obj
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K)) :=
  by
    let KF := (pbcEmbeddingIntegralTensor l E F i Y.scheme Y.dimension Y.prime_unit).obj K
    let KE := (integralPull l E g agE.integral_mem).obj K
    let L := (integralPull l F g agF.integral_mem).obj KF
    let R := (pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj KE
    let q : L ⟶ R := ObjectProperty.homMk
      ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj)
    refine ⟨(pbcRationalization X.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map q,
      HEq.rfl, ?_⟩
    let QK := (pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K
    let BX := pbcDerivedExtend bX.coefficient
    let BY := pbcDerivedExtend bY.coefficient
    let PE := derivedPull g agE.coefficient
    let PF := derivedPull g agF.coefficient
    let EXE := pbcDerivedExtend (aXE.integralIso.hom ≫ aXE.inclusion)
    let EXF := pbcDerivedExtend (aXF.integralIso.hom ≫ aXF.inclusion)
    let t := (pbcRationalization X.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map q
    let uE := (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj
    let uF := (pbcActualCompletedPullUnit g (pbcIntegralDatum l F)).app KF.obj
    let cX := fun M ↦ (bX.integralBalance l E F i X aXE aXF M).hom
    let cY := (bY.integralBalance l E F i Y aYE aYF K.obj).hom
    let v := BX.map (agE.comparison.inv.app QK ≫ aXE.integral.hom.app KE)
    have hv : v = BX.map (PE.map (aYE.integral.hom.app K) ≫
        agE.ambient.hom.app K.obj ≫ EXE.map uE) :=
      congrArg BX.map (pull_normalization l E g aXE aYE agE K).symm
    have hJ : aXF.J.map t ≫ aXF.integral.hom.app R =
        aXF.integral.hom.app L ≫ EXF.map q.hom := by
      exact aXF.integral.hom.naturality q
    have hX : bX.comparison.hom.app ((agE.raw l E).obj QK) ≫
        BX.map (aXE.integral.hom.app KE) = aXF.integral.hom.app R ≫ cX KE.obj :=
      scalar_normalization l E F i X aXE aXF bX KE
    have hY : bY.comparison.hom.app QK ≫ BY.map (aYE.integral.hom.app K) =
        aYF.integral.hom.app KF ≫ cY :=
      scalar_normalization l E F i Y aYE aYF bY K
    have hm : m.ambient.hom.app (aYE.J.obj QK) ≫
        BX.map (PE.map (aYE.integral.hom.app K)) =
      PF.map (BY.map (aYE.integral.hom.app K)) ≫
        m.ambient.hom.app
          ((pbcDerivedExtend (aYE.integralIso.hom ≫ aYE.inclusion)).obj K.obj) :=
      (m.ambient.hom.naturality (aYE.integral.hom.app K)).symm
    have ho := continuousMixedOrdinaryBalance l E F i g
      aXE aYE aXF aYF agE agF bX bY m K.obj
    have hc := balance_naturality l E F i X aXE aXF bX uE
    have hu := congrArg EXF.map (scalarCompletedPull_unit l E F i g K.obj)
    have hF := pull_normalization l F g aXF aYF agF KF
    change PF.map cY ≫ m.ambient.hom.app
        ((pbcDerivedExtend (aYE.integralIso.hom ≫ aYE.inclusion)).obj K.obj) ≫
        BX.map (agE.ambient.hom.app K.obj) =
      agF.ambient.hom.app KF.obj ≫
        EXF.map ((pbcScalarOrdinaryPullIso l E F i g).hom.app K.obj) ≫
        cX ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) at ho
    change EXF.map ((pbcEmbeddingAmbientTensor l E F i X.scheme).map uE) ≫ cX KE.obj =
      cX ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫
        BX.map (EXE.map uE) at hc
    change EXF.map (uF ≫ q.hom) =
      EXF.map ((pbcScalarOrdinaryPullIso l E F i g).hom.app K.obj ≫
        (pbcEmbeddingAmbientTensor l E F i X.scheme).map uE) at hu
    change PF.map (aYF.integral.hom.app KF) ≫ agF.ambient.hom.app KF.obj ≫ EXF.map uF =
      agF.comparison.inv.app
          ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
        aXF.integral.hom.app L at hF
    have hcancel : BX.map (agE.comparison.hom.app QK) ≫ v =
        BX.map (aXE.integral.hom.app KE) :=
      (BX.map_comp _ _).symm.trans
        (congrArg BX.map (Iso.hom_inv_id_app_assoc agE.comparison QK
          (aXE.integral.hom.app KE)))
    apply (cancel_mono v).1
    change (aXF.J.map t ≫ bX.comparison.hom.app ((agE.raw l E).obj QK) ≫
        BX.map (agE.comparison.hom.app QK)) ≫ v =
      (agF.comparison.hom.app
          ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
        PF.map (bY.comparison.hom.app QK) ≫ m.ambient.hom.app (aYE.J.obj QK)) ≫ v
    have hleft : (aXF.J.map t ≫ bX.comparison.hom.app ((agE.raw l E).obj QK) ≫
        BX.map (agE.comparison.hom.app QK)) ≫ v =
        aXF.integral.hom.app L ≫ EXF.map q.hom ≫ cX KE.obj := by
      calc
        _ = aXF.J.map t ≫ bX.comparison.hom.app ((agE.raw l E).obj QK) ≫
            BX.map (aXE.integral.hom.app KE) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ aXF.J.map t ≫ bX.comparison.hom.app ((agE.raw l E).obj QK) ≫ z)
            hcancel
        _ = aXF.J.map t ≫ aXF.integral.hom.app R ≫ cX KE.obj := by rw [hX]
        _ = _ := by rw [← Category.assoc, hJ, Category.assoc]
    refine hleft.trans ?_
    symm
    calc
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          PF.map (bY.comparison.hom.app QK) ≫
          m.ambient.hom.app (aYE.J.obj QK) ≫
          BX.map (PE.map (aYE.integral.hom.app K)) ≫
          BX.map (agE.ambient.hom.app K.obj) ≫ BX.map (EXE.map uE) := by
        rw [hv]
        simp only [Functor.map_comp, Category.assoc]
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          PF.map (bY.comparison.hom.app QK) ≫
          PF.map (BY.map (aYE.integral.hom.app K)) ≫
          m.ambient.hom.app
            ((pbcDerivedExtend (aYE.integralIso.hom ≫ aYE.inclusion)).obj K.obj) ≫
          BX.map (agE.ambient.hom.app K.obj) ≫ BX.map (EXE.map uE) := by
        rw [reassoc_of% hm]
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          PF.map (aYF.integral.hom.app KF) ≫ PF.map cY ≫
          m.ambient.hom.app
            ((pbcDerivedExtend (aYE.integralIso.hom ≫ aYE.inclusion)).obj K.obj) ≫
          BX.map (agE.ambient.hom.app K.obj) ≫ BX.map (EXE.map uE) := by
        rw [← PF.map_comp_assoc, hY, PF.map_comp, Category.assoc]
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          PF.map (aYF.integral.hom.app KF) ≫ agF.ambient.hom.app KF.obj ≫
          EXF.map ((pbcScalarOrdinaryPullIso l E F i g).hom.app K.obj) ≫
          cX ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫
          BX.map (EXE.map uE) := by
        rw [reassoc_of% ho]
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          PF.map (aYF.integral.hom.app KF) ≫ agF.ambient.hom.app KF.obj ≫
          EXF.map ((pbcScalarOrdinaryPullIso l E F i g).hom.app K.obj) ≫
          EXF.map ((pbcEmbeddingAmbientTensor l E F i X.scheme).map uE) ≫ cX KE.obj := by
        rw [← hc]
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          PF.map (aYF.integral.hom.app KF) ≫ agF.ambient.hom.app KF.obj ≫
          EXF.map uF ≫ EXF.map q.hom ≫ cX KE.obj := by
        simp only [Functor.map_comp] at hu
        rw [reassoc_of% hu.symm]
      _ = agF.comparison.hom.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          agF.comparison.inv.app
            ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj QK) ≫
          aXF.integral.hom.app L ≫ EXF.map q.hom ≫ cX KE.obj := by
        rw [reassoc_of% hF]
      _ = _ := by rw [Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Scheme.ContinuousRational
