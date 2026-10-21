/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.RealizationCompletedPullData
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcUniformCompleteTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Raw rational descent of normalized pullback comparisons

Source: BS Remark 6.8.15 and scalar localization on Hom modules.
(blueprint: lem-weil-pbc-realization-pull-rational-descent). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Pretriangulated

section GeneralTransport
universe r a b a' b' e d
variable (R : Type r) [CommRing R] (p : R)
variable {C : Type a} [Category.{b} C] [Preadditive C] [Linear R C]
  {D : Type a'} [Category.{b'} D] [Preadditive D] [Linear R D]

private def transportIntegral (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization.localization R C p ⋙ ScalarLocalization.transport R p F ≅
      F ⋙ ScalarLocalization.localization R D p :=
  NatIso.ofComponents (fun _ ↦ { hom := 𝟙 _, inv := 𝟙 _ }) (by
    intro X Y f
    dsimp only [Functor.comp_map, ScalarLocalization.localization,
      ScalarLocalization.transport, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp,
      ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
    rfl)

private def transportIso (F G : C ⥤ D) [F.Additive] [F.Linear R]
    [G.Additive] [G.Linear R] (i : F ≅ G) :
    ScalarLocalization.transport R p F ≅ ScalarLocalization.transport R p G := by
  let Q := ScalarLocalization.localization R D p
  refine NatIso.ofComponents (fun K ↦ Q.mapIso (i.app K.obj)) ?_
  intro K L f
  exact ScalarLocalization.transportNat_naturality R p i.hom K L f

private def transportComp {B : Type e} [Category.{d} B] [Preadditive B] [Linear R B]
    (F : C ⥤ D) (G : D ⥤ B) [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] :
    ScalarLocalization.transport R p F ⋙ ScalarLocalization.transport R p G ≅
      ScalarLocalization.transport R p (F ⋙ G) :=
  NatIso.ofComponents (fun _ ↦ { hom := 𝟙 _, inv := 𝟙 _ }) (by
    intro X Y f
    dsimp only [Functor.comp_map, Functor.id_map, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp]
    change (ScalarLocalization.transportHom R p G _ _)
      ((ScalarLocalization.transportHom R p F _ _) f) =
        (ScalarLocalization.transportHom R p (F ⋙ G) _ _) f
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a f => simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul]; rfl
    | add f g hf hg => simp only [map_add, hf, hg])

private def transportId : ScalarLocalization.transport R p (𝟭 C) ≅
    𝟭 (ScalarLocalization R C p) :=
  NatIso.ofComponents (fun _ ↦ { hom := 𝟙 _, inv := 𝟙 _ }) (by
    intro X Y f
    dsimp only [Functor.comp_map, Functor.id_map, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp]
    change (ScalarLocalization.transportHom R p (𝟭 C) _ _) f = f
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a f => simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul]; rfl
    | add f g hf hg => simp only [map_add, hf, hg])

private def rationalComparison (C : Type a) [Category.{b} C] [Preadditive C] [Linear R C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C] :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        erw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        erw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        erw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      erw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      erw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem rawLocalization (C : Type a) [Category.{b} C] [Preadditive C] [Linear R C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C] :
    (ScalarLocalization.localization R C p).IsLocalization
      (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let V := rationalComparison R p C
  have : V.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : V.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : V.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : V.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ V ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, V, ScalarLocalization.localization, rationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
    (Rationalization.W M C) Q V.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm V.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q V.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

end GeneralTransport

section Descent
variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {k : Type u} [Field k]
variable {scalar : ∀ T : RealizationPullScheme l k, RealizationScalarFunctorData l E T.scheme}
variable (arrow : ∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
  RealizationCompletedPullArrow T U h.left (scalar T) (scalar U))

private theorem integralLocalization (T : RealizationPullScheme l k) :
    (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).IsLocalization
      (Rationalization.W (Submonoid.powers (pbcUniformizer l E))
        (PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E))) := by
  let h := pbcIntegralUniformComplete_isTriangulated l E T.scheme
    (RealizationPullScheme.dimension T).out (RealizationPullScheme.invertible T).out
  let : ObjectProperty.IsTriangulated
    (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) := h.2
  exact rawLocalization (PbcIntegralRing l E) (pbcUniformizer l E) _

private def integralUnit {T U : RealizationPullScheme l k} (h : RealizationPullHom T U) :
    (arrow h).integralOrdinary ≅ (arrow h).integralCompleted := by
  refine NatIso.ofComponents (fun K ↦ ?_) ?_
  · let := (arrow h).unit_isIso K
    exact ObjectProperty.isoMk _
      (asIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).app K.obj))
  · intro K L f
    apply ObjectProperty.hom_ext
    exact (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).naturality f.hom

private def rawUnit {T U : RealizationPullScheme l k} (h : RealizationPullHom T U) :
    (arrow h).rationalOrdinary ≅ (arrow h).rationalCompleted := by
  let : (arrow h).integralOrdinary.Additive := (arrow h).ordinaryAdditive
  let : (arrow h).integralOrdinary.Linear (PbcIntegralRing l E) := (arrow h).ordinaryLinear
  let : (arrow h).integralCompleted.Additive := (arrow h).completedAdditive
  let : (arrow h).integralCompleted.Linear (PbcIntegralRing l E) := (arrow h).completedLinear
  exact transportIso (PbcIntegralRing l E) (pbcUniformizer l E)
    (arrow h).integralOrdinary (arrow h).integralCompleted (integralUnit arrow h)

private theorem rawUnit_integral : realizationPullLawRawUnitIntegral scalar arrow (rawUnit arrow) :=
  fun _ _ ↦ rfl

private theorem rawFractions : realizationPullLawRawFractions scalar arrow := by
  intro T U h K L f n
  let : Module (PbcIntegralRing l E) (Localization.Away (pbcUniformizer l E)) :=
    OreLocalization.instModuleOfIsScalarTower
  let : (arrow h).integralOrdinary.Additive := (arrow h).ordinaryAdditive
  let : (arrow h).integralOrdinary.Linear (PbcIntegralRing l E) := (arrow h).ordinaryLinear
  let : (arrow h).integralCompleted.Additive := (arrow h).completedAdditive
  let : (arrow h).integralCompleted.Linear (PbcIntegralRing l E) := (arrow h).completedLinear
  constructor
  · change (ScalarLocalization.transport _ _ (arrow h).integralOrdinary).map _ = _
    change (ScalarLocalization.transportHom (PbcIntegralRing l E) (pbcUniformizer l E)
      (arrow h).integralOrdinary _ _) (_ • (1 ⊗ₜ f)) = _
    erw [map_smul]
    simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
    rfl
  · change (ScalarLocalization.transport _ _ (arrow h).integralCompleted).map _ = _
    change (ScalarLocalization.transportHom (PbcIntegralRing l E) (pbcUniformizer l E)
      (arrow h).integralCompleted _ _) (_ • (1 ⊗ₜ f)) = _
    erw [map_smul]
    simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
    rfl

private def integralAlpha {T U : RealizationPullScheme l k} (h : RealizationPullHom T U) :
    pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
      ((arrow h).rationalCompleted ⋙ realizationPullRationalScalar l E (scalar T)) ≅
    pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
      (realizationPullRationalScalar l E (scalar U) ⋙ (arrow h).continuousPull) := by
  let : (arrow h).integralCompleted.Additive := (arrow h).completedAdditive
  let : (arrow h).integralCompleted.Linear (PbcIntegralRing l E) := (arrow h).completedLinear
  exact
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (transportIntegral (PbcIntegralRing l E) (pbcUniformizer l E)
          (arrow h).integralCompleted) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (arrow h).integralCompleted
        (realizationPullIntegral l E (scalar T)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      (arrow h).alpha ≪≫
      Functor.isoWhiskerRight (realizationPullIntegral l E (scalar U)).symm _ ≪≫
      Functor.associator _ _ _

private def rationalAlpha {T U : RealizationPullScheme l k} (h : RealizationPullHom T U) :
    (arrow h).rationalCompleted ⋙ realizationPullRationalScalar l E (scalar T) ≅
      realizationPullRationalScalar l E (scalar U) ⋙ (arrow h).continuousPull := by
  let := (integralLocalization (E := E) U)
  let Q := pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
  let H := (Functor.whiskeringLeft _ _
    (DerivedCategory (pbcModules T.scheme (rationalCoefficientSheaf l T.scheme E)))).obj Q
  have : H.Full := Localization.full_whiskeringLeft Q
    (Rationalization.W (Submonoid.powers (pbcUniformizer l E))
      (PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))) _
  have : H.Faithful := Localization.faithful_whiskeringLeft Q
    (Rationalization.W (Submonoid.powers (pbcUniformizer l E))
      (PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))) _
  exact H.preimageIso (integralAlpha arrow h)

private theorem rationalAlpha_app {T U : RealizationPullScheme l k}
    (h : RealizationPullHom T U)
    (K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) :
    (rationalAlpha arrow h).hom.app
      ((pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
        (integralAlpha arrow h).hom.app K := by
  let := (integralLocalization (E := E) U)
  let Q := pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
  let H := (Functor.whiskeringLeft _ _
    (DerivedCategory (pbcModules T.scheme (rationalCoefficientSheaf l T.scheme E)))).obj Q
  have : H.Full := Localization.full_whiskeringLeft Q
    (Rationalization.W (Submonoid.powers (pbcUniformizer l E))
      (PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))) _
  have : H.Faithful := Localization.faithful_whiskeringLeft Q
    (Rationalization.W (Submonoid.powers (pbcUniformizer l E))
      (PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))) _
  change (H.map (H.preimage (integralAlpha arrow h).hom)).app K = _
  exact NatTrans.congr_app (H.map_preimage _) K

private theorem rationalAlpha_integral :
    realizationPullLawRationalAlphaIntegral scalar arrow (rationalAlpha arrow) := by
  intro T U h K
  erw [rationalAlpha_app]
  simp only [integralAlpha, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  change (realizationPullRationalScalar l E (scalar T)).map (𝟙 _) ≫
    (realizationPullIntegral l E (scalar T)).hom.app ((arrow h).integralCompleted.obj K) ≫
      (arrow h).alpha.hom.app K ≫
        (arrow h).continuousPull.map ((realizationPullIntegral l E (scalar U)).inv.app K) ≫
        (arrow h).continuousPull.map ((realizationPullIntegral l E (scalar U)).hom.app K) = _
  erw [(realizationPullRationalScalar l E (scalar T)).map_id, Category.id_comp,
    ← (arrow h).continuousPull.map_comp, Iso.inv_hom_id_app,
    (arrow h).continuousPull.map_id, Category.comp_id]

variable (completedComp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) j.left) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) h.left) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)) ⋙
      pbcActualStrictCompletedPull (pbcIntegralDatum l E) (h ≫ j).left)

private def integralComp {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V) :
    (arrow j).integralCompleted ⋙ (arrow h).integralCompleted ≅
      (arrow (h ≫ j)).integralCompleted :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ ((completedComp h j).app K)) (by
    intro K L f
    apply ObjectProperty.hom_ext
    exact (completedComp h j).hom.naturality f)

private def rawComp {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V) :
    (arrow j).rationalCompleted ⋙ (arrow h).rationalCompleted ≅
      (arrow (h ≫ j)).rationalCompleted := by
  let : (arrow h).integralCompleted.Additive := (arrow h).completedAdditive
  let : (arrow h).integralCompleted.Linear (PbcIntegralRing l E) := (arrow h).completedLinear
  let : (arrow j).integralCompleted.Additive := (arrow j).completedAdditive
  let : (arrow j).integralCompleted.Linear (PbcIntegralRing l E) := (arrow j).completedLinear
  let : (arrow (h ≫ j)).integralCompleted.Additive := (arrow (h ≫ j)).completedAdditive
  let : (arrow (h ≫ j)).integralCompleted.Linear (PbcIntegralRing l E) :=
    (arrow (h ≫ j)).completedLinear
  exact transportComp (PbcIntegralRing l E) (pbcUniformizer l E)
      (arrow j).integralCompleted (arrow h).integralCompleted ≪≫
    transportIso (PbcIntegralRing l E) (pbcUniformizer l E)
      ((arrow j).integralCompleted ⋙ (arrow h).integralCompleted)
      (arrow (h ≫ j)).integralCompleted
      (integralComp arrow completedComp h j)

private theorem rawComp_integral :
    realizationPullLawRawCompIntegral scalar arrow completedComp (rawComp arrow completedComp) := by
  intro T U V h j K
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private def integralId (T : RealizationPullScheme l k) :
    (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).integralCompleted ≅ 𝟭 _ := by
  let h : RealizationPullHom T T := 𝟙 _
  let i : (arrow h).integralOrdinary ≅ 𝟭 _ :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
      ((pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T.scheme).app K.obj)) (by
        intro K L f
        apply ObjectProperty.hom_ext
        exact (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T.scheme).hom.naturality f.hom)
  exact (integralUnit arrow h).symm ≪≫ i

private def rawId (T : RealizationPullScheme l k) :
    (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).rationalCompleted ≅ 𝟭 _ := by
  let h : RealizationPullHom T T := 𝟙 _
  let : (arrow h).integralCompleted.Additive := (arrow h).completedAdditive
  let : (arrow h).integralCompleted.Linear (PbcIntegralRing l E) := (arrow h).completedLinear
  exact transportIso (PbcIntegralRing l E) (pbcUniformizer l E)
      (arrow h).integralCompleted (𝟭 _) (integralId arrow T) ≪≫
    transportId (PbcIntegralRing l E) (pbcUniformizer l E)

private theorem rawId_integral :
    realizationPullLawRawIdIntegral scalar arrow (rawId arrow) := by
  intro T K
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

variable (rationalComp : ∀ {T U V : RealizationPullScheme l k}
    (h : RealizationPullHom T U) (j : RealizationPullHom U V),
    (arrow j).continuousPull ⋙ (arrow h).continuousPull ≅ (arrow (h ≫ j)).continuousPull)
variable (continuousId : ∀ T : RealizationPullScheme l k,
    (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).continuousPull ≅ 𝟭 _)

private theorem rationalAlpha_formula {T U : RealizationPullScheme l k}
    (h : RealizationPullHom T U)
    (K : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) :
    (rationalAlpha arrow h).hom.app ⟨K⟩ =
      (realizationPullIntegral l E (scalar T)).hom.app ((arrow h).integralCompleted.obj K) ≫
        (arrow h).alpha.hom.app K ≫
          (arrow h).continuousPull.map ((realizationPullIntegral l E (scalar U)).inv.app K) := by
  apply (cancel_mono ((arrow h).continuousPull.map
    ((realizationPullIntegral l E (scalar U)).hom.app K))).mp
  erw [rationalAlpha_integral arrow h K]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    (arrow h).continuousPull.map_id]
  erw [Category.comp_id]

private theorem rawAlpha_comp
    (ha : realizationPullLawAlphaComp scalar arrow rationalComp completedComp) :
    realizationPullLawRawAlphaComp scalar arrow (rationalAlpha arrow) rationalComp
      (rawComp arrow completedComp) := by
  intro T U V h j K
  let f := (integralComp arrow completedComp h j).hom.app K.obj
  let I := realizationPullIntegral l E (scalar T)
  let IV := realizationPullIntegral l E (scalar V)
  let F := pbcDerivedExtend (realizationPullScalarMap l E (scalar T))
  let J := realizationPullRationalScalar l E (scalar T)
  have hn := I.hom.naturality f
  change J.map ((pbcRationalization T.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map f) ≫ _ = _ at hn
  have hc := (rationalComp h j).hom.naturality (IV.inv.app K.obj)
  change (arrow h).continuousPull.map ((arrow j).continuousPull.map _) ≫ _ = _ at hc
  erw [rawComp_integral arrow completedComp h j K.obj]
  change J.map ((pbcRationalization T.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map f) ≫ _ = _
  have ha' : F.map f.hom ≫ (arrow (h ≫ j)).alpha.hom.app K.obj = _ := ha h j K.obj
  erw [rationalAlpha_formula arrow (h ≫ j) K.obj,
    ← Category.assoc, hn, Category.assoc]
  have ha'' := congrArg (fun z ↦ I.hom.app
    (((arrow j).integralCompleted ⋙ (arrow h).integralCompleted).obj K.obj) ≫ z ≫
      (arrow (h ≫ j)).continuousPull.map (IV.inv.app K.obj)) ha'
  simp only [Category.assoc] at ha''
  apply ha''.trans
  erw [rationalAlpha_formula arrow h ((arrow j).integralCompleted.obj K.obj),
    rationalAlpha_formula arrow j K.obj]
  simp only [Functor.map_comp, Category.assoc]
  have hu : (arrow h).continuousPull.map
      ((realizationPullIntegral l E (scalar U)).inv.app
        ((arrow j).integralCompleted.obj K.obj)) ≫
      (arrow h).continuousPull.map
        ((realizationPullIntegral l E (scalar U)).hom.app
          ((arrow j).integralCompleted.obj K.obj)) = 𝟙 _ := by
    erw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (arrow h).continuousPull.map_id _
  erw [← Category.assoc ((arrow h).continuousPull.map
    ((realizationPullIntegral l E (scalar U)).inv.app
      ((arrow j).integralCompleted.obj K.obj))), hu, Category.id_comp]
  erw [hc]
  rfl

private theorem rawAlpha_id
    (ha : realizationPullLawAlphaId scalar arrow continuousId) :
    realizationPullLawRawAlphaId scalar arrow (rationalAlpha arrow) continuousId (rawId arrow) := by
  intro T K
  let h : RealizationPullHom T T := 𝟙 _
  let f := (integralId arrow T).hom.app K.obj
  let I := realizationPullIntegral l E (scalar T)
  let F := pbcDerivedExtend (realizationPullScalarMap l E (scalar T))
  let J := realizationPullRationalScalar l E (scalar T)
  have hn := I.hom.naturality f
  change J.map ((pbcRationalization T.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map f) ≫ _ = _ at hn
  have he := (continuousId T).hom.naturality (I.inv.app K.obj)
  have hi : (arrow h).alpha.hom.app K.obj ≫ (continuousId T).hom.app (F.obj K.obj.obj) =
      F.map f.hom := by
    let := (arrow h).unit_isIso K.obj
    apply (cancel_epi (F.map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h.left).app K.obj.obj))).mp
    rw [← Category.assoc]
    have hid := ha T K.obj
    change F.map _ ≫ (arrow h).alpha.hom.app K.obj ≫ _ = _ at hid
    rw [Category.assoc]
    apply hid.trans
    rw [← F.map_comp]
    simp only [f, integralId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      integralUnit, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
      ObjectProperty.isoMk_inv, ObjectProperty.isoMk_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, asIso_inv]
    erw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rfl
  erw [rawId_integral arrow T K.obj]
  change _ = J.map ((pbcRationalization T.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map f)
  apply (cancel_mono (I.hom.app K.obj)).mp
  erw [hn, rationalAlpha_formula arrow h K.obj]
  simp only [Category.assoc]
  erw [← Category.assoc ((arrow h).continuousPull.map _), he]
  simp only [Functor.id_map, Category.assoc, Iso.inv_hom_id_app]
  have hif := congrArg (I.hom.app ((arrow h).integralCompleted.obj K.obj) ≫ ·) hi
  erw [Category.comp_id]
  exact hif

/-- Descent of normalized integral comparisons to the unchanged objects of raw
scalar localization.
Source: BS Remark 6.8.15 and scalar localization of Hom modules
(blueprint: lem-weil-pbc-realization-pull-rational-descent).

Proof: tensor the actual linear ordinary and completed restrictions on Hom modules.
The integral completion unit, completed compositor and completed identity give
natural isomorphisms after tensoring; their components are the integral tensors
with one. The scalar localization is also the Verdier rationalization: the
rational Hom equivalence identifies its tensors with localized morphisms.
Consequently restriction along Q is fully faithful on functor categories. Lift
the integral alpha, conjugated by the scalar functor's integral isomorphisms,
through this restriction. Its normalization follows by cancelling the integral
isomorphisms. Naturality of those isomorphisms and the supplied integral alpha
composition and identity laws give the rational laws on every object, because
all rational objects are unchanged integral objects. Finally linear tensor
extension preserves the specified uniformizer denominator of every fraction. -/
theorem realizationPullRationalDescent
    (hc : realizationPullLawAlphaComp scalar arrow rationalComp completedComp)
    (hi : realizationPullLawAlphaId scalar arrow continuousId) :
    ∃ rationalAlpha : (∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
      (arrow h).rationalCompleted ⋙ realizationPullRationalScalar l E (scalar T) ≅
        realizationPullRationalScalar l E (scalar U) ⋙ (arrow h).continuousPull),
      realizationPullLawRationalAlphaIntegral scalar arrow rationalAlpha ∧
      realizationPullLawRawFractions scalar arrow ∧
    ∃ rawUnit : (∀ {T U : RealizationPullScheme l k} (h : RealizationPullHom T U),
      (arrow h).rationalOrdinary ≅ (arrow h).rationalCompleted),
      realizationPullLawRawUnitIntegral scalar arrow rawUnit ∧
    ∃ rawComp : (∀ {T U V : RealizationPullScheme l k}
      (h : RealizationPullHom T U) (j : RealizationPullHom U V),
      (arrow j).rationalCompleted ⋙ (arrow h).rationalCompleted ≅
        (arrow (h ≫ j)).rationalCompleted),
      realizationPullLawRawCompIntegral scalar arrow completedComp rawComp ∧
    ∃ rawId : (∀ T : RealizationPullScheme l k,
      (arrow (𝟙 (Over.mk (T.scheme ↘ Spec (.of k))))).rationalCompleted ≅ 𝟭 _),
      realizationPullLawRawIdIntegral scalar arrow rawId ∧
      realizationPullLawRawAlphaComp scalar arrow rationalAlpha rationalComp rawComp ∧
      realizationPullLawRawAlphaId scalar arrow rationalAlpha continuousId rawId := by
  exact ⟨rationalAlpha arrow, rationalAlpha_integral arrow, rawFractions arrow,
    rawUnit arrow, rawUnit_integral arrow, rawComp arrow completedComp,
    rawComp_integral arrow completedComp, rawId arrow, rawId_integral arrow,
    rawAlpha_comp arrow completedComp rationalComp hc,
    rawAlpha_id arrow continuousId hi⟩

end Descent

end WeilConjectures
