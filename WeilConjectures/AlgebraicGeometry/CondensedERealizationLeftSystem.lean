/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedERealizationDefinitions

/-! # Integral operations and left realization comparisons

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
(blueprint: def-weil-pbc-condensed-e-left-system)

The records omit the rational adjunction and the right realization comparison.
Those are constructed by tensor extension and taking mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.CondensedERealization

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Integral restrictions with their ambient adjunction normalization and a left comparison.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-pbc-condensed-e-left-system). -/
structure LeftAlong (T U : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] (rT : At l E T.scheme) (rU : At l E U.scheme) where
  pull : Integral l E U.scheme ⥤ Integral l E T.scheme
  [pullAdditive : pull.Additive]
  [pullLinear : pull.Linear (PbcIntegralRing l E)]
  push : Integral l E T.scheme ⥤ Integral l E U.scheme
  [pushAdditive : push.Additive]
  [pushLinear : push.Linear (PbcIntegralRing l E)]
  pullAmbient : pull ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme
    (pbcIntegralDatum l E)) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
      (pbcIntegralDatum l E).completedPull h
  pushAmbient : push ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme
    (pbcIntegralDatum l E)) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
      (pbcIntegralDatum l E).push h
  integralAdjunction : pull ⊣ push
  integral_unit : ∀ K : Integral l E U.scheme,
    (integralAdjunction.unit.app K).hom ≫ pushAmbient.hom.app (pull.obj K) ≫
        ((pbcIntegralDatum l E).push h).map (pullAmbient.hom.app K) =
      (proEtaleRingDerivedAdjunction h _ _ ((pbcIntegralDatum l E).integralRingIso h)).unit.app
          K.obj ≫
        ((pbcIntegralDatum l E).push h).map
          ((pbcIntegralDatum l E).ordinaryToCompleted h K.obj)
  integral_counit : ∀ K : Integral l E T.scheme,
    (pbcIntegralDatum l E).ordinaryToCompleted h (push.obj K).obj ≫
        pullAmbient.inv.app (push.obj K) ≫ (integralAdjunction.counit.app K).hom =
      ((pbcIntegralDatum l E).pull h).map (pushAmbient.hom.app K) ≫
        (proEtaleRingDerivedAdjunction h _ _
          ((pbcIntegralDatum l E).integralRingIso h)).counit.app K.obj
  pullComparison :
    ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) pull ⋙
        rT.realization.functor ≅
      rU.realization.functor ⋙
        boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := T.model) (Y := U.model)
      (Base.map T U h)

attribute [instance] LeftAlong.pullAdditive LeftAlong.pullLinear
  LeftAlong.pushAdditive LeftAlong.pushLinear

/-- Tensor extension of the integral inverse image.
Source: BS 6.8.15 (blueprint: def-weil-pbc-condensed-e-left-system). -/
abbrev LeftAlong.rationalPull {T U : Base k} {h : T.scheme ⟶ U.scheme}
    [h.IsOver (Spec (.of k))] {rT : At l E T.scheme} {rU : At l E U.scheme}
    (a : LeftAlong l E k T U h rT rU) :=
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) a.pull

/-- Coherent left comparisons, with no right realization comparison or rational adjunction.
Source: BS 6.8.15 (blueprint: def-weil-pbc-condensed-e-left-system). -/
structure LeftSystem (atObject : ∀ T : Base k, At l E T.scheme) where
  along : ∀ (T U : Base k) (h : T.scheme ⟶ U.scheme) [h.IsOver (Spec (.of k))],
    LeftAlong l E k T U h (atObject T) (atObject U)
  integralComp : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))],
    (along T V (h ≫ j)).pull ≅ (along U V j).pull ⋙ (along T U h).pull
  integralComp_normalization : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))]
      (K : Integral l E V.scheme),
    ((integralComp T U V h j).hom.app K).hom ≫
        (along T U h).pullAmbient.hom.app ((along U V j).pull.obj K) ≫
        ((pbcIntegralDatum l E).completedPull h).map
          (X := ((along U V j).pull.obj K).obj)
          (Y := ((pbcIntegralDatum l E).completedPull j).obj K.obj)
          ((along U V j).pullAmbient.hom.app K) =
      (along T V (h ≫ j)).pullAmbient.hom.app K ≫
        ((pbcIntegralDatum l E).completedPullComp h j).hom.app K.obj
  rationalComp : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))],
    (along T V (h ≫ j)).rationalPull ≅
      (along U V j).rationalPull ⋙ (along T U h).rationalPull
  rationalComp_normalization : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))]
      (K : Integral l E V.scheme),
    HEq ((rationalComp T U V h j).hom.app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        (integralComp T U V h j).hom.app K)
  composition : ∀ (T U V : Base k) (h : T.scheme ⟶ U.scheme)
      [h.IsOver (Spec (.of k))] (j : U.scheme ⟶ V.scheme) [j.IsOver (Spec (.of k))]
      (K : Rational l E V.scheme),
    (atObject T).realization.functor.map
        (X := (along T V (h ≫ j)).rationalPull.obj K)
        (Y := (along T U h).rationalPull.obj ((along U V j).rationalPull.obj K))
        ((rationalComp T U V h j).hom.app K) ≫
        (along T U h).pullComparison.hom.app ((along U V j).rationalPull.obj K) ≫
        (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := T.model) (Y := U.model)
      (Base.map T U h)).map
          (X := (atObject U).realization.functor.obj ((along U V j).rationalPull.obj K))
          (Y := (boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
            (Base.map U V j)).obj ((atObject V).realization.functor.obj K))
          ((along U V j).pullComparison.hom.app K) =
      (along T V (h ≫ j)).pullComparison.hom.app K ≫
        (boundedConstructibleUpperStarComp (Profinite.continuousCoefficientRingObj E)
          l (X := T.model) (Y := U.model) (Z := V.model)
            (Base.map T U h) (Base.map U V j)).hom.app ((atObject V).realization.functor.obj K)
  integralId : ∀ T : Base k, (along T T (𝟙 T.scheme)).pull ≅ 𝟭 (Integral l E T.scheme)
  integralId_normalization : ∀ (T : Base k) (K : Integral l E T.scheme),
    (pbcIntegralDatum l E).ordinaryToCompleted (𝟙 T.scheme) K.obj ≫
        (along T T (𝟙 T.scheme)).pullAmbient.inv.app K ≫
        ((integralId T).hom.app K).hom =
      ((pbcIntegralDatum l E).pullId T.scheme).hom.app K.obj
  rationalId : ∀ T : Base k,
    (along T T (𝟙 T.scheme)).rationalPull ≅ 𝟭 (Rational l E T.scheme)
  rationalId_normalization : ∀ (T : Base k) (K : Integral l E T.scheme),
    HEq ((rationalId T).hom.app (ScalarLocalization.mk K))
      ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
        (integralId T).hom.app K)
  condensedId : ∀ T : Base k,
    boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l (𝟙 T.model) ≅
      𝟭 (Constructible E T.scheme)
  condensedId_normalization : ∀ (T : Base k) (K : Constructible E T.scheme),
    (boundedConstructibleUpperStarComp (Profinite.continuousCoefficientRingObj E) l
        (𝟙 T.model) (𝟙 T.model)).hom.app K ≫
      (condensedId T).hom.app
        ((boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (𝟙 T.model)).obj K) =
      𝟙 ((boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
        (𝟙 T.model)).obj K)
  identity : ∀ (T : Base k) (K : Rational l E T.scheme),
    (atObject T).realization.functor.map ((rationalId T).hom.app K) =
      (along T T (𝟙 T.scheme)).pullComparison.hom.app K ≫
        (condensedId T).hom.app ((atObject T).realization.functor.obj K)

end WeilConjectures.CondensedERealization
