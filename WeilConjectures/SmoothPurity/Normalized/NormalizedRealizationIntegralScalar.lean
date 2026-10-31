/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Integral scalar maps in normalized continuous coefficient charts

Source: Bhatt--Scholze 6.8.2, finite quotient and inverse-limit coefficient realizations.
(blueprint: lem-pur-normalized-realization-integral-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

-- The elementary scalar-unit argument also appears in AdicFiniteExchangeEncoding;
-- keeping it local avoids importing its unrelated derived smooth-exchange theory.
private theorem finite_constant_unit
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (W : Scheme.{u}) (n : ℕ) :
    pbcFunctionScalars W d n = Functor.whiskerRight
      (toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
        (pbcLevelConstantComparison W d n).hom.hom)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e := AdicCoefficients.finiteRingComparison W (ProEtale.PbcQuotient d n)
  have he : Functor.whiskerRight (toSheafify (ProEt.topology W)
        (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
        AdicCoefficients.finiteRingUnit W (ProEtale.PbcQuotient d n) :=
    (AdicCoefficients.finiteRingComparison_exists W
      (ProEtale.PbcQuotient d n)).choose_spec.1.2
  have hconst : toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient d n))) ≫
      (pbcLevelConstantComparison W d n).hom.hom =
        AdicCoefficients.constants W (ProEtale.PbcQuotient d n) ≫
          toSheafify (ProEt.topology W)
            (AdicCoefficients.functionPresheaf W (ProEtale.PbcQuotient d n)) := by
    ext U b
    exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b
  rw [hconst]
  apply (cancel_mono e.hom.hom).1
  have hi : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg
    (fun f : AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ⟶
      AdicCoefficients.finiteRingPresentation W (ProEtale.PbcQuotient d n) ↦ f.hom)
    e.inv_hom_id
  change (ProEtale.finiteCoefficientScalarMap W (ProEtale.PbcQuotient d n) ≫
    e.inv.hom) ≫ e.hom.hom = _
  erw [Category.assoc, hi]
  erw [Category.comp_id]
  erw [Functor.whiskerRight_comp, Category.assoc, he]
  rfl

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})

private theorem finite_chart (A : CondensedERealization.At l E W) (n : ℕ) :
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        (A.finiteIso n).hom =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
        continuousCoefficientConstantComparison W (finiteCoefficientRing l E n) := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteContinuousCoefficientSheaf l W E n).property
  have hu := finite_constant_unit (pbcIntegralDatum l E) W n
  ext V a
  apply ContinuousMap.ext
  intro x
  have hn := A.finite_normalization n V a x
  have hunit := congrArg (fun z ↦ (z.app V).hom a) hu
  change _ = _ at hunit
  rw [hunit] at hn
  have hmap := congr_app (toSheafify_naturality (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map (integralCoefficientULift l E n).toCommRingCatIso.hom)) V
  have hmap' := ConcreteCategory.congr_hom hmap a
  have hc := continuousCoefficientConstantComparison_unit W (finiteCoefficientRing l E n)
  have hc' := ConcreteCategory.congr_hom (congr_app hc V)
    (integralCoefficientULift l E n a)
  let e := (integralCoefficientULift l E n).toCommRingCatIso.hom
  let η := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)))
  let η' := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))
  let q := continuousCoefficientConstantComparison W (finiteCoefficientRing l E n)
  let m := sheafifyMap (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).map e)
  change (η'.app V) (e a) = (m.app V) ((η.app V) a) at hmap'
  change (q.hom.app V) ((η'.app V) (e a)) = ContinuousMap.const V.unop.left
    (show finiteCoefficientRing l E n from e a) at hc'
  let f : C(V.unop.left, finiteCoefficientRing l E n) :=
    (A.finiteIso n).hom.hom.app V
      ((pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom.hom.app V
        ((η.app V) a))
  change f x = e a at hn
  let g : C(V.unop.left, finiteCoefficientRing l E n) :=
    q.hom.app V ((m.app V) ((η.app V) a))
  change f x = g x
  rw [hn]
  have hg : g = ContinuousMap.const V.unop.left
      (show finiteCoefficientRing l E n from e a) := by
    change (q.hom.app V) ((m.app V) ((η.app V) a)) = _
    rw [← hmap']
    exact hc'
  exact (congrArg (fun z : C(V.unop.left, finiteCoefficientRing l E n) ↦ z x) hg).symm

private theorem finite_scalar_chart (AE : CondensedERealization.At l E W)
    (AF : CondensedERealization.At l F W) (n : ℕ) :
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    let : TopologicalSpace (finiteCoefficientRing l F n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l F n) := ⟨rfl⟩
    let q : finiteCoefficientRing l E n →+* finiteCoefficientRing l F n :=
      (integralCoefficientULift l F n).toRingHom.comp
      ((pbcScalarQuotientMap l E F i n).comp
        (integralCoefficientULift l E n).symm.toRingHom)
    AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) ≫
        (AF.finiteIso n).hom =
      (AE.finiteIso n).hom ≫ continuousCoefficientMap q continuous_of_discreteTopology W := by
  let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  let : TopologicalSpace (finiteCoefficientRing l F n) := ⊥
  let : DiscreteTopology (finiteCoefficientRing l F n) := ⟨rfl⟩
  let q : finiteCoefficientRing l E n →+* finiteCoefficientRing l F n :=
      (integralCoefficientULift l F n).toRingHom.comp
    ((pbcScalarQuotientMap l E F i n).comp
      (integralCoefficientULift l E n).symm.toRingHom)
  apply (cancel_epi (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).mp
  have hn :
      (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (pbcScalarQuotientMap l E F i n)) ≫
        (pbcLevelConstantComparison W (pbcIntegralDatum l F) n).hom := by
    exact (scalarLevelConstantComparison_naturality W (pbcIntegralDatum l E)
      (pbcIntegralDatum l F) n (pbcScalarQuotientMap l E F i n)).symm
  conv_lhs =>
    erw [← Category.assoc, hn, Category.assoc, finite_chart l F W AF n]
  conv_rhs =>
    erw [← Category.assoc, finite_chart l E W AE n, Category.assoc]
  erw [← discreteConstantComparison_naturality W (CommRingCat.ofHom q)]
  have hm : CommRingCat.ofHom (pbcScalarQuotientMap l E F i n) ≫
        (integralCoefficientULift l F n).toCommRingCatIso.hom =
      (integralCoefficientULift l E n).toCommRingCatIso.hom ≫ CommRingCat.ofHom q := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (integralCoefficientULift l E n).symm_apply_apply a |>.symm
      |> congrArg (fun a ↦ integralCoefficientULift l F n
        (pbcScalarQuotientMap l E F i n a))
  conv_lhs => erw [← Category.assoc, ← Functor.map_comp]
  conv_rhs => erw [← Category.assoc, ← Functor.map_comp]
  erw [hm]
  rfl

/-- In residue-normalized integral charts, completed coefficient extension acts pointwise
by the given field embedding. Source: Bhatt--Scholze 6.8.2, finite quotients and their limit
(blueprint: lem-pur-normalized-realization-integral-scalar).
Proof: finite chart normalization identifies each finite chart with the constant-sheaf
comparison. Naturality on constants therefore proves the scalar square at every finite
level. Apply the completed scalar map's projection equation and the integral chart's
reduction equation. Every residue of the target value is the residue of the embedded
source value. The valuation ring is the inverse limit of its positive finite quotients,
so equality of those residues gives equality of integral values, hence of field values.
The argument is sectionwise and also applies to empty test objects. -/
theorem normalizedRealizationIntegralScalar
    (AE : CondensedERealization.At l E W) (AF : CondensedERealization.At l F W)
    (U : W.ProEtᵒᵖ) (b : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E).obj.obj U)
    (x : U.unop.left) :
    (integralCoefficientValue l F W U
      ((AE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i W ≫ AF.integralIso.hom).hom.app
        U b) x).val = i (integralCoefficientValue l E W U b x).val := by
  let c := AE.integralIso.inv ≫ pbcScalarCoefficientMap l E F i W ≫ AF.integralIso.hom
  let q (n : ℕ) : finiteCoefficientRing l E n →+* finiteCoefficientRing l F n :=
    (integralCoefficientULift l F n).toRingHom.comp
    ((pbcScalarQuotientMap l E F i n).comp
      (integralCoefficientULift l E n).symm.toRingHom)
  have hq (n : ℕ) (a : Padic.coefficientExtensionIntegers l E) :
      q n (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) =
        ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))
          (integralScalarIntegerInclusion l E F i a)) := by
    change integralCoefficientULift l F n
      (pbcScalarQuotientMap l E F i n ((integralCoefficientULift l E n).symm _)) = _
    have hE : integralCoefficientULift l E n
        (Ideal.Quotient.mk _ (ULift.up a)) =
          ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) :=
      (integralCoefficientULift_exists l E n).exists.choose_spec (ULift.up a)
    rw [← hE, RingEquiv.symm_apply_apply]
    change integralCoefficientULift l F n
      (Ideal.Quotient.mk _ (pbcEmbeddingIntegerMap l E F i (ULift.up a))) = _
    exact (integralCoefficientULift_exists l F n).exists.choose_spec _
  have hres (n : ℕ) :
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))
          (integralCoefficientValue l F W U (c.hom.app U b) x) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (n + 1))
          (integralScalarIntegerInclusion l E F i (integralCoefficientValue l E W U b x)) := by
    let : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    let : TopologicalSpace (finiteCoefficientRing l F n) := ⊥
    let : DiscreteTopology (finiteCoefficientRing l F n) := ⟨rfl⟩
    have hs : c ≫ AF.integralIso.inv ≫ pbcAdicProjection W (pbcIntegralDatum l F) n ≫
          (AF.finiteIso n).hom =
        (AE.integralIso.inv ≫ pbcAdicProjection W (pbcIntegralDatum l E) n ≫
          (AE.finiteIso n).hom) ≫ continuousCoefficientMap (q n)
            continuous_of_discreteTopology W := by
      simp only [c, Category.assoc, Iso.hom_inv_id_assoc]
      have hp : pbcScalarCoefficientMap l E F i W ≫
          pbcAdicProjection W (pbcIntegralDatum l F) n =
          pbcAdicProjection W (pbcIntegralDatum l E) n ≫
            AdicCoefficients.coefficientMap W (pbcScalarQuotientMap l E F i n) :=
        (pbcScalarCoefficientMap_exists l E F i W).exists.choose_spec n
      rw [reassoc_of% hp]
      erw [Category.assoc]
      erw [finite_scalar_chart l E F i W AE AF n]
      erw [Category.assoc, Category.assoc]
      rfl
    have hv := congrArg (fun z ↦
      (finiteContinuousCoefficientValue l F W n U (z.hom.app U b) x).down) hs
    have he := AE.integral_normalization n U b x
    have hf := AF.integral_normalization n U (c.hom.app U b) x
    rw [← hf]
    change (finiteContinuousCoefficientValue l F W n U
      ((c ≫ AF.integralIso.inv ≫ pbcAdicProjection W (pbcIntegralDatum l F) n ≫
        (AF.finiteIso n).hom).hom.app U b) x).down = _
    rw [hv]
    change (q n (finiteContinuousCoefficientValue l E W n U
      ((AE.integralIso.inv ≫ pbcAdicProjection W (pbcIntegralDatum l E) n ≫
        (AE.finiteIso n).hom).hom.app U b) x)).down = _
    rw [← ULift.up_down (finiteContinuousCoefficientValue l E W n U
      ((AE.integralIso.inv ≫ pbcAdicProjection W (pbcIntegralDatum l E) n ≫
        (AE.finiteIso n).hom).hom.app U b) x), he, hq]
  obtain ⟨⟨e, he, _⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l F
  have h : integralCoefficientValue l F W U (c.hom.app U b) x =
      integralScalarIntegerInclusion l E F i (integralCoefficientValue l E W U b x) := by
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    exact hres n
  exact congrArg Subtype.val h

end WeilConjectures
