/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink

/-! # Admissibility of the four actual coefficient representatives
Source: latest blueprint sk-lem-finite, coefficient convention
(blueprint: lem-sf-finite-point-coefficient-admissibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing

private def finiteCoefficientIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A] :
    letI : TopologicalSpace (Shrink.{0} A) := ⊥
    letI : DiscreteTopology (Shrink.{0} A) := ⟨rfl⟩
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousMapRingObj (Shrink.{0} A)) := by
  let B := Shrink.{0} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let e : A ≃+* B := (Shrink.ringEquiv.{0} A).symm
  let h : Profinite.continuousCoefficientRingSheaf A ⟶
      Profinite.continuousMapRingSheaf B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheaf B ⟶
      Profinite.continuousCoefficientRingSheaf A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let e' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e'.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  exact Mon.mkIso' e'

private theorem finiteCoefficient_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] [Finite A] (hA : ∃ n : ℕ, (ℓ ^ n : A) = 0) :
    IsLocalizingAdmissibleCoefficient ℓ (Profinite.continuousCoefficientRingObj A) := by
  let B := Shrink.{0} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  refine Or.inl ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨finiteCoefficientIso A⟩⟩
  obtain ⟨n, hn⟩ := hA
  refine ⟨n, fun a ↦ ?_⟩
  have hz : (ℓ ^ n : B) = 0 := by
    apply (Shrink.ringEquiv.{0} A).injective
    simpa only [map_pow, map_natCast, map_zero] using hn
  rw [nsmul_eq_mul]
  rw [Nat.cast_pow, hz, zero_mul]

private theorem quotient_annihilated
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (n : ℕ) :
    (ℓ ^ n : Padic.coefficientExtensionRing ℓ E n) = 0 := by
  let O := Padic.coefficientExtensionIntegers ℓ E
  let π := Padic.coefficientExtensionUniformizer ℓ E
  have h := (Padic.extension_integers_dvr ℓ E (Padic.coefficientExtensionAbsoluteValue ℓ E)
    (spectralNorm_extends (K := Padic ℓ) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal ℓ E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hval : Padic.coefficientExtensionAbsoluteValue ℓ E (ℓ : E) < 1 := by
    have hext := spectralNorm_extends (K := Padic ℓ) (L := E) (ℓ : Padic ℓ)
    change spectralNorm (Padic ℓ) E (ℓ : E) < 1
    simpa only [map_natCast] using hext.trans_lt (Padic.norm_p_lt_one (p := ℓ))
  have hl : (ℓ : O) ∈ Ideal.span ({π} : Set O) := by
    rw [hgen]
    exact (h.2.1 (ℓ : O)).mpr hval
  have hp : (ℓ : O) ^ n ∈ Padic.coefficientExtensionIdeal ℓ E n :=
    Ideal.pow_mem_pow hl n
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  simpa only [map_pow, map_natCast] using hz

/-- The spectral valuation-ring and quotient representatives used in cohomology are
admissible, as are the two recorded rational representatives.

Source: latest blueprint sk-lem-finite, first paragraph and coefficient convention
(blueprint: lem-sf-finite-point-coefficient-admissibility).

Proof: the positive spectral quotients are finite and discrete. The rational prime lies
in the maximal ideal, so its nth power vanishes in the nth uniformizer-power quotient.
Shrink that finite ring to Type 0 and postcompose continuous functions with the ring
equivalence; this gives the required condensed monoid isomorphism. The proved spectral
valuation-ring comparison identifies the lifted integer coefficient with the recorded
embedded integer coefficient. Sheaf composition retains unit and multiplication.
The finite-extension and algebraic-closure cases are reflexive admissibility witnesses.
-/
theorem finite_point_coefficient_admissibility (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ n : ℕ, 1 ≤ n → IsLocalizingAdmissibleCoefficient ℓ
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n)) ∧
    IsLocalizingAdmissibleCoefficient ℓ (DerivedNakayama.integerRing ℓ (ULift.{u} E)) ∧
    IsLocalizingAdmissibleCoefficient ℓ (Profinite.continuousMapRingObj.{u} E) ∧
    IsLocalizingAdmissibleCoefficient ℓ (Profinite.padicAlgClRingObj.{u} ℓ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    let nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E)).toNormedField
    let : NormedField (ULift.{u} E) := nf
    let : TopologicalSpace (ULift.{u} E) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let := DerivedNakayama.quotientDiscrete ℓ (ULift.{u} E) n
    let := Padic.finite_coefficientExtensionRing ℓ (ULift.{u} E) n hn
    exact finiteCoefficient_admissible ℓ _ ⟨n, quotient_annihilated ℓ (ULift.{u} E) n⟩
  · let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
    let e := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
    have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨(Mon.mkIso' e).symm⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

end AlgebraicGeometry.ProEtale.CondensedRing
