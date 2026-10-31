/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
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
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.AlgebraicGeometry.QcqsIntegralFiniteModelCompleteness
import all WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import all WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageReductionCone
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.FiniteModelSheafQuotientConstructible
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Ordinary integral exchange under arbitrary qcqs base change

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6, Theorem 7.7 and Section 3;
Bhatt--Scholze, Section 6.7, Lemma 6.7.5; latest blueprint, convolution-kernel proof step 2
(blueprint: lem-fd-integral-arbitrary-pullback-reduction).

The residue is positive quotient level zero, namely O_E/pi. All operations are the
ordinary uncompleted derived operations. The endpoint comparisons below are composites
of the normalized balancing comparison and its actual direct-image adjunction mate.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open QuotientChange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] proofSectionDerived

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStarFromPoint

private noncomputable def continuousRingIso
    {A B : Type u} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousCoefficientRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

@[irreducible] private noncomputable def integerLatticeIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (ProEtale.integralCondensedRing l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l E) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := ProEtale.latticeCoefficientIntegers l E
  let B := Padic.coefficientExtensionIntegers l E
  let e : A ≃+* B :=
    { toFun := fun x ↦ ⟨x.val.ofAbs, x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ x.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact continuousRingIso e he.continuous he'.continuous

private theorem integerModel_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) X)) :
    IsConstructibleModuleObject (condensedRingObj
      (ProEtale.DerivedNakayama.integerRing l E) X) M ↔
      ProEtale.IsConstantModelConstructible (ProEtale.DerivedNakayama.integerRing l E) X M :=
  ProEtale.comparison_transport (integerLatticeIso l E) X
    (ProEtale.integralLfpConstantModelComparison l E X) M

private theorem complete_of_constant_model (V : Scheme.{u})
    [CompactSpace V] [QuasiSeparatedSpace V]
    (K : DerivedCategory (AdicCompletion.Modules l E V))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) V K) :
    IsDerivedComplete l E V K := by
  have := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.integerRing l E) V).1
  obtain ⟨hi, ht⟩ := complete_triangulated l E V
  let := hi
  let := ht
  exact DerivedCategory.prop_of_bounded (IsDerivedComplete l E V)
    (IsConstantModelConstructible (DerivedNakayama.integerRing l E) V)
    (complete_sheaf l E V) K hK.1 hK.2

/-- The source comparison: inverse balancing along g, followed by Lg_A^*(rho_h).
It is a natural transformation, built from the specified scalar-adjunction mate.
Source: HRS Section 3; BS Lemma 6.7.5, first residue comparison
(blueprint: lem-fd-integral-arbitrary-pullback-reduction). -/
def integralResidueSourceComparison
    (b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      D (DerivedNakayama.reductionRing l E 1) T ⋙
          L (DerivedNakayama.quotientRing l E 1) f ≅
        L (DerivedNakayama.integerRing l E) f ⋙
          D (DerivedNakayama.reductionRing l E 1) S)
    {Z Y Y' : Scheme.{u}} (h : Z ⟶ Y) (g : Y' ⟶ Y) :
    (F (DerivedNakayama.integerRing l E) h ⋙ L (DerivedNakayama.integerRing l E) g) ⋙
        D (DerivedNakayama.reductionRing l E 1) Y' ⟶
      D (DerivedNakayama.reductionRing l E 1) Z ⋙
        (F (DerivedNakayama.quotientRing l E 1) h ⋙
          L (DerivedNakayama.quotientRing l E 1) g) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (b g).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (rho (DerivedNakayama.reductionRing l E 1) h (b h)) _ ≫
    (Functor.associator _ _ _).hom

/-- The target comparison: rho_h' followed by Rh'_{*,A} of inverse balancing along a.
The comparisons are constructed before any isomorphism or completeness assertion.
Source: HRS Section 3; BS Lemma 6.7.5, second residue comparison
(blueprint: lem-fd-integral-arbitrary-pullback-reduction). -/
def integralResidueTargetComparison
    (b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      D (DerivedNakayama.reductionRing l E 1) T ⋙
          L (DerivedNakayama.quotientRing l E 1) f ≅
        L (DerivedNakayama.integerRing l E) f ⋙
          D (DerivedNakayama.reductionRing l E 1) S)
    {Z' Z Y' : Scheme.{u}} (a : Z' ⟶ Z) (h' : Z' ⟶ Y') :
    (L (DerivedNakayama.integerRing l E) a ⋙ F (DerivedNakayama.integerRing l E) h') ⋙
        D (DerivedNakayama.reductionRing l E 1) Y' ⟶
      D (DerivedNakayama.reductionRing l E 1) Z ⋙
        (L (DerivedNakayama.quotientRing l E 1) a ⋙
          F (DerivedNakayama.quotientRing l E 1) h') :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (rho (DerivedNakayama.reductionRing l E 1) h' (b h')) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (b a).inv _ ≫
    (Functor.associator _ _ _).hom

/-- The first residue in normalized ordinary coordinates, with its retained bounded
constructible etale antecedent. This specializes the existing encoding and witness to the
actual first reduction; the final condition is on the antecedent itself.
Source: HRS Theorem 7.7; BS Section 6.7, first finite reduction
(blueprint: lem-fd-integral-arbitrary-pullback-reduction). -/
def IntegralResidueBoundedEtaleOrigin (Z : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E Z)) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ∃ e : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E 1) Z,
    ∃ q : DerivedCategory.TStructure.t.plus
        (e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E Z 0).obj M)),
    ∃ w : Scheme.FixedEtaleOriginWitness Z
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))
        ⟨e.fixedDerived.functor.obj ((AdicCompletion.derivedReduction l E Z 0).obj M), q⟩,
      Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))) Z
        w.complex.obj

private theorem residue_origin_of_constant_model (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (M : DerivedCategory (AdicCompletion.Modules l E Z))
    (hM : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) Z M) :
    IntegralResidueBoundedEtaleOrigin l E Z M := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E 1
  let : TopologicalSpace A := AdicCompletion.finiteTopology l E 1
  obtain ⟨hf, hd, _⟩ :=
    FiniteModelQuotient.finite_model_sheaf_quotient_constructible l E Z
      ((DerivedCategory.homologyFunctor _ 0).obj M) (hM.2 0) 0
  let : Finite A := hf
  let : DiscreteTopology A := hd
  obtain ⟨e⟩ := FiniteDiscreteOrdinary.encoding_exists A Z
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E Z 0)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (AdicCompletion.derivedReduction l E Z 0).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  have : e.fixedDerived.functor.IsTriangulated := by
    change (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  let F := AdicCompletion.derivedReduction l E Z 0 ⋙ e.fixedDerived.functor
  let B := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} A)) Z
  have : F.IsTriangulated := by dsimp only [F]; infer_instance
  have : B.IsTriangulated := by dsimp only [B]; infer_instance
  have : B.IsClosedUnderIsomorphisms := by dsimp only [B]; infer_instance
  have := (constantModelConstructibleFiniteTor_wellDefined
    (DerivedNakayama.integerRing l E) Z).1
  have hB : B (F.obj M) := by
    apply _root_.DerivedCategory.prop_of_bounded (B.inverseImage F)
      (IsConstantModelConstructible (DerivedNakayama.integerRing l E) Z) ?_
      M hM.1 hM.2
    intro N hN
    obtain ⟨_, _, _, hred, _⟩ :=
      FiniteModelQuotient.finite_model_sheaf_quotient_constructible l E Z N hN 0
    have hord := (FiniteDiscreteOrdinary.encoding_constructibility A Z e).2 _ |>.mp hred
    apply DerivedCategory.boundedConstructible_of_homology (ULift.{u + 1} A) hord.1
    intro q
    exact (isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _).mp
      ((ordinary_constructible_iff A Z _).mp (hord.2 q))
  have hI := DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic _ hB
  obtain ⟨N, hN, ⟨i⟩⟩ := hB
  exact ⟨e, hI.1.1, ⟨⟨N, hN.1.1⟩, i⟩, hN⟩

private theorem residue_balancing_exists {S T : Scheme.{u}} (f : S ⟶ T) :
    ∃ b : D (DerivedNakayama.reductionRing l E 1) T ⋙
        L (DerivedNakayama.quotientRing l E 1) f ≅
      L (DerivedNakayama.integerRing l E) f ⋙
        D (DerivedNakayama.reductionRing l E 1) S,
      PullNormalized (DerivedNakayama.reductionRing l E 1) f b :=
  internal_pull_normalization_exists (DerivedNakayama.reductionRing l E 1) f

private theorem residue_rho_isIso {S T : Scheme.{u}} (f : S ⟶ T)
    (b : D (DerivedNakayama.reductionRing l E 1) T ⋙
        L (DerivedNakayama.quotientRing l E 1) f ≅
      L (DerivedNakayama.integerRing l E) f ⋙
        D (DerivedNakayama.reductionRing l E 1) S)
    (hb : PullNormalized (DerivedNakayama.reductionRing l E 1) f b) :
    IsIso (rho (DerivedNakayama.reductionRing l E 1) f b) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  obtain ⟨tS, tT, _, _, _, htS, htT, _⟩ :=
    internal_scalar_pullback_normalization (DerivedNakayama.reductionRing l E 1) f
  apply ((internal_scalar_mate_projection (DerivedNakayama.reductionRing l E 1)
    f tS tT b htS htT hb).2.2.2.2.1 K).mpr
  exact scalarProjection_dualizable (DerivedNakayama.reductionRing l E 1) f K
    (finiteCoefficient_dualizable l E T 0)

private theorem reorient_comparison {C : Type*} [Category* C]
    {W X Y Z : C} (i : W ≅ X) (j : Y ≅ Z)
    (p : X ⟶ Z) (q : W ⟶ Y) (h : i.hom ≫ p = q ≫ j.hom) :
    p ≫ j.inv = i.inv ≫ q := by
  apply (cancel_epi i.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem integral_endpoint_properties
    (Z Y : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
    [CompactSpace Y] [IsLocallyNoetherian Y] (h : Z ⟶ Y) [IsProper h]
    (Y' : Scheme.{u}) [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (Z' : Scheme.{u}) (a : Z' ⟶ Z) (h' : Z' ⟶ Y')
    (sq : ChosenCartesianSquare a h' h g)
    (M : DerivedCategory (AdicCompletion.Modules l E Z))
    (hM : boundedConstructible (AdicCompletion.ring l E Z) M)
    (hMh : boundedConstructible (AdicCompletion.ring l E Y)
      ((F (DerivedNakayama.integerRing l E) h).obj M)) :
    IsDerivedComplete l E Y'
        ((L (DerivedNakayama.integerRing l E) g).obj
          ((F (DerivedNakayama.integerRing l E) h).obj M)) ∧
    IsDerivedComplete l E Y'
        ((F (DerivedNakayama.integerRing l E) h').obj
          ((L (DerivedNakayama.integerRing l E) a).obj M)) ∧
    IntegralResidueBoundedEtaleOrigin l E Z M := by
  let : IsNoetherian Z := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let : IsProper h' := by
    rw [← sq.hom_snd]
    infer_instance
  let : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace h'
  let : QuasiSeparatedSpace Z' := quasiSeparatedSpace_of_quasiSeparated h'
  have constant {T : Scheme.{u}} [IsNoetherian T]
      (K : DerivedCategory (AdicCompletion.Modules l E T))
      (hK : boundedConstructible (AdicCompletion.ring l E T) K) :
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T K := by
    exact ⟨hK.1, fun n ↦
      (integerModel_comparison l E T _).mp (hK.2 n)⟩
  have hconstM := constant M hM
  have hconstH := constant _ hMh
  have hpullM := pullback_bounded_constructible (DerivedNakayama.integerRing l E) a
    (pullback_constructible (DerivedNakayama.integerRing l E) a) M hconstM
  have hpullH := pullback_bounded_constructible (DerivedNakayama.integerRing l E) g
    (pullback_constructible (DerivedNakayama.integerRing l E) g) _ hconstH
  obtain ⟨_, hpush⟩ := internal_integral_direct_image_limits l E h'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [L, CondensedRing.moduleObjectDerivedPullback] using
      complete_of_constant_model l E Y' _ hpullH
  · simpa only [L, F, CondensedRing.moduleObjectDerivedPullback,
      CondensedRing.moduleObjectDerivedPushforward] using
      (hpush _).1 (complete_of_constant_model l E Z' _ hpullM)
  · exact residue_origin_of_constant_model l E Z M hconstM

private theorem residue_source_isIso
    (b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      D (DerivedNakayama.reductionRing l E 1) T ⋙
          L (DerivedNakayama.quotientRing l E 1) f ≅
        L (DerivedNakayama.integerRing l E) f ⋙
          D (DerivedNakayama.reductionRing l E 1) S)
    (hb : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      PullNormalized (DerivedNakayama.reductionRing l E 1) f (b f))
    {Z Y Y' : Scheme.{u}} (h : Z ⟶ Y) (g : Y' ⟶ Y)
    (M : DerivedCategory (AdicCompletion.Modules l E Z)) :
    IsIso ((integralResidueSourceComparison l E b h g).app M) := by
  have := residue_rho_isIso l E h (b h) (hb h)
  have : IsIso (integralResidueSourceComparison l E b h g) := by
    dsimp only [integralResidueSourceComparison]
    infer_instance
  infer_instance

private theorem residue_target_isIso
    (b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      D (DerivedNakayama.reductionRing l E 1) T ⋙
          L (DerivedNakayama.quotientRing l E 1) f ≅
        L (DerivedNakayama.integerRing l E) f ⋙
          D (DerivedNakayama.reductionRing l E 1) S)
    (hb : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      PullNormalized (DerivedNakayama.reductionRing l E 1) f (b f))
    {Z' Z Y' : Scheme.{u}} (a : Z' ⟶ Z) (h' : Z' ⟶ Y')
    (M : DerivedCategory (AdicCompletion.Modules l E Z)) :
    IsIso ((integralResidueTargetComparison l E b a h').app M) := by
  have := residue_rho_isIso l E h' (b h') (hb h')
  have : IsIso (integralResidueTargetComparison l E b a h') := by
    dsimp only [integralResidueTargetComparison]
    infer_instance
  infer_instance

private theorem source_comparison_app
    {C₀ D₀ E₀ C₁ D₁ E₁ : Type*}
    [Category* C₀] [Category* D₀] [Category* E₀]
    [Category* C₁] [Category* D₁] [Category* E₁]
    (R : C₀ ⥤ D₀) (L : D₀ ⥤ E₀)
    (c : C₀ ⥤ C₁) (d : D₀ ⥤ D₁) (e : E₀ ⥤ E₁)
    (R' : C₁ ⥤ D₁) (L' : D₁ ⥤ E₁)
    (r : R ⋙ d ⟶ c ⋙ R') (b : d ⋙ L' ≅ L ⋙ e) (M : C₀) :
    ((Functor.associator R L e).hom ≫ Functor.whiskerLeft R b.inv ≫
      (Functor.associator R d L').inv ≫ Functor.whiskerRight r L' ≫
        (Functor.associator c R' L').hom).app M =
      b.inv.app (R.obj M) ≫ L'.map (r.app M) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem target_comparison_app
    {C₀ D₀ E₀ C₁ D₁ E₁ : Type*}
    [Category* C₀] [Category* D₀] [Category* E₀]
    [Category* C₁] [Category* D₁] [Category* E₁]
    (L : C₀ ⥤ D₀) (R : D₀ ⥤ E₀)
    (c : C₀ ⥤ C₁) (d : D₀ ⥤ D₁) (e : E₀ ⥤ E₁)
    (L' : C₁ ⥤ D₁) (R' : D₁ ⥤ E₁)
    (r : R ⋙ e ⟶ d ⋙ R') (b : c ⋙ L' ≅ L ⋙ d) (M : C₀) :
    ((Functor.associator L R e).hom ≫ Functor.whiskerLeft L r ≫
      (Functor.associator L d R').inv ≫ Functor.whiskerRight b.inv R' ≫
        (Functor.associator c L' R').hom).app M =
      r.app (L.obj M) ≫ R'.map (b.inv.app M) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem abstract_inverse_rectangle
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {rf : A₁ ⥤ A₀} {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂} {a : A₁ ⥤ A₃}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {cb : B₀ ⥤ B₂} {rgb : B₃ ⥤ B₂}
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (e : rf ⋙ c ⟶ a ⋙ rg) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (la : T₁ ⋙ ab ≅ a ⋙ T₃) (lc : T₀ ⋙ cb ≅ c ⋙ T₂) (J : A₁)
    (h : mateRouteLeft cb r eb la.hom J = mateRouteRight T₂ lc.hom e t J) :
    T₂.map (e.app J) ≫
        ((Functor.associator a rg T₂).hom ≫ Functor.whiskerLeft a t ≫
          (Functor.associator a T₃ rgb).inv ≫ Functor.whiskerRight la.inv rgb ≫
            (Functor.associator T₁ ab rgb).hom).app J =
      ((Functor.associator rf c T₂).hom ≫ Functor.whiskerLeft rf lc.inv ≫
        (Functor.associator rf T₀ cb).inv ≫ Functor.whiskerRight r cb ≫
          (Functor.associator T₁ rfb cb).hom).app J ≫ eb.app (T₁.obj J) := by
  have hs := source_comparison_app rf c T₁ T₀ T₂ rfb cb r lc J
  have ht := target_comparison_app a rg T₁ T₃ T₂ ab rgb t la J
  rw [hs, ht]
  dsimp only [mateRouteLeft, mateRouteRight] at h
  let i := lc.app (rf.obj J)
  let j := rgb.mapIso (la.app J)
  let p := T₂.map (e.app J) ≫ t.app (a.obj J)
  let q := cb.map (r.app J) ≫ eb.app (T₁.obj J)
  have he : i.hom ≫ p = q ≫ j.hom := by
    simpa only [i, j, p, q, Functor.mapIso_hom, Iso.app_hom,
      Functor.comp_obj, Category.assoc] using h.symm
  simpa only [i, j, p, q, Functor.mapIso_inv, Iso.app_inv,
    Functor.comp_obj, Category.assoc] using reorient_comparison i j p q he

private theorem abstract_scalar_rectangle
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]
    (φ : Λ ⟶ Λ') [IsMonHom φ]
    (b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      D φ T ⋙ L Λ' f ≅ L Λ f ⋙ D φ S)
    (hb : ∀ {S T : Scheme.{u}} (f : S ⟶ T), PullNormalized φ f (b f))
    {Z' Z Y' Y : Scheme.{u}}
    {a : Z' ⟶ Z} {h' : Z' ⟶ Y'} {h : Z ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare a h' h g) (M : DerivedCategory (Modules Λ Z)) :
    scalarExchangeLeft φ sq b M = scalarExchangeRight φ sq b M :=
  (scalar_geometric_exchange_rectangle φ sq b hb M).1

section
attribute [local irreducible] rho scalarAmbientExchange

private theorem residue_exchange
    (b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      D (DerivedNakayama.reductionRing l E 1) T ⋙
          L (DerivedNakayama.quotientRing l E 1) f ≅
        L (DerivedNakayama.integerRing l E) f ⋙
          D (DerivedNakayama.reductionRing l E 1) S)
    (hb : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
      PullNormalized (DerivedNakayama.reductionRing l E 1) f (b f))
    {Z' Z Y' Y : Scheme.{u}}
    {a : Z' ⟶ Z} {h' : Z' ⟶ Y'} {h : Z ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare a h' h g)
    (M : DerivedCategory (AdicCompletion.Modules l E Z)) :
    (D (DerivedNakayama.reductionRing l E 1) Y').map
          ((scalarAmbientExchange (DerivedNakayama.integerRing l E) sq).app M) ≫
        (integralResidueTargetComparison l E b a h').app M =
      (integralResidueSourceComparison l E b h g).app M ≫
        (scalarAmbientExchange (DerivedNakayama.quotientRing l E 1) sq).app
          ((D (DerivedNakayama.reductionRing l E 1) Z).obj M) := by
  exact abstract_inverse_rectangle
    (rf := F (DerivedNakayama.integerRing l E) h)
    (c := L (DerivedNakayama.integerRing l E) g)
    (rg := F (DerivedNakayama.integerRing l E) h')
    (a := L (DerivedNakayama.integerRing l E) a)
    (T₀ := D (DerivedNakayama.reductionRing l E 1) Y)
    (T₁ := D (DerivedNakayama.reductionRing l E 1) Z)
    (T₂ := D (DerivedNakayama.reductionRing l E 1) Y')
    (T₃ := D (DerivedNakayama.reductionRing l E 1) Z')
    (rfb := F (DerivedNakayama.quotientRing l E 1) h)
    (ab := L (DerivedNakayama.quotientRing l E 1) a)
    (cb := L (DerivedNakayama.quotientRing l E 1) g)
    (rgb := F (DerivedNakayama.quotientRing l E 1) h')
    (rho (DerivedNakayama.reductionRing l E 1) h (b h))
    (rho (DerivedNakayama.reductionRing l E 1) h' (b h'))
    (scalarAmbientExchange (DerivedNakayama.integerRing l E) sq)
    (scalarAmbientExchange (DerivedNakayama.quotientRing l E 1) sq)
    (b a) (b g) M
    (abstract_scalar_rectangle (DerivedNakayama.reductionRing l E 1) b hb sq M)


end

/-- Completeness of both ordinary integral exchange endpoints and normalization of its
first residue reduction, for a proper map between Noetherian schemes and arbitrary qcqs
base change. The displayed comparisons are natural in the input complex. Their balancing
maps are pinned by their computation counits, and rho is the specified adjunction mate.
The origin clause retains the normalized ordinary finite encoding, a bounded-below
etale antecedent with its specified iso, and bounded constructibility of that antecedent.

Source: HRS Propositions 5.1 and 7.6, Theorem 7.7 and Section 3; BS Lemma 6.7.5;
latest blueprint, lem-fd-convolution-kernel proof step 2
(blueprint: lem-fd-integral-arbitrary-pullback-reduction).

Proof:
1. Proper base change and qcqs permanence give qcqs for Z'.
2. Identify the integral coefficient presentation with the lattice presentation by its
isometric ring equivalence. Transport the constructibility comparison and pull back
bounded constant-model constructibility along a and g using exact inverse image.
3. Bounded induction from complete constructible sheaves proves completeness of La^*M
and U. The canonical direct-image/limit theorem then proves completeness of V.
4. Apply the first-quotient constructibility calculation to sheaves, followed by the
normalized finite discrete encoding. Bounded induction gives a bounded constructible
etale antecedent of the first reduction of M, retaining its actual comparison iso.
5. Choose normalized balancing maps for the actual residue coefficient morphism.
The finite coefficient is dualizable, so its projection map is invertible. The
normalized scalar-mate equation makes rho invertible for every geometric morphism.
Thus both displayed endpoint comparison composites are invertible.
6. Apply the scalar-geometric exchange rectangle and cancel the invertible balancing
maps on its two sides to get the stated equality in its specified orientation.
No extra Tor-amplitude, Noetherianity, dimension, characteristic or field-base
hypothesis on Y' or Z' is used. -/
theorem integral_arbitrary_pullback_reduction :
    ∃ b : ∀ {S T : Scheme.{u}} (f : S ⟶ T),
        D (DerivedNakayama.reductionRing l E 1) T ⋙
            L (DerivedNakayama.quotientRing l E 1) f ≅
          L (DerivedNakayama.integerRing l E) f ⋙
            D (DerivedNakayama.reductionRing l E 1) S,
      (∀ {S T : Scheme.{u}} (f : S ⟶ T),
        PullNormalized (DerivedNakayama.reductionRing l E 1) f (b f)) ∧
      ∀ (Z Y : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z]
          [CompactSpace Y] [IsLocallyNoetherian Y]
          (h : Z ⟶ Y) [IsProper h]
          (Y' : Scheme.{u}) [CompactSpace Y'] [QuasiSeparatedSpace Y']
          (g : Y' ⟶ Y) (Z' : Scheme.{u}) (a : Z' ⟶ Z) (h' : Z' ⟶ Y')
          (sq : ChosenCartesianSquare a h' h g)
          (M : DerivedCategory (AdicCompletion.Modules l E Z)),
        boundedConstructible (AdicCompletion.ring l E Z) M →
        boundedConstructible (AdicCompletion.ring l E Y)
          ((F (DerivedNakayama.integerRing l E) h).obj M) →
        IsDerivedComplete l E Y'
            ((L (DerivedNakayama.integerRing l E) g).obj
              ((F (DerivedNakayama.integerRing l E) h).obj M)) ∧
        IsDerivedComplete l E Y'
            ((F (DerivedNakayama.integerRing l E) h').obj
              ((L (DerivedNakayama.integerRing l E) a).obj M)) ∧
        IntegralResidueBoundedEtaleOrigin l E Z M ∧
        IsIso ((integralResidueSourceComparison l E b h g).app M) ∧
        IsIso ((integralResidueTargetComparison l E b a h').app M) ∧
        (D (DerivedNakayama.reductionRing l E 1) Y').map
              ((scalarAmbientExchange (DerivedNakayama.integerRing l E) sq).app M) ≫
            (integralResidueTargetComparison l E b a h').app M =
          (integralResidueSourceComparison l E b h g).app M ≫
            (scalarAmbientExchange (DerivedNakayama.quotientRing l E 1) sq).app
              ((D (DerivedNakayama.reductionRing l E 1) Z).obj M) := by
  classical
  choose b hb using @residue_balancing_exists l _ E _ _ _
  refine ⟨b, hb, ?_⟩
  intro Z Y _ _ _ _ h _ Y' _ _ g Z' a h' sq M hM hMh
  obtain ⟨hU, hV, hO⟩ := integral_endpoint_properties l E
    Z Y h Y' g Z' a h' sq M hM hMh
  have hS := residue_source_isIso l E b hb h g M
  have hT := residue_target_isIso l E b hb a h' M
  have hE := residue_exchange l E b hb sq M
  exact ⟨hU, hV, hO, hS, hT, hE⟩

end AlgebraicGeometry.ProEtale
