/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
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
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.IntegralPointNakayamaUpperBound
import WeilConjectures.AlgebraicGeometry.FinitePointCoefficientAdmissibility
import WeilConjectures.AlgebraicGeometry.FinitePointFiniteOrdinaryBound
import WeilConjectures.AlgebraicGeometry.FinitePointCompactHeartUpperBound
import WeilConjectures.AlgebraicGeometry.IntegralPositiveReductionConstructible
import all WeilConjectures.AlgebraicGeometry.ConstructibleFiniteHeart
import WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageReductionCone
import WeilConjectures.SixFunctors.AdmissibleDirectImage
import WeilConjectures.AlgebraicGeometry.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.Compactification.Over
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import Mathlib.Algebra.CharP.CharAndCard

/-! # Integral native upper bounds for cohomology of a sheaf

Source: current blueprint, sk-lem-finite.proof.md, integral Complement
(blueprint: lem-sf-finite-point-integral-heart-upper-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject
namespace AlgebraicGeometry.ProEtale.CondensedRing

section Auxiliary
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]

private theorem integral_direct_images_ctf (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    ∀ Q ∈ [(rightDerivedLowerShriekOfCompactification Λ c).obj K.obj,
      (lowerStar Λ X.hom).rightDerivedFunctor.obj K.obj],
      (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
        DerivedCategory.finiteTorAmplitude _) Q := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
  let : X.hom.IsOver (Spec (.of k)) := ⟨by
    change X.hom ≫ 𝟙 _ = X.hom
    exact Category.comp_id _⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType ((Spec (.of k)) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (𝟙 (Spec (.of k)))
    infer_instance
  have : QuasiCompact ((Spec (.of k)) ↘ Spec (.of k)) := by
    change QuasiCompact (𝟙 (Spec (.of k)))
    infer_instance
  have : IsSeparated ((Spec (.of k)) ↘ Spec (.of k)) := by
    change IsSeparated (𝟙 (Spec (.of k)))
    infer_instance
  have ho := (openImmersionLowerShriek_localizing ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos Fact.out Λ hΛ c.i).1 K
  have hc := (properLocalizingHypotheses_admissible ℓ Λ hΛ k c.g).1 ⟨_, ho⟩
  have hn := constructibleFiniteTor_rightDerivedLowerStar_of_admissible ℓ k Λ hΛ
    X.hom K.obj K.property
  intro Q hQ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl
  · exact hc
  · exact hn

end Auxiliary

private theorem constant_model_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply constantModelConstructible_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

private theorem reduction_isLE (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (b : ℤ) [K.IsLE b] :
    ((AdicCompletion.derivedReduction l E X 0).obj K).IsLE b := by
  let q := AdicCompletion.quotient l E X 0
  let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0) ⥤ AdicCompletion.Modules l E X := Mod.comap q
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction q
  change DerivedCategory.TStructure.t.IsLE _ b
  rw [DerivedCategory.TStructure.t.isLE_iff_orthogonal b (b + 1) rfl]
  intro Z f hZ
  have : Z.IsGE (b + 1) := hZ
  have : (G.mapDerivedCategory.obj Z).IsGE (b + 1) :=
    G.isGE_mapDerivedCategory_obj Z (b + 1)
  have hz : adj.homEquiv K Z f = 0 :=
    DerivedCategory.TStructure.t.zero _ b (b + 1) (by omega)
  have hz0 : adj.homEquiv K Z 0 = 0 := by
    rw [Adjunction.homEquiv_unit]
    simp only [Functor.map_zero, comp_zero]
  exact (adj.homEquiv K Z).injective (hz.trans hz0.symm)

private def firstReductionPushIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E Y 0).obj
        ((lowerStar (DerivedNakayama.integerRing l E) f).rightDerivedFunctor.obj K) ≅
      (lowerStar (DerivedNakayama.quotientRing l E 1) f).rightDerivedFunctor.obj
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  have : IsIso (integralReductionPullbackMap l E f 0) :=
    (internal_integral_direct_image_limits l E f).choose
  have : IsIso (integralFiniteProjection l E f 0 K) :=
    ((internal_integral_direct_image_limits l E f).choose_spec K).2
  exact asIso (integralFiniteProjection l E f 0 K)

private def firstReductionCompactIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E Y 0).obj
        ((rightDerivedLowerShriekOfCompactification (DerivedNakayama.integerRing l E) c).obj K) ≅
      (rightDerivedLowerShriekOfCompactification (DerivedNakayama.quotientRing l E 1) c).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K) :=
  firstReductionPushIso l E c.g
      ((openImmersionLowerShriek (DerivedNakayama.integerRing l E) c.i).mapDerivedCategory.obj K)
    ≪≫ (lowerStar (DerivedNakayama.quotientRing l E 1) c.g).rightDerivedFunctor.mapIso
      ((derivedOpenImmersionShriekIso (DerivedNakayama.reductionRing l E 1) c.i).app K)

/-- Integral native heart bound: for a constant-model constructible module `M` over
`𝒪_E = integerRing ℓ (ULift E)` on a separated finite-type `X` over the finite field with
`dim X = d`, both the native compact direct image and the ordinary direct image of `M` in
degree zero are concentrated in degrees `≤ 2d`.
Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Complement: the degree-zero finite, integral, E and Qbar estimates (integral clause).

Proof: the integral residue criterion puts the degree-zero input in the constructible
finite-Tor category. Direct-image stability makes both integral outputs bounded with
constructible cohomology. First uniformizer reduction of the input is bounded constructible
and concentrated in degrees at most zero. The finite-coefficient heart bounds extend to this
complex by finite truncation devissage. The canonical finite projection comparison, and
its compatibility with extension by zero for the compact image, identify these finite outputs
with the reductions of the integral outputs. At the geometric point, abelian Nakayama for
finite presentations and descending induction on the top cohomology degree reflect the
upper bound 2d from residue reduction to each integral output.
(blueprint: lem-sf-finite-point-integral-heart-upper-bound)
-/
theorem finite_point_integral_heart_upper_bound
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) :
    ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ),
    ∀ (X : Over (Spec (.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (c : Compactification X.hom)
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.left)),
      IsConstantModelConstructible
        (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.left M →
      ∀ d : ℕ, topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ∀ P ∈ [(rightDerivedLowerShriekOfCompactification
          (DerivedNakayama.integerRing ℓ (ULift.{u} E)) c).obj
          ((DerivedCategory.singleFunctor _ 0).obj M),
        (lowerStar (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.hom).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)],
        P.IsLE (2 * (d : ℤ)) := by
  intro E X _ _ _ c M hM d hd P hP
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) := ⟨by
    rw [ringChar.eq D.k D.p]
    exact hℓ.symm⟩
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  let O := DerivedNakayama.integerRing ℓ (ULift.{u} E)
  let A := DerivedNakayama.quotientRing ℓ (ULift.{u} E) 1
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  have hKbc : constantModelBoundedConstructible O X.left K :=
    constant_model_single O X.left M hM
  have hKctf : (constantModelBoundedConstructible O X.left ⊓
      DerivedCategory.finiteTorAmplitude _) K := by
    rw [← (internal_integral_residue_criterion ℓ (ULift.{u} E) X.left).2]
    exact hKbc
  have hPbc := (integral_direct_images_ctf O D.k ℓ
    (finite_point_coefficient_admissibility ℓ E).2.1 X c ⟨K, hKctf⟩ P hP).1
  let Q := (AdicCompletion.derivedReduction ℓ (ULift.{u} E) X.left 0).obj K
  have hQ : constantModelBoundedConstructible A X.left Q :=
    integralReduction_constantModelBoundedConstructible ℓ (ULift.{u} E) X.left K hKbc 0
  have : Q.IsLE 0 := reduction_isLE ℓ (ULift.{u} E) X.left K 0
  let S := IsConstantModelConstructible A X.left
  let := (constantModelConstructibleFiniteTor_wellDefined A X.left).1
  let : ObjectProperty.ContainsZero S := ⟨⟨0, isZero_zero _,
    constantModelConstructible_of_isZero A X.left _ (isZero_zero _)⟩⟩
  have hfiniteCompact :
      ((rightDerivedLowerShriekOfCompactification A c).obj Q).IsLE (2 * (d : ℤ)) := by
    have hb := DerivedCategory.isLE_obj_of_isLE_of_homologyProperty
      (rightDerivedLowerShriekOfCompactification A c) (2 * (d : ℤ)) S
      (fun N hN ↦ finite_point_compact_heart_upper_bound_split D ℓ hℓ E 1 le_rfl
        X c N hN d hd) Q hQ.1 hQ.2 0
    simpa only [zero_add] using hb
  have hfiniteOrdinary :
      ((lowerStar A X.hom).rightDerivedFunctor.obj Q).IsLE (2 * (d : ℤ)) := by
    have hb := DerivedCategory.isLE_obj_of_isLE_of_homologyProperty
      (lowerStar A X.hom).rightDerivedFunctor (2 * (d : ℤ)) S
      (fun N hN ↦ finite_point_finite_ordinary_bound ℓ E 1 le_rfl X N hN d hd.le)
      Q hQ.1 hQ.2 0
    simpa only [zero_add] using hb
  have hred : ((AdicCompletion.derivedReduction ℓ (ULift.{u} E)
      (Spec (.of D.k)) 0).obj P).IsLE (2 * (d : ℤ)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact DerivedCategory.TStructure.t.isLE_of_iso
        (firstReductionCompactIso ℓ (ULift.{u} E) c K).symm (2 * (d : ℤ))
    · exact DerivedCategory.TStructure.t.isLE_of_iso
        (firstReductionPushIso ℓ (ULift.{u} E) X.hom K).symm (2 * (d : ℤ))
  exact integral_point_isLE_of_residue_isLE ℓ (ULift.{u} E) D.k P hPbc (2 * (d : ℤ))

end AlgebraicGeometry.ProEtale.CondensedRing
