/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Topology.KrullDimension
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
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import all WeilConjectures.AlgebraicGeometry.FinitePointCoefficientAdmissibility
import all WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # The sharp finite-coefficient native ordinary bound
Source: latest blueprint sk-lem-finite, finite-coefficient Complement
(blueprint: lem-sf-finite-point-finite-ordinary-bound).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- A native ordinary direct-image bound for finite discrete coefficients.

Source: latest blueprint sk-lem-finite, finite-coefficient Complement
(blueprint: lem-sf-finite-point-finite-ordinary-bound).

Proof: finite-coefficient encoding carries the constructible internal module to an
ordinary pro-etale module, and constructible origin supplies an etale model. The
etale dimension theorem bounds its derived direct image by twice the source dimension.
The bounded-below direct-image comparison identifies this with the pro-etale image.
Conjugating pushforward by the exact coefficient-encoding equivalences identifies
the latter with the native internal-module direct image. Exact derived encoding and
comparison pullback preserve the upper bound; transport it through these canonical
isomorphisms. The annihilator is positive also for the zero coefficient ring.
-/
private theorem finiteDiscrete_ordinary_bound
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] (n : ℕ) (hn : (ℓ : T) ^ n = 0)
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj T) X.left) F)
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞)) :
    ((R((f.left)_*⟦Profinite.continuousMapRingObj T⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE (2 * (d : ℤ)) := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} T
  have : IsMonHom eR.hom := heR
  obtain ⟨G, hG, hforget⟩ := internalModuleAb_equivalence (ULift.{u + 1} T)
  have : G.IsEquivalence := hG
  let ES := finiteDiscreteCoefficientEquivalence T eR G hforget X.left
  let ET := finiteDiscreteCoefficientEquivalence T eR G hforget Y.left
  obtain ⟨L, hL, ⟨eL⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    (ULift.{u + 1} T) (finiteDiscreteCoefficient_constructible T eR G hforget X.left F hF)
  have : Scheme.IsConstructibleSheaf L := hL
  let A := ModuleCat.{u + 1} (ULift.{u + 1} T)
  let K := (DerivedCategory.singleFunctor _ 0).obj L
  have hAtors : IsAddTorsion (ULift.{u + 1} T) := by
    intro x
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨ℓ ^ n, pow_pos (Fact.out : ℓ.Prime).pos _, ?_⟩
    rw [nsmul_eq_mul]
    have hz : (ℓ ^ n : ULift.{u + 1} T) = 0 := by
      apply (ULift.ringEquiv : ULift.{u + 1} T ≃+* T).injective
      simpa only [map_pow, map_natCast, map_zero] using hn
    rw [Nat.cast_pow, hz, zero_mul]
  have hb : ((Etale.lowerStar A f.left).rightDerivedFunctor.obj K).IsLE (2 * (d : ℤ)) := by
    have := Etale.isLE_rightDerivedLowerStar_obj (ULift.{u + 1} T) hAtors
      X.hom Y.hom f.left (Over.w f) d hd K 0
    simpa only [zero_add] using this
  let N := comparisonUpperStar A Y.left
  have hNb := N.isLE_mapDerivedCategory_obj
    ((Etale.lowerStar A f.left).rightDerivedFunctor.obj K) (2 * (d : ℤ))
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : QuasiCompact f.left := inferInstance
  have : QuasiSeparated f.left := inferInstance
  have hm : IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} T) f.left K) :=
    unboundedDirectImageComparison_boundedBelow (ULift.{u + 1} T) f.left K 0
  let I := lowerStar (Profinite.continuousMapRingObj T) f.left
  let H := ProEtale.lowerStar A f.left
  let i := encodingPushforwardNatIso T eR G hforget Y.left X.left f.left
  let j : (ES.functor ⋙ I) ⋙ ET.inverse ≅ H :=
    Functor.associator _ _ _ ≪≫ Iso.inverseCompIso (G := ES.symm) i
  let k : H ⋙ ET.functor ≅ ES.functor ⋙ I :=
    (Iso.isoCompInverse (H := ET.symm) j).symm
  let comparisonD : R(H) ⋙ D(ET.functor) ≅ D(ES.functor) ⋙ R(I) :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H ET.functor).symm ≪≫
      Functor.rightDerivedFunctorNatIso k ≪≫
      Functor.rightDerivedFunctorCompIso ES.functor I ≪≫
      Functor.isoWhiskerRight ES.functor.rightDerivedFunctorIsoMapDerivedCategory R(I)
  let eF : ES.functor.obj ((comparisonUpperStar A X.left).obj L) ≅ F :=
    ES.functor.mapIso eL ≪≫ ES.counitIso.app F
  let eS := ES.functor.mapDerivedCategory.mapIso
      (((comparisonUpperStar A X.left).mapDerivedCategorySingleFunctor 0).app L) ≪≫
    (ES.functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso eF
  let e := ET.functor.mapDerivedCategory.mapIso
      (asIso (unboundedDirectImageComparisonMap (ULift.{u + 1} T) f.left K)) ≪≫
    comparisonD.app ((comparisonUpperStar A X.left).mapDerivedCategory.obj K) ≪≫
    R(I).mapIso eS
  have := ET.functor.isLE_mapDerivedCategory_obj
    (N.mapDerivedCategory.obj ((Etale.lowerStar A f.left).rightDerivedFunctor.obj K)) (2 * (d : ℤ))
  exact DerivedCategory.TStructure.t.isLE_of_iso e (2 * (d : ℤ))


/-- The sharp ordinary bound in the actual lifted spectral quotient coordinates.

Source: latest blueprint sk-lem-finite, finite-coefficient Complement
(blueprint: lem-sf-finite-point-finite-ordinary-bound).

Proof: shrink the finite discrete spectral quotient to a Type 0 ring, keeping its
multiplication and its ell-power annihilator. Restriction along the resulting
condensed ring isomorphism is an exact equivalence and preserves finite constant
local models. Such models give local finite presentations on the same strata.
Apply the finite discrete etale comparison bound. Restriction commutes with native
pushforward; deriving that isomorphism through the exact equivalences identifies
the result with restriction of the actual quotient direct image. Exact equivalence
reflects homology vanishing, so the same upper bound holds before restriction.
-/
theorem finite_point_finite_ordinary_bound
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) (hn : 1 ≤ n)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.left))
    (hM : IsConstantModelConstructible
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.left M)
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞)) :
    ((lowerStar (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.hom).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * (d : ℤ)) := by
  classical
  let nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E)).toNormedField
  let : NormedField (ULift.{u} E) := nf
  let : TopologicalSpace (ULift.{u} E) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let := DerivedNakayama.quotientDiscrete ℓ (ULift.{u} E) n
  let := Padic.finite_coefficientExtensionRing ℓ (ULift.{u} E) n hn
  let A := Padic.coefficientExtensionRing ℓ (ULift.{u} E) n
  let B := Shrink.{0} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let Λ := DerivedNakayama.quotientRing ℓ (ULift.{u} E) n
  let Λ' := Profinite.continuousMapRingObj.{u} B
  let e : Mon.mk Λ ≅ Mon.mk Λ' := finiteCoefficientIso A
  let a : Λ' ⟶ Λ := e.inv.hom
  have : IsMonHom a := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso a := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  let RX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (coefficientMap a X.left)
  let RY := Mod.comap (D := Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (coefficientMap a (Spec (.of k)))
  have : RX.IsEquivalence := inferInstanceAs
    (Mod.comapEquivalenceOfIsIso
      (C := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (coefficientMap a X.left)).functor.IsEquivalence
  have : RY.IsEquivalence := inferInstanceAs
    (Mod.comapEquivalenceOfIsIso
      (C := Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientMap a (Spec (.of k)))).functor.IsEquivalence
  let F := RX.obj M
  have hF : IsConstantModelConstructible Λ' X.left F :=
    constructible_comap a X.left M hM
  have hqcqs : CompactSpace X.left ∧ QuasiSeparatedSpace X.left := by
    exact ⟨QuasiCompact.compactSpace_of_compactSpace X.hom,
      quasiSeparatedSpace_of_quasiSeparated X.hom⟩
  have hstrat : IsFiniteConstantStratified Λ' X.left F := by
    simpa only [IsConstantModelConstructible, if_pos hqcqs] using hF
  have hFi := constructible_of_finiteConstantStratified Λ' X.left F hstrat
  have hB : (ℓ : B) ^ n = 0 := by
    let r : A →+* B := (Shrink.ringEquiv.{0} A).symm.toRingHom
    have hr : r (ℓ : A) = (ℓ : B) := map_natCast r ℓ
    have hz := congrArg r
      (show (ℓ : A) ^ n = 0 from quotient_annihilated ℓ (ULift.{u} E) n)
    rw [map_pow, hr, map_zero] at hz
    exact hz
  let Y : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  have : LocallyOfFiniteType Y.hom := by dsimp [Y]; infer_instance
  have : QuasiCompact Y.hom := by dsimp [Y]; infer_instance
  have : IsSeparated Y.hom := by dsimp [Y]; infer_instance
  let f : X ⟶ Y := Over.homMk X.hom (by simp [Y])
  let I := lowerStar Λ X.hom
  let I' := lowerStar Λ' X.hom
  have hb : (I'.rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE (2 * (d : ℤ)) :=
    finiteDiscrete_ordinary_bound ℓ f B n hB F hFi d hd
  let comparison : I.rightDerivedFunctor ⋙ RY.mapDerivedCategory ≅
      RX.mapDerivedCategory ⋙ I'.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso I RY).symm ≪≫
      Functor.rightDerivedFunctorNatIso (comapLowerStarIso a X.hom) ≪≫
      Functor.rightDerivedFunctorCompIso RX I' ≪≫
      Functor.isoWhiskerRight RX.rightDerivedFunctorIsoMapDerivedCategory I'.rightDerivedFunctor
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let ep := comparison.app K ≪≫ I'.rightDerivedFunctor.mapIso
    ((RX.mapDerivedCategorySingleFunctor 0).app M)
  have hb' : (RY.mapDerivedCategory.obj (I.rightDerivedFunctor.obj K)).IsLE
      (2 * (d : ℤ)) := by
    exact ⟨(DerivedCategory.TStructure.t.le (2 * (d : ℤ))).prop_of_iso ep.symm hb.le⟩
  apply (DerivedCategory.isLE_iff _ _).2
  intro q hq
  have hz := DerivedCategory.isZero_of_isLE (RY.mapDerivedCategory.obj
    (I.rightDerivedFunctor.obj K)) (2 * (d : ℤ)) q hq
  have he := (RY.mapDerivedCategoryHomologyFunctorIso q).app (I.rightDerivedFunctor.obj K)
  exact IsZero.of_full_of_faithful_of_isZero RY _ (hz.of_iso he)

end AlgebraicGeometry.ProEtale.CondensedRing
