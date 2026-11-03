/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.StrictWeilDerivedScalar.StrictWeilScalarLocalCompatibility
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral

import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.PoincareDuality.Abstract
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.GroupScheme.StrictWeilDerivedScalar.StrictWeilScalarCompactTransport

/-! # Derived scalar comparisons for strict Weil pairs

Source: latest blueprint, prop-every-iterate-trace.proof.md, scalar-descent sentence.
(blueprint: lem-zl-strict-weil-derived-scalar-frobenius).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.StrictWeilDerivedScalar

section LiftReturn
open NativeCondensedModule

private theorem pointPower_eq (D : FiniteFieldDatum.{u}) (n : ℕ) :
    localPositivePower (frobeniusPointIso D).hom n =
      let := Fintype.ofFinite D.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom) := by
  let := Fintype.ofFinite D.k₀
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [localPositivePower, ih]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1

private theorem frobeniusPower_projections (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        localPositivePower (frobeniusPointIso D).hom n := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ = _ ≫ (frobeniusPointIso D).hom at h
  induction n with
  | zero => exact h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2,
        Category.assoc]
      rfl

/-- Every lift with an arbitrary source automorphism has the required semilinear return.
Source: def-weil-local-frobenius-trace, point return convention
(blueprint: lem-zl-strict-weil-scalar-lift-return).

Proof: the chosen subfield has q^n elements, so the n-th power of geometric Frobenius
fixes every embedding of it in k. Apply this to the ring map corresponding to the
composite of b with its inclusion. Every ring endomorphism of k commutes with geometric
Frobenius, since it commutes with x ↦ x^q and hence with its inverse. The first
projection of g_Y^n is the first projection, and its second projection is the second
projection followed by g_s^n. The two asserted lift projections therefore identify the
projections of z g_Y^n and g_s^n z. Pullback uniqueness gives the equality. -/
theorem scalarLift_return (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (b : Spec (.of D.k) ≅ Spec (.of D.k))
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz₁ : z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      b.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left)
    (hz₂ : z ≫ pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = b.hom) :
    z ≫ localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ z := by
  let := Fintype.ofFinite D.k₀
  have hc : Nat.card (D.extensionSubfield n hn) = D.q ^ n :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.1
  have hq : 0 < D.q := by
    rw [← D.card_base]
    exact Nat.card_pos
  let : Finite (D.extensionSubfield n hn) :=
    (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos hq n)).2
  have hc' : Nat.card (D.extensionSubfield n hn) = Fintype.card D.k₀ ^ n := by
    simpa only [← D.card_base, Nat.card_eq_fintype_card] using hc
  have hfix : localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
      (b.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype)) =
      b.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) := by
    rw [← Spec.map_preimage
      (b.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype)),
      pointPower_eq, Nat.sub_add_cancel hn, ← Spec.map_comp]
    congr 1
    ext a
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
      D.k₀ D.k n hc' _ a
  have hcomm : localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ b.hom =
      b.hom ≫ localPositivePower (frobeniusPointIso D).hom (n - 1) := by
    rw [← Spec.map_preimage b.hom, pointPower_eq, ← Spec.map_comp, ← Spec.map_comp]
    rw [Nat.sub_add_cancel hn]
    congr 1
    ext a
    exact (FiniteField.map_geometricFrobeniusAlgEquivOfAlgebraic_pow_apply
      D.k₀ D.k (Spec.preimage b.hom).hom n a).symm
  apply pullback.hom_ext
  · simp only [Category.assoc, (frobeniusPower_projections D Y₀ (n - 1)).1, hz₁]
    simpa only [Category.assoc] using (congrArg (fun f ↦ f ≫ x.left) hfix).symm
  · rw [Category.assoc, (frobeniusPower_projections D Y₀ (n - 1)).2,
      ← Category.assoc, hz₂, Category.assoc, hz₂]
    exact hcomm.symm

end LiftReturn

/-- Exact field extension preserves the bounded constructible carrier of a strict pair.
Source: DAG step 1, exact scalar extension of finite presentations and cohomology
(blueprint: lem-zl-strict-weil-derived-scalar-frobenius). -/
theorem extendedPair_boundedConstructible (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : strictWeilComplexCategory D ell hEll Y₀ (.finite E)) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber Y₀).left)
      (extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj).carrier := by
  exact boundedConstructible_leftDerivedExtendScalars_obj _ _
    (padicSubfieldRingObjToPadicAlgCl (D.geometricFiber Y₀).left ell E) K.obj.carrier K.property

private theorem field_ctf (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] [QuasiSeparatedSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (hc : boundedConstructible (condensedRingObj Λ X) =
      constantModelBoundedConstructible Λ X)
    (K : NativeCondensedDerived.Ambient Λ X)
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) K := by
  have hcoeff :
      Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
      Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ F : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.padicIntegersRingObj ell F)) ∨
        Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.continuousMapRingObj F))) ∨
      Nonempty ((Mon.mk Λ) ≅ Mon.mk (Profinite.padicAlgClRingObj ell)) := by
    rcases hΛ with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr h⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  have hi := (integral_ctf_equals_bc ell X (Mon.mk Λ) hcoeff).2.2.2
  rw [hc] at hK
  exact (congrFun hi K).mpr hK

/-- The specified compact coefficient complexes are perfect over either section field.
Source: DAG step 4, compact-support perfectness from sk-lem-finite
(blueprint: lem-zl-strict-weil-derived-scalar-frobenius). -/
theorem compactCoefficientComplex_perfect (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (c : Compactification (D.geometricFiber Y₀).hom) :
    (∀ (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E)
        (D.geometricFiber Y₀).left),
      boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj E) (D.geometricFiber Y₀).left) K →
        DerivedCategory.IsPerfectRingComplex
          ((condensedRingCompactCoefficientComplex (Profinite.continuousMapRingObj E) c).obj K)) ∧
    (∀ (K : NativeCondensedDerived.Ambient (Profinite.padicAlgClRingObj ell)
        (D.geometricFiber Y₀).left),
      boundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber Y₀).left) K →
        DerivedCategory.IsPerfectRingComplex
          ((condensedRingCompactCoefficientComplex
            (Profinite.padicAlgClRingObj ell) c).obj K)) := by
  let : LocallyOfFiniteType (D.geometricFiber Y₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom _))
  let : QuasiCompact (D.geometricFiber Y₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom _))
  let : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom _))
  let : IsLocallyNoetherian (D.geometricFiber Y₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber Y₀).hom
  let : CompactSpace (D.geometricFiber Y₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber Y₀).hom
  have h := finite_geometric_point_cohomology D ell hEll E (D.geometricFiber Y₀)
  constructor
  · intro K hK
    have hc := (adicConstructibilityPredicateComparison ell (D.geometricFiber Y₀).left
      (Profinite.continuousMapRingObj E) (.continuous E)).2
    have hctf := field_ctf ell E (D.geometricFiber Y₀).left
      (Profinite.continuousMapRingObj E) (Or.inl ⟨Iso.refl _⟩) hc K hK
    exact ((h.2.2.1.2 c ⟨K, hctf⟩).2 _ (by simp)).1.1
  · intro K hK
    have hc := (adicConstructibilityPredicateComparison ell (D.geometricFiber Y₀).left
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).2
    have hctf := field_ctf ell E (D.geometricFiber Y₀).left
      (Profinite.padicAlgClRingObj ell) (Or.inr ⟨Iso.refl _⟩) hc K hK
    exact ((h.2.2.2.1.2 c ⟨K, hctf⟩).2 _ (by simp)).1.1

private theorem pull_boundedConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}}
    (D : FiniteFieldDatum.{u}) (z : Spec (.of D.k) ⟶ Y)
    (K : NativeCondensedDerived.Ambient Λ Y)
    (hK : boundedConstructible (condensedRingObj Λ Y) K) :
    boundedConstructible (condensedRingObj Λ (Spec (.of D.k)))
      ((NativeCondensedDerived.pull Λ z).obj K) := by
  refine ⟨(CondensedRing.upperStar Λ z).bounded_mapDerivedCategory_obj hK.1, fun i ↦ ?_⟩
  exact constructible_of_iso
    (((CondensedRing.upperStar Λ z).mapDerivedCategoryHomologyFunctorIso i).app K)
    (CondensedRing.isConstructibleModuleObject_upperStar Λ z _ (hK.2 i))

private theorem perfect_of_iso {R : Type (u + 1)} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u + 1} R)} (e : K ≅ L)
    (hK : DerivedCategory.IsPerfectRingComplex K) :
    DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := hK
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ i⟩⟩

/-- The actual native scalar stalk is perfect at both field coefficients.
Source: DAG step 4, point realization in sk-lem-finite and constructible pullback
(blueprint: lem-zl-strict-weil-derived-scalar-frobenius). -/
theorem stalk_perfect (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ Y) :
    (∀ (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y),
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y) K →
        DerivedCategory.IsPerfectRingComplex
          (NativeCondensedDerived.stalk (Profinite.continuousMapRingObj E) D K z)) ∧
    (∀ (K : NativeCondensedDerived.Ambient (Profinite.padicAlgClRingObj ell) Y),
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) Y) K →
        DerivedCategory.IsPerfectRingComplex
          (NativeCondensedDerived.stalk (Profinite.padicAlgClRingObj ell) D K z)) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let X : Over (Spec (.of D.k)) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  let : QuasiCompact X.hom := inferInstanceAs (QuasiCompact (𝟙 _))
  let : IsSeparated X.hom := inferInstanceAs (IsSeparated (𝟙 _))
  have h := finite_geometric_point_cohomology D ell hEll E X
  constructor
  · intro K hK
    have hpull := pull_boundedConstructible _ D z K hK
    have hc := (adicConstructibilityPredicateComparison ell (Spec (.of D.k))
      (Profinite.continuousMapRingObj E) (.continuous E)).2
    have hctf := field_ctf ell E (Spec (.of D.k))
      (Profinite.continuousMapRingObj E) (Or.inl ⟨Iso.refl _⟩) hc _ hpull
    exact perfect_of_iso ((sectionComparison (Profinite.continuousMapRingObj E) D).app _)
      (h.2.2.1.1.choose ⟨_, hctf⟩)
  · intro K hK
    have hpull := pull_boundedConstructible _ D z K hK
    have hc := (adicConstructibilityPredicateComparison ell (Spec (.of D.k))
      (Profinite.padicAlgClRingObj ell) .algebraicClosure).2
    have hctf := field_ctf ell E (Spec (.of D.k))
      (Profinite.padicAlgClRingObj ell) (Or.inr ⟨Iso.refl _⟩) hc _ hpull
    exact perfect_of_iso ((sectionComparison (Profinite.padicAlgClRingObj ell) D).app _)
      (h.2.2.2.1.1.choose ⟨_, hctf⟩)

set_option maxHeartbeats 4000000 in
-- The global transport endpoint elaborates several large derived functor composites.
/-- Apply naturality at theta after the scalar square for the compact first arrow.
Source: DAG step 7, the defining composite F_c = C(theta) t_c
(blueprint: lem-zl-strict-weil-derived-scalar-frobenius). -/
theorem global_compact_scalar (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : strictWeilComplexCategory D ell hEll Y₀ (.finite E)) :
    let KΩ : strictWeilComplexCategory D ell hEll Y₀ .qbar :=
      ⟨extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj,
        extendedPair_boundedConstructible D ell hEll E Y₀ K⟩
    (scalarChange ell E).map
        (GlobalGeometricFrobenius.globalGeometricFrobenius
          D ell hEll Y₀ (.finite E) c₀ K).2 ≫ compactComparison D ell E c₀ K.obj.carrier =
      compactComparison D ell E c₀ K.obj.carrier ≫
        (GlobalGeometricFrobenius.globalGeometricFrobenius
          D ell hEll Y₀ .qbar c₀ KΩ).2 := by
  let KΩ : strictWeilComplexCategory D ell hEll Y₀ .qbar :=
    ⟨extendedPair ell E (D.geometricFrobenius Y₀).hom K.obj,
      extendedPair_boundedConstructible D ell hEll E Y₀ K⟩
  dsimp only
  rw [global_compact_factorization D ell hEll Y₀ (.finite E) c₀ K,
    global_compact_factorization D ell hEll Y₀ .qbar c₀ KΩ]
  rw [Functor.map_comp, Category.assoc,
    compactComparison_naturality D ell E c₀ K.obj.str.hom, ← Category.assoc,
    compactTransport_scalar D ell hEll E Y₀ c₀ K.obj.carrier K.property
      (extendedPair_boundedConstructible D ell hEll E Y₀ K)]
  simp only [KΩ, extendedPair, Endofunctor.IsoAlgebra.mk_carrier,
    Endofunctor.IsoAlgebra.mk_str, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]

end WeilConjectures.StrictWeilDerivedScalar
