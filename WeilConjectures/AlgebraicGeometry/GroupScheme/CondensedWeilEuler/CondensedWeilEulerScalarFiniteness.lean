/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
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
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRings
import Mathlib.Algebra.Field.ULift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
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
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerLocalSupport
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
/-! # Scalar finiteness and amplitude for Euler factors
Source: latest blueprint, Euler-product proof Steps 1 and 5.
(blueprint: lem-condensed-weil-euler-scalar-finiteness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open CondensedRing

private theorem scalarMap_surjective {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell) :
    Function.Surjective (scalarMap.{u} c) := by
  cases c with
  | finite E => exact Profinite.continuousMapConstRingHom_surjective E
  | qbar => exact Profinite.PadicAlgCl.constRingHom_surjective ell

private theorem finite_restrict {ell : ℕ} [Fact ell.Prime] (c : WeilCoefficient ell)
    (M : ModuleCat.{u + 1} (MonObj.Γ (WeilCoefficient.ab c)))
    [Module.Finite (MonObj.Γ (WeilCoefficient.ab c)) M] :
    Module.Finite (Scalar c) ((ModuleCat.restrictScalars (scalarMap c)).obj M) := by
  let : RingHomSurjective (scalarMap c) := ⟨scalarMap_surjective c⟩
  let f : ((ModuleCat.restrictScalars (scalarMap c)).obj M) →ₛₗ[scalarMap c] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact (f.finite_iff_of_bijective Function.bijective_id).2 inferInstance

/-- Scalar stalk cohomology is finite dimensional at every geometric point.
Source: Euler-product proof Step 1. Pullback preserves bounded constructibility;
field-coefficient ctf=bc and perfect point realization give finite homology. Exact
point sections identify that realization with the native stalk; restriction along
the surjective constant-section map preserves finite generation.
(blueprint: lem-condensed-weil-euler-scalar-finiteness). -/
theorem eulerPointFinite (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    ∀ j, Module.Finite (Scalar c) ((ModuleCat.restrictScalars (scalarMap c)).obj
      ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).obj
        (NativeCondensedDerived.stalk (WeilCoefficient.ab c) D K.obj.carrier z))) := by
  classical
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let Λ := WeilCoefficient.ab.{u} c
  let M := (NativeCondensedDerived.pull Λ z).obj K.obj.carrier
  have hM : boundedConstructible (condensedRingObj Λ (Spec (.of D.k))) M := by
    exact (boundedConstructible (condensedRingObj Λ (Spec (.of D.k)))).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ z).app K.obj.carrier)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ z K.obj.carrier K.property)
  have hadic : IsEllAdicCoefficient ell Λ inferInstance := by
    cases c with
    | finite E => exact .continuous E
    | qbar => exact .algebraicClosure
  have hMc : constantModelBoundedConstructible Λ (Spec (.of D.k)) M := by
    rw [← (adicConstructibilityPredicateComparison ell _ Λ hadic).2]
    exact hM
  have hcoeff : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)) := by
    cases c with
    | finite E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))
    | qbar => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  let M' : ConstantModelConstructibleFiniteTor Λ (Spec (.of D.k)) :=
    ⟨M, by
      rw [(integral_ctf_equals_bc ell _ (Mon.mk Λ) hcoeff).2.2.2]
      exact hMc⟩
  have hpoint : FinitePointScalarRealizationData Λ D.k := by
    cases c with
    | finite E => exact (finite_point_scalar_realization D ell hEll E).2.2.1
    | qbar =>
      exact (finite_point_scalar_realization D ell hEll (Classical.arbitrary _)).2.2.2
  obtain ⟨hperfect, _⟩ := hpoint
  have hp : DerivedCategory.IsPerfect
      ((condensedRingCoefficientSections Λ (Spec (.of D.k))).rightDerivedFunctor.obj M) :=
    hperfect M'
  have : IsNoetherianRing (MonObj.Γ Λ) := by
    cases c with
    | finite E => exact (finite_point_scalar_rings ell E).2.1
    | qbar => exact (finite_point_scalar_rings ell (Classical.arbitrary _)).2.2
  have hf := hp.finite_homology
  have := (finite_point_sections_exact Λ D.k).1
  have := (finite_point_sections_exact Λ D.k).2
  let e := Functor.rightDerivedFunctorIsoMapDerivedCategory
    (condensedRingCoefficientSections Λ (Spec (.of D.k)))
  intro j
  have : Module.Finite (MonObj.Γ Λ)
      ((NativeCondensedDerived.cohomology Λ j).obj
        (NativeCondensedDerived.stalk Λ D K.obj.carrier z)) := by
    let e' := (DerivedCategory.homologyFunctor _ j).mapIso (e.app M)
    have := hf j
    exact Module.Finite.equiv e'.toLinearEquiv
  exact finite_restrict c _

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)
  [IsSeparated X₀.hom] (c₀ : Compactification (D.geometricFiber X₀).hom)

end WeilConjectures.CondensedWeilEuler
