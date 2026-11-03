/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
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
import WeilConjectures.SixFunctors.SfIdentificationData
import Mathlib.Algebra.Module.Injective
import WeilConjectures.Algebra.Homology.DerivedCategory.HomToInjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Category.ModuleCat.Injective
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectCohomologyAssembly
import WeilConjectures.RingTheory.DiscreteValuationRing.QuotientDuality
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData

/-! # Degreewise duality for finite Frobenius coefficients

Source: current smooth identification proof, finite-coefficient complement.
(blueprint: lem-sf-finite-coefficient-degreewise-pairing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalClosed
open scoped TensorProduct
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.SixFunctors

attribute [local instance] RingHomInvPair.of_ringEquiv

-- Evaluation commutes with a semilinear equivalence and its two dual equivalences.
section
variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]
-- Transport the tensor-Hom adjunction using the prescribed native shift comparisons.
end

-- The generic cancellation is exactly the signed comparison in the degree value.
/-- Finite cohomology of a scalar complex gives finite Hom-from-unit
cohomology in that degree.
Source: the regular module's projectivity
(blueprint: lem-pod-field-hom-degreewise-pairing).

Proof: the shift comparison identifies H0(E[i]) with Hi(E). Projectivity identifies Hom(R[0],E[i])
with Hom(R,H0(E[i])); evaluation at 1 gives a linear equivalence with H0(E[i]).
The single-complex unit comparison identifies R[0] with the derived unit.
Transport finite generation through the resulting equivalence. -/
theorem finiteHomFromUnitOfFiniteCohomology
    {R : Type (u + 1)} [CommRing R]
    {E : DerivedCategory (ModuleCat.{u + 1} R)}
    (i : ℤ) [Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj E)] :
    Module.Finite R (𝟙_ _ ⟶ E⟦i⟧) := by
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).obj (E⟦i⟧)
  let h := ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).shiftIso
    i 0 i (add_zero i)).app E
  have : Module.Finite R
      (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) 0).shift i).obj E) := by
    simpa only [DerivedCategory.shift_homologyFunctor] using
      (inferInstance : Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj E))
  have : Module.Finite R H := Module.Finite.of_surjective
    h.inv.hom ((ModuleCat.epi_iff_surjective h.inv).mp inferInstance)
  let e := DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} R)
  let φ : (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ E⟦i⟧) →ₗ[R] H :=
    { toFun := fun x ↦
        ((DerivedCategory.homSingleToHomology (ModuleCat.of R R) 0 (E⟦i⟧)
          (e.hom ≫ x)).hom) 1
      map_add' := by
        intro x y
        simp [DerivedCategory.homSingleToHomology]
      map_smul' := by
        intro r x
        simp [DerivedCategory.homSingleToHomology] }
  have hφ : Function.Bijective φ := by
    have hpre : Function.Bijective
        (fun x : (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)) ⟶ E⟦i⟧) ↦ e.hom ≫ x) := by
      constructor
      · intro x y h
        exact (cancel_epi e.hom).mp h
      · intro x
        exact ⟨e.inv ≫ x, by simp⟩
    let hRing := (DerivedCategory.homSingleEquivOfProjective
      (ModuleCat.of R R) 0 (E⟦i⟧)).trans
        (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv)
    have hcomp := hRing.bijective.comp hpre
    convert hcomp using 1
    funext x
    simp [φ, e, H, DerivedCategory.homSingleToHomology, hRing, ModuleCat.homEquiv]
  exact Module.Finite.of_surjective (LinearEquiv.ofBijective φ hφ).symm.toLinearMap
    (LinearEquiv.ofBijective φ hφ).symm.surjective

end WeilConjectures.SixFunctors
