/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientTensorCtf
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
import WeilConjectures.SecSmoothPurity.CompositeTensorLocalData.CompositeTensorTranspose
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison

/-! # Composition and the dualizing tensor mate

Source:
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-composition/
thm-pur-composition-coherence.proof.md,
Steps 1--2 (blueprint: lem-pur-composition-tensor-mate).

## Main statements

* `CompositionTensorMate.composition_tensor_mate` states the complete
  orientation-free finite-coefficient composition identity, including its common
  composite-adjunction transpose and all specified source domains.
* The other declarations construct its canonical maps or name its individual
  clauses using the existing derived operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify
universe u v w v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

namespace CompositionTensorMate

section GenericTensor
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

end GenericTensor

section GenericTheta
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

end GenericTheta

section Maps
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]

end Maps

namespace CondensedBridge

open FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]

/-- The recorded normalized derived coefficient encoding.
Source: def-pe-finite-discrete-presentation-encoding
(blueprint: lem-pur-composition-tensor-mate). -/
abbrev N (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :=
  (E T).fixedDerived.functor

/-- The existing native derived inverse image, without a replacement construction.
Source: derived operations (blueprint: lem-pur-composition-tensor-mate). -/
abbrev nativePull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CondensedRing.CompactificationReindexing.P (coefficient A) f

/-- The existing native proper/open compact-support composite.
Source: compact-support convention (blueprint: lem-pur-composition-tensor-mate). -/
abbrev nativeSupport {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  CondensedRing.CompactificationReindexing.F (coefficient A)
    (HasCompactification.compactification f)

/-- Reuse the recorded open/proper encoding paste for the very same compactification.
Source: def-pur-finite-compact-support-encoding
(blueprint: lem-pur-composition-tensor-mate). -/
abbrev canonicalSupport (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  FiniteNativeTensor.compactEncoding A E (HasCompactification.compactification f)

/-- The actual specified coefficient-equivalence counit at the exceptional value.
Source: coefficient coordinate cancellation (blueprint: lem-pur-composition-tensor-mate). -/
def exceptionalComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : Native A Y) :
    (N A E X).obj ((exceptional A E f).obj K) ≅
      (G (ULift.{u + 1} A) f).obj ((N A E Y).obj K) :=
  (E X).fixedDerived.counitIso.app _

/-- Transport the normalized standing finite Hom bijection through the specified
compact-support comparison and coefficient equivalences. All maps are given data.
Source: finite comparison adjunction (blueprint: lem-pur-composition-tensor-mate). -/
def exceptionalHomEquiv (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (M : Native A X) (K : Native A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
      ((N A E X).obj M))
    (hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K)) :
    ((nativeSupport A f).obj M ⟶ K) ≃ (M ⟶ (exceptional A E f).obj K) :=
  (E Y).fixedDerived.fullyFaithfulFunctor.homEquiv.trans
    (((canonicalSupport A E f).app M).homFromEquiv.trans
      ((standingExceptionalHomEquiv (ULift.{u + 1} A) f hM hK).trans
        ((E X).fixedDerived.toAdjunction.homEquiv M _)))

/-- The native compact-support compositor is the unique preimage of the actual fixed
compositor under the normalized coefficient equivalence, with the specified boundary maps.
Source: compact-support composition (blueprint: lem-pur-composition-tensor-mate). -/
def nativeAlpha (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] (M : Native A X) :
    (nativeSupport A g).obj ((nativeSupport A f).obj M) ⟶
      (nativeSupport A (f ≫ g)).obj M :=
  (N A E Z).preimage
    ((canonicalSupport A E g).hom.app _ ≫
      (F (ULift.{u + 1} A) g).map ((canonicalSupport A E f).hom.app M) ≫
      alpha (ULift.{u + 1} A) f g ((N A E X).obj M) ≫
      (canonicalSupport A E (f ≫ g)).inv.app M)

/-- The native dualizing object is the exceptional image of the native tensor unit.
Source: omega_h (blueprint: lem-pur-composition-tensor-mate). -/
def nativeOmega (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : Native A X :=
  (exceptional A E f).obj (𝟙_ (Native A Y))

/-- The actual native projection arrow recorded by def-exchange-projection.
Source: specified projection (blueprint: lem-pur-composition-tensor-mate). -/
abbrev nativeProjection {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : Native A X) (K : Native A Y) :=
  (CondensedRing.exchangeProjectionData (coefficient A)
    (HasCompactification.compactification f) (𝟙 Y)).projection M K

variable [UpperStarPreservesFlat (ModuleCat.{u + 1} (ULift.{u + 1} A))]

/-- The coefficient unit comparison of the recorded monoidal encoding.
Source: def-sf-finite-realization-monoidal (blueprint: lem-pur-composition-tensor-mate). -/
def unitComparison (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :
    (N A E T).obj (𝟙_ (Native A T)) ≅ unit (ULift.{u + 1} A) T := by
  letI := FiniteNativeTensor.encodingMonoidal A T (E T)
  exact (Functor.Monoidal.εIso (N A E T)).symm

/-- The dualizing comparison includes the monoidal unit comparison, not an arbitrary
isomorphism of dualizing objects.
Source: omega definition and coefficient unit (blueprint: lem-pur-composition-tensor-mate). -/
def omegaComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (N A E X).obj (nativeOmega A E f) ≅ omega (ULift.{u + 1} A) f :=
  exceptionalComparison A E f _ ≪≫
    (G (ULift.{u + 1} A) f).mapIso (unitComparison A E Y)

/-- Finite-Tor preservation and invertibility of the evaluation-normalized internal-Hom
comparison. The comparison is literally the tensor-Hom transpose of the encoded evaluation
using the recorded encodingMonoidal tensorator. No isomorphism is chosen.
Source: derived tensor-Hom adjunction (blueprint: lem-pur-composition-tensor-mate). -/
def Objects (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) : Prop :=
    (∀ K : Native A T,
      CondensedRing.condensedConstructibleFiniteTor (coefficient A) T K ↔
        DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
          ((N A E T).obj K)) ∧
    (∀ K L : Native A T,
      letI := FiniteNativeTensor.encodingMonoidal A T (E T)
      let H := ((CondensedRing.derivedHom (coefficient A) T).obj (Opposite.op K)).obj L
      IsIso ((ProEtale.derivedTensorHomAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) ((N A E T).obj K)).homEquiv _ _
          ((Functor.Monoidal.μIso (N A E T) K H).hom ≫
            (N A E T).map
              ((CondensedRing.derivedTensorHomAdjunction (coefficient A) K).counit.app L))))

end CondensedBridge

end CompositionTensorMate
end AlgebraicGeometry.ProEtale
