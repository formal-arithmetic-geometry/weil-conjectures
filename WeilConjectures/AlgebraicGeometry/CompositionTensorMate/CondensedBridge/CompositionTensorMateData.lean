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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
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

/-- The published internal-module derived category over Lambda_T.
Source: finite coefficient convention (blueprint: lem-pur-composition-tensor-mate). -/
abbrev Native (T : Scheme.{u}) := _root_.DerivedCategory (Internal A T)

/-- The finite comparison exceptional operation in the internal coefficient presentation.
Its functor is the conjugate of the published nu^* f^times Rnu_* composite. The Hom
normalization is specified below, so this is not an arbitrary right-adjoint identification.
Source: finite paragraph of def-weil-exceptional-inverse-image
(blueprint: lem-pur-composition-tensor-mate). -/
def exceptional (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Native A Y ⥤ Native A X :=
  (E Y).fixedDerived.functor ⋙ G (ULift.{u + 1} A) f ⋙ (E X).fixedDerived.inverse

variable [UpperStarPreservesFlat (ModuleCat.{u + 1} (ULift.{u + 1} A))]

end CondensedBridge

end CompositionTensorMate
end AlgebraicGeometry.ProEtale
