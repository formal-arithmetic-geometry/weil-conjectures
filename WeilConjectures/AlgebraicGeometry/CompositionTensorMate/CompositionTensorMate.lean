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
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
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
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCoefficientCoherence
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompatibleCompactificationTriangle
import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionMate
import WeilConjectures.SecSmoothPurity.CompositeTensorLocalData.CompositeTensorTranspose
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientTensorCtf
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CompositionTensorRouteTransposes
public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CondensedBridge.CompositionTensorMateData
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteCounitProjectionTransport
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness

/-! # Composition and the dualizing tensor mate

Source: main-20261015, sk-prop-sp-composition, Steps 1--2
(blueprint: lem-pur-composition-tensor-mate).

## Main statements

* `CompositionTensorMate.composition_tensor_mate` states the complete
  orientation-free finite-coefficient composition identity, including its common
  composite-adjunction transpose and all specified source domains.
* The other declarations construct its canonical maps or name its individual
  clauses using the existing derived operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

namespace CompositionTensorMate

/-- The existing constant-module derived category on the small pro-etale site.
Source: finite purity conventions (blueprint: lem-pur-composition-tensor-mate). -/
abbrev D (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))

/-- Extend the inverse by zero away from its invertibility domain. On the theorem's
projection and composition components this is precisely the unique inverse.
Source: displayed inverse maps (blueprint: lem-pur-composition-tensor-mate). -/
def inverseOnDomain {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
    {M N : C} (a : M ⟶ N) : N ⟶ M :=
  open Classical in
  if h : IsIso a then @inv _ _ _ _ a h else 0

section GenericTensor
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The prescribed inverse projection, with the coefficient instances cached generically.
Source: projection formula (blueprint: lem-pur-composition-tensor-mate). -/
def genericPi (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C)) :=
  inverseOnDomain (((projectionMap C f).app M).app K)

/-- The exact counit/projection composite to be transposed. The symmetry is the
published signed K-flat symmetry, and the target unit constraint is explicit.
Source: defining transpose of theta (blueprint: lem-pur-composition-tensor-mate). -/
def genericTensorTranspose
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (e : (rightDerivedLowerShriek C f).obj M ⟶ 𝟙_ _) :=
  (rightDerivedLowerShriek C f).map (derivedTensorKoszulSymmetry _
    ((upperStar C f).leftDerivedFunctor.obj K) M).hom ≫
    genericPi C f M K ≫ e ▷ K ≫ (λ_ K).hom

/-- Cache the existing tensor object without expanding the concrete coefficient instances.
Source: derived tensor in the assertion (blueprint: lem-pur-composition-tensor-mate). -/
def genericTensor (T : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) := M ⊗ N

/-- Assemble the specified symmetry, tensor mate and inverse composition component.
Source: sigma (blueprint: lem-pur-composition-tensor-mate). -/
def genericSigma
    (M V U : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (th : (upperStar C f).leftDerivedFunctor.obj N ⊗ M ⟶ V) (a : U ⟶ V) :=
  (derivedTensorKoszulSymmetry _
    M ((upperStar C f).leftDerivedFunctor.obj N)).hom ≫
    th ≫ inverseOnDomain a

/-- Assemble the prescribed pullback compositor and signed tensor reassociation.
Source: r_K (blueprint: lem-pur-composition-tensor-mate). -/
def genericR {Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) :=
  (leftDerivedUpperStarComp C f g).hom.app K ▷
      genericTensor C X M ((upperStar C f).leftDerivedFunctor.obj N) ≫
    (upperStar C f).leftDerivedFunctor.obj ((upperStar C g).leftDerivedFunctor.obj K) ◁
      (derivedTensorKoszulSymmetry _ M ((upperStar C f).leftDerivedFunctor.obj N)).hom ≫
    (α_ ((upperStar C f).leftDerivedFunctor.obj ((upperStar C g).leftDerivedFunctor.obj K))
      ((upperStar C f).leftDerivedFunctor.obj N) M).inv ≫
    (leftDerivedUpperStarTensorIso C f ((upperStar C g).leftDerivedFunctor.obj K) N).inv ▷ M

/-- Assemble precisely the two counits and inverse f-projection defining t.
Source: t (blueprint: lem-pur-composition-tensor-mate). -/
def genericTrace {Z : Scheme.{u}} (g : Y ⟶ Z) [HasCompactification g]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (e : (rightDerivedLowerShriek C f).obj M ⟶ 𝟙_ _)
    (e' : (rightDerivedLowerShriek C g).obj N ⟶ 𝟙_ _) :=
  (rightDerivedLowerShriek C g).map
    (genericPi C f M N ≫ e ▷ N ≫ (λ_ N).hom) ≫ e'

/-- Assemble the successive inverse projections with the fixed pullback compositor.
Source: common transpose (blueprint: lem-pur-composition-tensor-mate). -/
def genericCompositePi {Z : Scheme.{u}} (g : Y ⟶ Z) [HasCompactification g]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) :=
  (rightDerivedLowerShriek C g).map ((rightDerivedLowerShriek C f).map
    ((derivedTensorKoszulSymmetry _
      ((upperStar C (f ≫ g)).leftDerivedFunctor.obj K) M).hom ≫
      M ◁ (leftDerivedUpperStarComp C f g).hom.app K) ≫
    genericPi C f M ((upperStar C g).leftDerivedFunctor.obj K)) ≫
      genericPi C g ((rightDerivedLowerShriek C f).obj M) K

/-- Assemble the left tensor-mate route with the specified final comparison.
Source: left side of (*) (blueprint: lem-pur-composition-tensor-mate). -/
def genericLeft (T : Scheme.{u})
    (A W M V V' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (a : W ⟶ M) (th : A ⊗ M ⟶ V) (b : V ⟶ V') := A ◁ a ≫ th ≫ b

/-- Assemble the right tensor-mate route, with all instances retained symbolically.
Source: right side of (*) (blueprint: lem-pur-composition-tensor-mate). -/
def genericRight {Z : Scheme.{u}} (g : Y ⟶ Z)
    (M V : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (th : (upperStar C g).leftDerivedFunctor.obj K ⊗ N ⟶ L)
    (th' : (upperStar C f).leftDerivedFunctor.obj L ⊗ M ⟶ V) :=
  genericR C f g M N K ≫ (upperStar C f).leftDerivedFunctor.map th ▷ M ≫ th'

/-- Finish the specified common inverse transpose by the trace and coefficient unit.
Source: final paragraph (blueprint: lem-pur-composition-tensor-mate). -/
def genericCommon {Z : Scheme.{u}} (g : Y ⟶ Z) [HasCompactification g]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (tr : (rightDerivedLowerShriek C g).obj ((rightDerivedLowerShriek C f).obj M) ⟶ 𝟙_ _) :=
  genericCompositePi C f g M K ≫ tr ▷ K ≫ (λ_ K).hom

/-- Tensor-map clauses with the coefficient instances cached at the generic level.
Source: finite-Tor tensor domains (blueprint: lem-pur-composition-tensor-mate). -/
def genericTensorClause
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (R : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (th : ∀ K, (upperStar C f).leftDerivedFunctor.obj K ⊗ M ⟶ R.obj K)
    (px : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)))
    (py : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))) : Prop :=
  px M ∧ ∀ K, py K → px ((upperStar C f).leftDerivedFunctor.obj K ⊗ M) ∧
    IsIso (((projectionMap C f).app M).app K) ∧ IsIso (th K)

/-- The unit of the existing derived tensor, cached before coefficient specialization.
Source: coefficient unit (blueprint: lem-pur-composition-tensor-mate). -/
def genericUnit (T : Scheme.{u}) :=
  𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))

/-- A specified canonical projection component is invertible.
Source: inverse projection domains (blueprint: lem-pur-composition-tensor-mate). -/
def genericProjectionDomain
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C)) : Prop :=
  IsIso (((projectionMap C f).app M).app K)

/-- The single-input tensor assertion used at omega_g and Rg!K for f.
Source: displayed f-tensor domains (blueprint: lem-pur-composition-tensor-mate). -/
def genericTensorInput
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (R : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (th : ∀ K, (upperStar C f).leftDerivedFunctor.obj K ⊗ M ⟶ R.obj K)
    (px : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C)) : Prop :=
  px ((upperStar C f).leftDerivedFunctor.obj K ⊗ M) ∧
    genericProjectionDomain C f M K ∧ IsIso (th K)

/-- The tensor source functor for the naturality equation.
Source: left side of (*) (blueprint: lem-pur-composition-tensor-mate). -/
def genericSource (T : Scheme.{u}) (h : X ⟶ T)
    (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) :=
  (upperStar C h).leftDerivedFunctor ⋙ tensorRight W

/-- The additional finite-Tor source domains of the K-form.
Source: domains of (*) (blueprint: lem-pur-composition-tensor-mate). -/
def genericDomains {Z : Scheme.{u}} (g : Y ⟶ Z) [HasCompactification g]
    (M W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (R : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (px : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)))
    (py : ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C)) : Prop :=
  py (R.obj K) ∧ px ((genericSource C Z (f ≫ g) W).obj K) ∧
  px (genericTensor C X ((upperStar C f).leftDerivedFunctor.obj
    (genericTensor C Y ((upperStar C g).leftDerivedFunctor.obj K) N)) M) ∧
  IsIso (genericR C f g M N K) ∧
  genericProjectionDomain C f W ((upperStar C g).leftDerivedFunctor.obj K) ∧
  genericProjectionDomain C g ((rightDerivedLowerShriek C f).obj W) K

/-- The isomorphism assertion for precisely the sigma assembled above.
Source: sigma invertibility (blueprint: lem-pur-composition-tensor-mate). -/
def genericSigmaIso
    (M V U : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (th : (upperStar C f).leftDerivedFunctor.obj N ⊗ M ⟶ V) (a : U ⟶ V) : Prop :=
  IsIso (genericSigma C f M V U N th a)

/-- The actual inverse Hom image of the specified unit-input sigma composite.
Source: transpose of c sigma (blueprint: lem-pur-composition-tensor-mate). -/
def genericUnitTranspose {Z : Scheme.{u}} (g : Y ⟶ Z) [HasCompactification g]
    (M V U : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) C))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) C))
    (th : (upperStar C f).leftDerivedFunctor.obj N ⊗ M ⟶ V) (a : U ⟶ V)
    (ep : (rightDerivedLowerShriek C g).obj ((rightDerivedLowerShriek C f).obj V) ⟶
      genericUnit C Z)
    (tr : (rightDerivedLowerShriek C g).obj ((rightDerivedLowerShriek C f).obj
      (genericTensor C X M ((upperStar C f).leftDerivedFunctor.obj N))) ⟶
      genericUnit C Z) : Prop :=
  (rightDerivedLowerShriek C g).map ((rightDerivedLowerShriek C f).map
    (genericSigma C f M V U N th a ≫ a)) ≫ ep = tr

end GenericTensor

section GenericTheta
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

/-- Form the exact tensor mate using the supplied standing Hom bijections. Its data is a
literal Hom transpose. Specialised to finite constant coefficients, where `Rf^!` exists.
Source: inverse-projection/counit definition (blueprint: lem-pur-composition-tensor-mate). -/
def genericTheta
    (H : ∀ (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))),
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X M →
      ∀ (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))),
      _root_.DerivedCategory.TStructure.t.plus K →
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj M ⟶ K) ≃
        (M ⟶ (rightDerivedUpperShriek Λ f).obj K))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :=
  open Classical in
  if hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X
      ((upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.obj K ⊗
        (rightDerivedUpperShriek Λ f).obj (𝟙_ _)) then
    if hK : _root_.DerivedCategory.TStructure.t.plus K then
      if hU : _root_.DerivedCategory.TStructure.t.plus
          (𝟙_ (_root_.DerivedCategory
            (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))) then
        H _ hW K hK
          (genericTensorTranspose (ModuleCat.{u + 1} Λ) f
            ((rightDerivedUpperShriek Λ f).obj (𝟙_ _)) K
            ((H _ (plusEtaleOrigin_rightDerivedUpperShriek_obj f hU) _ hU).symm (𝟙 _)))
      else 0
    else 0
  else 0

end GenericTheta

/-- Equality of both routes, equality of their inverse Hom images, and naturality,
with categorical types kept abstract to avoid expanding the derived tensor instance.
Source: (*) and its common transpose (blueprint: lem-pur-composition-tensor-mate). -/
def routeEquations {A : Type v₁} {B : Type v₂} [Category.{w₁} A] [Category.{w₂} B]
    (P : A ⥤ B) (L R : B ⥤ A)
    (l r : ∀ K, L.obj K ⟶ R.obj K)
    (ep : ∀ K, P.obj (R.obj K) ⟶ K) (tr : ∀ K, P.obj (L.obj K) ⟶ K)
    (pz : ObjectProperty B) (K : B) : Prop :=
  l K = r K ∧ P.map (l K) ≫ ep K = tr K ∧ P.map (r K) ≫ ep K = tr K ∧
  ∀ J, pz J → ∀ a : K ⟶ J, L.map a ≫ l J = l K ≫ R.map a

/-- Naturality of the specified comparison on its actual object domain.
Source: c is a natural isomorphism (blueprint: lem-pur-composition-tensor-mate). -/
def comparisonNaturality {A : Type v₁} {B : Type v₂}
    [Category.{w₁} A] [Category.{w₂} B] (L R : B ⥤ A)
    (a : ∀ K, L.obj K ⟶ R.obj K) (p : ObjectProperty B) : Prop :=
  ∀ K, p K → ∀ J, p J → ∀ b : K ⟶ J, L.map b ≫ a J = a K ≫ R.map b

/-- The comparison is invertible and its inverse Hom image is the specified map.
Source: counit-mate clause (blueprint: lem-pur-composition-tensor-mate). -/
def mateEquation {A : Type v₁} {B : Type v₂} [Category.{w₁} A] [Category.{w₂} B]
    (P : A ⥤ B) {U V : A} {J : B}
    (a : U ⟶ V) (ep : P.obj V ⟶ J) (tr : P.obj U ⟶ J) : Prop :=
  IsIso a ∧ P.map a ≫ ep = tr

section Maps
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The actual K-flat derived inverse image.
Source: derived operations (blueprint: lem-pur-composition-tensor-mate). -/
def S {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor

/-- The standing compact-support operation at the chosen compactification.
Source: compact-support composition (blueprint: lem-pur-composition-tensor-mate). -/
abbrev F {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : D Λ X ⥤ D Λ Y :=
  rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f

/-- The standing exceptional inverse image, with no ambient right-adjoint assumption.
Source: exceptional inverse image (blueprint: lem-pur-composition-tensor-mate). -/
abbrev G {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : D Λ Y ⥤ D Λ X :=
  rightDerivedUpperShriek Λ f

/-- The coefficient sheaf in degree zero, using the existing derived tensor unit.
Source: Lambda_T in the statement (blueprint: lem-pur-composition-tensor-mate). -/
def unit (T : Scheme.{u}) : D Λ T := genericUnit (ModuleCat.{u + 1} Λ) T

/-- The relative dualizing object is the standing exceptional image of the unit.
Source: omega_h in the statement (blueprint: lem-pur-composition-tensor-mate). -/
def omega {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : D Λ X :=
  (G Λ f).obj (unit Λ Y)

/-- The standing exceptional counit, computed by its specified Hom bijection.
The zero extension is never used on the bounded-below domain in the assertion.
Source: epsilon_h in the statement (blueprint: lem-pur-composition-tensor-mate). -/
def epsilon {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : D Λ Y) : (F Λ f).obj ((G Λ f).obj K) ⟶ K :=
  open Classical in
  if hK : _root_.DerivedCategory.TStructure.t.plus K then
    (standingExceptionalHomEquiv Λ f
      (plusEtaleOrigin_rightDerivedUpperShriek_obj f hK) hK).symm (𝟙 _)
  else 0

/-- The specified compact-support compositor alpha on its etale-origin domain.
Source: thm-sf-comp-composition (blueprint: lem-pur-composition-tensor-mate). -/
def alpha {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (M : D Λ X) : (F Λ g).obj ((F Λ f).obj M) ⟶ (F Λ (f ≫ g)).obj M :=
  open Classical in
  if hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X M then
    (originCompositionAmbient Λ f g).hom.app ⟨M, hM⟩
  else 0

/-- The counit mate of alpha, computed by successively transposing through g and f.
On bounded constructible K this is literally standingExceptionalComposition.
Source: pur9-def-upper-shriek-composition (blueprint: lem-pur-composition-tensor-mate). -/
def c {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    [CompactSpace Y] [CompactSpace Z] (K : D Λ Z) :
    (G Λ (f ≫ g)).obj K ⟶ (G Λ f).obj ((G Λ g).obj K) :=
  open Classical in
  if hK : _root_.DerivedCategory.TStructure.t.plus K then
    (standingExceptionalHomEquiv Λ g
      ((plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hK).rightDerivedLowerShriek_obj f)
      hK).trans
      (standingExceptionalHomEquiv Λ f
        (plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hK)
        (plus_rightDerivedUpperShriek_obj g hK))
      (alpha Λ f g ((G Λ (f ≫ g)).obj K) ≫ epsilon Λ (f ≫ g) K)
  else 0

variable [UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]

/-- The inverse of the actual projection transformation component, extended by zero
only off its invertibility domain.
Source: def-exchange-projection (blueprint: lem-pur-composition-tensor-mate). -/
def pi {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : D Λ X) (K : D Λ Y) :=
  genericPi (ModuleCat.{u + 1} Λ) f M K

/-- The canonical tensor map in the statement's pullback-first ordering. Its
transpose is symmetry, inverse projection, the standing counit at the unit, and
left unitor. It is extended by zero only outside the standing Hom domains.
Source: def-pur-co-smoothness (blueprint: lem-pur-composition-tensor-mate). -/
def theta {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : D Λ Y) :=
  genericTheta Λ f
    (fun M hM L hL ↦ standingExceptionalHomEquiv Λ f (K := M) (L := L) hM hL) K

/-- The un-oriented tensor of the two relative dualizing objects.
Source: W in the statement (blueprint: lem-pur-composition-tensor-mate). -/
def W {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] :=
  genericTensor (ModuleCat.{u + 1} Λ) X (omega Λ f) ((S Λ f).obj (omega Λ g))

/-- The specified dualizing comparison: symmetry, theta_f at omega_g, then c inverse.
Source: displayed sigma (blueprint: lem-pur-composition-tensor-mate). -/
def sigma {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z] :=
  genericSigma (ModuleCat.{u + 1} Λ) f (omega Λ f) ((G Λ f).obj (omega Λ g))
    (omega Λ (f ≫ g)) (omega Λ g) (theta Λ f (omega Λ g)) (c Λ f g (unit Λ Z))

/-- The canonical reassociation r_K, including the actual derived pullback compositor.
All symmetries are the signed derived symmetries.
Source: displayed r_K (blueprint: lem-pur-composition-tensor-mate). -/
def r {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] (K : D Λ Z) :=
  genericR (ModuleCat.{u + 1} Λ) f g (omega Λ f) (omega Λ g) K

/-- Counit of the composite adjunction, in the specified pasted order.
Source: def-weil-pbc-composite-adjunction (blueprint: lem-pur-composition-tensor-mate). -/
def compositeEpsilon {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z]
    (K : D Λ Z) :=
  (F Λ g).map (epsilon Λ f ((G Λ g).obj K)) ≫ epsilon Λ g K

/-- The displayed trace t: inverse projection for f, T_f tensor identity, then T_g.
Source: displayed t (blueprint: lem-pur-composition-tensor-mate). -/
def t {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z] :=
  genericTrace (ModuleCat.{u + 1} Λ) f g (omega Λ f) (omega Λ g)
    (epsilon Λ f (unit Λ Y)) (epsilon Λ g (unit Λ Z))

/-- Left side of (*), written in diagrammatic order.
Source: equation (*) (blueprint: lem-pur-composition-tensor-mate). -/
def lhs {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z] (K : D Λ Z) :=
  genericLeft (ModuleCat.{u + 1} Λ) X ((S Λ (f ≫ g)).obj K) (W Λ f g)
    (omega Λ (f ≫ g)) ((G Λ (f ≫ g)).obj K) ((G Λ f).obj ((G Λ g).obj K))
    (sigma Λ f g) (theta Λ (f ≫ g) K) (c Λ f g K)

/-- Right side of (*), with precisely the stated tensor order.
Source: equation (*) (blueprint: lem-pur-composition-tensor-mate). -/
def rhs {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z]
    (K : D Λ Z) :=
  genericRight (ModuleCat.{u + 1} Λ) f g (omega Λ f)
    ((G Λ f).obj ((G Λ g).obj K)) (omega Λ g) ((G Λ g).obj K) K
    (theta Λ g K) (theta Λ f ((G Λ g).obj K))

/-- The common composite-adjunction transpose in the statement.
Source: final displayed composite (blueprint: lem-pur-composition-tensor-mate). -/
def commonTranspose {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z]
    (K : D Λ Z) :=
  genericCommon (ModuleCat.{u + 1} Λ) f g (W Λ f g) K (t Λ f g)

/-- Bounded constructible sources have origins and compact support preserves the origin class.
Source: domain paragraph of the statement (blueprint: lem-pur-composition-tensor-mate). -/
def OriginClause {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : Prop :=
  ∀ M : D Λ X, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M →
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X M ∧
      DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Y ((F Λ f).obj M)

/-- The tensor-mate assertions on the finite-Tor domains, with their source domains
and the invertibility of the very projection components used in their definitions.
Source: tensor-isomorphism clause (blueprint: lem-pur-composition-tensor-mate). -/
def TensorClause {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] : Prop :=
  genericTensorClause (ModuleCat.{u + 1} Λ) f (omega Λ f) (G Λ f) (theta Λ f)
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X)
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y)

/-- Restrict the existing exceptional adjunction to the actual full bounded
constructible categories, with their supplied preservation proofs.
Source: constructible adjunction (blueprint: lem-pur-composition-tensor-mate). -/
def restrictedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y]
    (hF : ∀ M : D Λ X, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y ((F Λ f).obj M))
    (hG : ∀ K : D Λ Y, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ((G Λ f).obj K)) :=
  rightDerivedUpperShriekAdjunction f
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X)
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y)
    (fun _ hM ↦ hM.plusEtaleOrigin) (fun _ hK ↦ hK.plusEtaleOrigin.plus) hF hG

/-- The composite is the Mathlib composite of the standing restricted adjunctions;
its underlying counit is exactly the stated pasted standing counit. The preservation
proofs are conclusions here, never hypotheses on the geometric theorem.
Source: composite-adjunction clause (blueprint: lem-pur-composition-tensor-mate). -/
def AdjunctionClause {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z] : Prop :=
  ∃ (hFf : ∀ M : D Λ X, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y ((F Λ f).obj M))
    (hGf : ∀ K : D Λ Y, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ((G Λ f).obj K))
    (hFg : ∀ M : D Λ Y, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y M →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z ((F Λ g).obj M))
    (hGg : ∀ K : D Λ Z, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y ((G Λ g).obj K)),
    ∀ K : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} Λ) Z,
      (((restrictedAdjunction Λ f hFf hGf).comp
        (restrictedAdjunction Λ g hFg hGg)).counit.app K).hom =
          compositeEpsilon Λ f g K.obj

/-- The tensor input domain and invertibility at a single specified object.
Source: f at omega_g and Rg!K (blueprint: lem-pur-composition-tensor-mate). -/
def TensorInputClause {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] (K : D Λ Y) : Prop :=
  genericTensorInput (ModuleCat.{u + 1} Λ) f (omega Λ f) (G Λ f) (theta Λ f)
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X) K

/-- All parts of the K-form, including its two actual inverse Hom images and naturality.
The explicit domain and projection assertions ensure that none of the extensions
by zero in the ambient map definitions is used in this assertion.
Source: equation (*) and final paragraph (blueprint: lem-pur-composition-tensor-mate). -/
def InputClause {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (K : D Λ Z) : Prop :=
  TensorInputClause Λ f ((G Λ g).obj K) ∧
  genericDomains (ModuleCat.{u + 1} Λ) f g (omega Λ f) (W Λ f g) (omega Λ g)
    (G Λ g) (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X)
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y) K ∧
  routeEquations (F Λ f ⋙ F Λ g)
    (genericSource (ModuleCat.{u + 1} Λ) Z (f ≫ g) (W Λ f g)) (G Λ g ⋙ G Λ f)
    (lhs Λ f g) (rhs Λ f g) (compositeEpsilon Λ f g) (commonTranspose Λ f g)
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z) K

/-- The comparison isomorphism and its defining counit-mate equation.
Source: c and its transpose (blueprint: lem-pur-composition-tensor-mate). -/
def MateClause {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z] : Prop :=
  comparisonNaturality (G Λ (f ≫ g)) (G Λ g ⋙ G Λ f) (c Λ f g)
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z) ∧
  ∀ K : D Λ Z, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z K →
    mateEquation (F Λ f ⋙ F Λ g) (c Λ f g K) (compositeEpsilon Λ f g K)
      (alpha Λ f g ((G Λ (f ≫ g)).obj K) ≫ epsilon Λ (f ≫ g) K)

/-- The dualizing tensor comparison is an isomorphism.
Source: sigma (blueprint: lem-pur-composition-tensor-mate). -/
def SigmaIsoClause {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z] : Prop :=
  genericSigmaIso (ModuleCat.{u + 1} Λ) f (omega Λ f) ((G Λ f).obj (omega Λ g))
    (omega Λ (f ≫ g)) (omega Λ g) (theta Λ f (omega Λ g)) (c Λ f g (unit Λ Z))

/-- The unit-input composite-adjunction transpose is exactly t.
Source: transpose of c sigma (blueprint: lem-pur-composition-tensor-mate). -/
def UnitTransposeClause {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z] : Prop :=
  genericUnitTranspose (ModuleCat.{u + 1} Λ) f g
    (omega Λ f) ((G Λ f).obj (omega Λ g)) (omega Λ (f ≫ g)) (omega Λ g)
    (theta Λ f (omega Λ g)) (c Λ f g (unit Λ Z))
    (compositeEpsilon Λ f g (unit Λ Z)) (t Λ f g)

/-- The orientation-free composition assertion, expressed entirely in the existing
constant-module coordinates on the small pro-etale sites.
Source: complete node statement (blueprint: lem-pur-composition-tensor-mate). -/
def Package {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z] : Prop :=
  AdjunctionClause Λ f g ∧
  OriginClause Λ f ∧ OriginClause Λ g ∧ OriginClause Λ (f ≫ g) ∧
  TensorClause Λ g ∧ TensorClause Λ (f ≫ g) ∧
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (omega Λ f) ∧
  TensorInputClause Λ f (omega Λ g) ∧
  DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (W Λ f g) ∧
  MateClause Λ f g ∧ SigmaIsoClause Λ f g ∧ UnitTransposeClause Λ f g ∧
  ∀ K : D Λ Z, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z K →
    InputClause Λ f g K

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

/-- Generator equations for the specified native-to-fixed transport. Every tensorator
is encodingMonoidal, every pullback component is encodingDerivedPull inverse, and every
support component is compactEncoding. The Hom, counit and theta equations fix adjunction
data and their tensor mates, not only the exceptional functor's isomorphism class.
Source: finite coefficient identification and defining transposes
(blueprint: lem-pur-composition-tensor-mate). -/
structure Arrow (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y] : Prop where
  projection : ∀ (M : Native A X) (K : Native A Y),
    letI := FiniteNativeTensor.encodingMonoidal A X (E X)
    letI := FiniteNativeTensor.encodingMonoidal A Y (E Y)
    (Functor.Monoidal.μIso (N A E Y) ((nativeSupport A f).obj M) K).hom ≫
      (N A E Y).map (nativeProjection A f M K) ≫
      (canonicalSupport A E f).hom.app (M ⊗ (nativePull A f).obj K) ≫
      (F (ULift.{u + 1} A) f).map
        ((Functor.Monoidal.μIso (N A E X) M ((nativePull A f).obj K)).inv ≫
          (N A E X).obj M ◁ (FiniteNativeTensor.encodingDerivedPull A E f).inv.app K) =
    (canonicalSupport A E f).hom.app M ▷ (N A E Y).obj K ≫
      ((projectionMap (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).app
        ((N A E X).obj M)).app ((N A E Y).obj K)
  hom : ∀ (M : Native A X) (K : Native A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
      ((N A E X).obj M))
    (hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K))
    (b : (nativeSupport A f).obj M ⟶ K),
    (N A E X).map (exceptionalHomEquiv A E f M K hM hK b) ≫
      (exceptionalComparison A E f K).hom =
    standingExceptionalHomEquiv (ULift.{u + 1} A) f hM hK
      ((canonicalSupport A E f).inv.app M ≫ (N A E Y).map b)
  counit : ∀ K : Native A Y,
    _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K) →
    (N A E Y).map (nativeEpsilon A E f K) =
      (canonicalSupport A E f).hom.app _ ≫
        (F (ULift.{u + 1} A) f).map (exceptionalComparison A E f K).hom ≫
        epsilon (ULift.{u + 1} A) f ((N A E Y).obj K)
  theta : ∀ K : Native A Y,
    CondensedRing.condensedConstructibleFiniteTor (coefficient A) Y K →
    letI := FiniteNativeTensor.encodingMonoidal A X (E X)
    (N A E X).map (nativeTheta A E f K) ≫ (exceptionalComparison A E f K).hom =
      (Functor.Monoidal.μIso (N A E X) ((nativePull A f).obj K)
        (nativeOmega A E f)).inv ≫
        ((FiniteNativeTensor.encodingDerivedPull A E f).inv.app K ⊗ₘ
          (omegaComparison A E f).hom) ≫ theta (ULift.{u + 1} A) f ((N A E Y).obj K)

/-- The dualizing comparison includes the monoidal unit comparison, not an arbitrary
isomorphism of dualizing objects.
Source: omega definition and coefficient unit (blueprint: lem-pur-composition-tensor-mate). -/
def omegaComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (N A E X).obj (nativeOmega A E f) ≅ omega (ULift.{u + 1} A) f :=
  exceptionalComparison A E f _ ≪≫
    (G (ULift.{u + 1} A) f).mapIso (unitComparison A E Y)

/-- The coefficient unit comparison of the recorded monoidal encoding.
Source: def-sf-finite-realization-monoidal (blueprint: lem-pur-composition-tensor-mate). -/
def unitComparison (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :
    (N A E T).obj (𝟙_ (Native A T)) ≅ unit (ULift.{u + 1} A) T := by
  letI := FiniteNativeTensor.encodingMonoidal A T (E T)
  exact (Functor.Monoidal.εIso (N A E T)).symm

/-- The actual native projection arrow recorded by def-exchange-projection.
Source: specified projection (blueprint: lem-pur-composition-tensor-mate). -/
abbrev nativeProjection {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : Native A X) (K : Native A Y) :=
  (CondensedRing.exchangeProjectionData (coefficient A)
    (HasCompactification.compactification f) (𝟙 Y)).projection M K

/-- The native dualizing object is the exceptional image of the native tensor unit.
Source: omega_h (blueprint: lem-pur-composition-tensor-mate). -/
def nativeOmega (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : Native A X :=
  (exceptional A E f).obj (𝟙_ (Native A Y))

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

/-- The actual specified coefficient-equivalence counit at the exceptional value.
Source: coefficient coordinate cancellation (blueprint: lem-pur-composition-tensor-mate). -/
def exceptionalComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : Native A Y) :
    (N A E X).obj ((exceptional A E f).obj K) ≅
      (G (ULift.{u + 1} A) f).obj ((N A E Y).obj K) :=
  (E X).fixedDerived.counitIso.app _

/-- The finite comparison exceptional operation in the internal coefficient presentation.
Its functor is the conjugate of the published nu^* f^times Rnu_* composite. The Hom
normalization is specified below, so this is not an arbitrary right-adjoint identification.
Source: finite paragraph of def-weil-exceptional-inverse-image
(blueprint: lem-pur-composition-tensor-mate). -/
def exceptional (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Native A Y ⥤ Native A X :=
  (E Y).fixedDerived.functor ⋙ G (ULift.{u + 1} A) f ⋙ (E X).fixedDerived.inverse

/-- Reuse the recorded open/proper encoding paste for the very same compactification.
Source: def-pur-finite-compact-support-encoding
(blueprint: lem-pur-composition-tensor-mate). -/
abbrev canonicalSupport (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  FiniteNativeTensor.compactEncoding A E (HasCompactification.compactification f)

/-- The existing native proper/open compact-support composite.
Source: compact-support convention (blueprint: lem-pur-composition-tensor-mate). -/
abbrev nativeSupport {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  CondensedRing.CompactificationReindexing.F (coefficient A)
    (HasCompactification.compactification f)

/-- The existing native derived inverse image, without a replacement construction.
Source: derived operations (blueprint: lem-pur-composition-tensor-mate). -/
abbrev nativePull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CondensedRing.CompactificationReindexing.P (coefficient A) f

/-- The recorded normalized derived coefficient encoding.
Source: def-pe-finite-discrete-presentation-encoding
(blueprint: lem-pur-composition-tensor-mate). -/
abbrev N (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) :=
  (E T).fixedDerived.functor

/-- The published internal-module derived category over Lambda_T.
Source: finite coefficient convention (blueprint: lem-pur-composition-tensor-mate). -/
abbrev Native (T : Scheme.{u}) := _root_.DerivedCategory (Internal A T)

/-- The native tensor map is its standing Hom transpose, using native projection,
Koszul symmetry, the actual counit at the native unit, and the left unitor.
Source: defining theta transpose (blueprint: lem-pur-composition-tensor-mate). -/
def nativeTheta (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : Native A Y) : (nativePull A f).obj K ⊗ nativeOmega A E f ⟶
      (exceptional A E f).obj K :=
  open Classical in
  let M := (nativePull A f).obj K ⊗ nativeOmega A E f
  if hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K) then
    if hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
        ((N A E X).obj M) then
      exceptionalHomEquiv A E f M K hM hK
        ((nativeSupport A f).map
            (derivedTensorKoszulSymmetry (Internal A X)
              ((nativePull A f).obj K) (nativeOmega A E f)).hom ≫
          inverseOnDomain (nativeProjection A f (nativeOmega A E f) K) ≫
          nativeEpsilon A E f (𝟙_ (Native A Y)) ▷ K ≫ (λ_ K).hom)
    else 0
  else 0

/-- The native exceptional compositor is the specified successive Hom transpose of
nativeAlpha followed by nativeEpsilon. Thus its adjunction normalization is fixed.
Source: pur9-def-upper-shriek-composition (blueprint: lem-pur-composition-tensor-mate). -/
def nativeC (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (K : Native A Z) : (exceptional A E (f ≫ g)).obj K ⟶
      (exceptional A E f).obj ((exceptional A E g).obj K) :=
  open Classical in
  let M := (exceptional A E (f ≫ g)).obj K
  if hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Z).obj K) then
    if hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
        ((N A E X).obj M) then
      if hF : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y
          ((N A E Y).obj ((nativeSupport A f).obj M)) then
        if hG : _root_.DerivedCategory.TStructure.t.plus
            ((N A E Y).obj ((exceptional A E g).obj K)) then
          (exceptionalHomEquiv A E g _ K hF hK).trans
            (exceptionalHomEquiv A E f M _ hM hG)
            (nativeAlpha A E f g M ≫ nativeEpsilon A E (f ≫ g) K)
        else 0
      else 0
    else 0
  else 0

/-- The native standing counit is the inverse Hom image of the identity. The guarded
zero extension is outside the bounded-below domains only, as in the fixed coordinates.
Source: standing counit (blueprint: lem-pur-composition-tensor-mate). -/
def nativeEpsilon (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : Native A Y) : (nativeSupport A f).obj ((exceptional A E f).obj K) ⟶ K :=
  open Classical in
  if hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K) then
    if hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
        ((N A E X).obj ((exceptional A E f).obj K)) then
      (exceptionalHomEquiv A E f _ K hM hK).symm (𝟙 _)
    else 0
  else 0

end Maps

/-- The complete assertion with source-implied compactifications and size conventions
installed internally. The comparison c is explicitly identified with the recorded
standingExceptionalComposition, so the assertion is about that specified mate.
Source: complete node statement (blueprint: lem-pur-composition-tensor-mate). -/
def Assertion (P : WeilConjectures.PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (d e : ℕ) : Prop :=
  letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  letI : UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient) :=
    upperStarPreservesFlat_moduleCat P.Coefficient
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of P.field.k))
  letI := (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification g (Z ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification (f ≫ g)
    (Z ↘ Spec (.of P.field.k))).hasCompactification
  SmoothOfRelativeDimension (d + e) (f ≫ g) ∧ IsSeparated (f ≫ g) ∧
    LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧
    (∀ K : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} P.Coefficient) Z,
      c P.Coefficient f g K.obj = standingExceptionalComposition P f g K) ∧
    Package P.Coefficient f g

end CompositionTensorMate
end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

private theorem tensor_source_calculation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (V : C ⥤ D) {N O U : C} {A W B Z : D}
    (p : A ⟶ V.obj N) (v : W ⟶ V.obj O) (c : V.obj N ⟶ B)
    (r : V.obj U ⟶ Z) (a : O ⟶ U)
    (tNO : V.obj (N ⊗ O) ≅ V.obj N ⊗ V.obj O)
    (tNU : V.obj (N ⊗ U) ≅ V.obj N ⊗ V.obj U)
    (tUN : V.obj (U ⊗ N) ≅ V.obj U ⊗ V.obj N)
    (hn : V.map (N ◁ a) ≫ tNU.hom = tNO.hom ≫ V.obj N ◁ V.map a)
    (hb : V.map (β_ N U).hom ≫ tUN.hom =
      tNU.hom ≫ (β_ (V.obj N) (V.obj U)).hom)
    (hs : (β_ B Z).hom ≫ (β_ Z B).hom = 𝟙 _) :
    (p ⊗ₘ v) ≫ tNO.inv ≫ V.map (N ◁ a) ≫ V.map (β_ N U).hom ≫
        tUN.hom ≫ (r ⊗ₘ c) ≫ (β_ Z B).hom =
      (p ≫ c) ⊗ₘ (v ≫ V.map a ≫ r) := by
  have hn' : tNO.inv ≫ V.map (N ◁ a) = V.obj N ◁ V.map a ≫ tNU.inv := by
    apply (cancel_mono tNU.hom).1
    simp only [Category.assoc, hn, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hb' : tNU.inv ≫ V.map (β_ N U).hom ≫ tUN.hom =
      (β_ (V.obj N) (V.obj U)).hom := by
    rw [hb, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn']
  rw [reassoc_of% hb']
  rw [← reassoc_of% (BraidedCategory.braiding_naturality c r)]
  simp only [hs, Category.comp_id]
  rw [← id_tensorHom]
  simp only [tensorHom_comp_tensorHom, Category.id_comp]

private theorem inverse_square_eq
    {C : Type*} [Category C] {A B U V : C}
    (a : A ≅ B) (b : U ≅ V) (p : A ⟶ U) (q : B ⟶ V)
    [IsIso p] [IsIso q] (h : a.hom ≫ q = p ≫ b.hom) :
    b.hom ≫ inv q = inv p ≫ a.hom := by
  apply (cancel_epi p).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← h]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem invert_projection_square
    {C : Type*} [Category C] {A B Q S T U : C}
    (p : A ⟶ B) (q : U ⟶ S) [IsIso p] [IsIso q]
    (b : Q ≅ B) (i : Q ≅ S) (t : A ≅ T) (w : T ≅ U)
    (h : p ≫ b.inv ≫ i.hom = t.hom ≫ w.hom ≫ q) :
    i.hom ≫ inv q = b.hom ≫ inv p ≫ t.hom ≫ w.hom := by
  have h' := congrArg (fun z ↦ b.hom ≫ inv p ≫ z ≫ inv q) h
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    IsIso.hom_inv_id, Category.comp_id] using h'

private theorem projection_tail_calculation
    {C : Type*} [Category C] {P Q R S T U V W X Y : C}
    (c : P ⟶ Q) (b : Q ⟶ R) (qi : R ⟶ S) (pi : Q ⟶ T)
    (a : T ⟶ S) (ε : S ⟶ U) (l : U ⟶ V)
    (i : P ⟶ W) (vi : W ⟶ X) (t : X ⟶ Y) (w : Y ⟶ T) (z : X ⟶ V)
    (h₁ : b ≫ qi = pi ≫ a) (h₂ : c ≫ pi = i ≫ vi ≫ t ≫ w)
    (h₃ : t ≫ w ≫ a ≫ ε ≫ l = z) :
    c ≫ b ≫ qi ≫ ε ≫ l = i ≫ vi ≫ z := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem derived_tensor_source_calculation
    (V : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    {N O U : _root_.DerivedCategory C} {A W B Z : _root_.DerivedCategory D}
    (p : A ⟶ V.obj N) (v : W ⟶ V.obj O) (c : V.obj N ⟶ B)
    (r : V.obj U ⟶ Z) (a : O ⟶ U)
    (tNO : V.obj (N ⊗ O) ≅ V.obj N ⊗ V.obj O)
    (tNU : V.obj (N ⊗ U) ≅ V.obj N ⊗ V.obj U)
    (tUN : V.obj (U ⊗ N) ≅ V.obj U ⊗ V.obj N)
    (hn : V.map (N ◁ a) ≫ tNU.hom = tNO.hom ≫ V.obj N ◁ V.map a)
    (hb : V.map (derivedTensorKoszulSymmetry C N U).hom ≫ tUN.hom =
      tNU.hom ≫ (derivedTensorKoszulSymmetry D (V.obj N) (V.obj U)).hom)
    (hs : (derivedTensorKoszulSymmetry D B Z).hom ≫
      (derivedTensorKoszulSymmetry D Z B).hom = 𝟙 _) :
    (p ⊗ₘ v) ≫ tNO.inv ≫ V.map (N ◁ a) ≫
        V.map (derivedTensorKoszulSymmetry C N U).hom ≫
        tUN.hom ≫ (r ⊗ₘ c) ≫ (derivedTensorKoszulSymmetry D Z B).hom =
      (p ≫ c) ⊗ₘ (v ≫ V.map a ≫ r) := by
  let bC := _root_.DerivedCategory.braidedCategory' C
  let bD := _root_.DerivedCategory.braidedCategory' D
  have h := tensor_source_calculation V p v c r a tNO tNU tUN hn hb hs
  simpa only [bC, bD, derivedTensorKoszulSymmetry, BraidedCategory.braiding,
    _root_.DerivedCategory.braidedCategory', DerivedMonoidal.braidedCategory'] using h

@[local tactic startMateProof] private meta def elabStartMateProof : Tactic := fun _ => do
  withMainContext do
    let g ← getMainGoal
    let h ← mkFreshExprSyntheticOpaqueMVar (← g.getType)
    g.setTag h.mvarId!.name
    replaceMainGoal [h.mvarId!, g]

@[local tactic finishMateProof] private meta def elabFinishMateProof : Tactic := fun _ => do
  withMainContext do
    let g ← getMainGoal
    let h : MVarId := ⟨← g.getTag⟩
    let proof ← instantiateMVars (mkMVar h)
    if proof.hasMVar then
      throwError "The mate proof has unresolved goals"
    let helpers := #[``transport_tensor_hom, ``transport_braiding,
      ``derived_comparison_tensor, ``derived_comparison_koszul, ``derived_comparison_braiding,
      ``tensor_source_calculation, ``projection_tail_calculation,
      ``inverse_square, ``inverse_square_eq,
      ``invert_projection_square]
    let proof ← Meta.transform proof (skipConstInApp := true) (pre := fun e => do
      if let .const n us := e.getAppFn then
        if helpers.contains n then
          let ci ← getConstInfo n
          return .visit ((← instantiateValueLevelParams ci us (allowOpaque := true)).beta
            e.getAppArgs)
      return .continue)
    let proof ← zetaReduce proof
    if proof.hasSorry then
      throwError "The mate proof contains an unfinished proof"
    g.assign proof
    replaceMainGoal []

private theorem proEtale_derived_symmetry
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (J K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) A) J K).hom ≫
      (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) A) K J).hom = 𝟙 _ := by
  exact _root_.DerivedCategory.braiding_hom_braiding_hom
    (Sheaf (Scheme.ProEt.topology X) A) (fun _ _ ↦ SymmetricCategory.symmetry _ _) J K

private theorem comparison_factors_eq
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) :
    let C := ProEtale.comparisonUpperStar A X
    C.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      C.mapDerivedCategoryFactors.hom.app K := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar A X
    change C.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      C.mapDerivedCategoryFactors.hom.app K
    erw [C.mapDerivedCategoryFactorsh_hom_app]
    have h₁ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf X.smallEtaleTopology A)).hom.app K = 𝟙 _ := fun _ ↦ rfl
    have h₂ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf (Scheme.ProEt.topology X) A)).inv.app K = 𝟙 _ :=
      fun _ ↦ rfl
    have h₃ : ∀ K, (C.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := fun _ ↦ rfl
    erw [h₁, h₂, h₃, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  · finish_mate_proof

private theorem comparison_Qh_map
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    {K L : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ}
    (g : K ⟶ L) :
    _root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map g) =
      _root_.DerivedCategory.Q.map g := by
  start_mate_proof
  · have h := _root_.DerivedCategory.quotientCompQhIso_hom_naturality g
    have hi : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf (Scheme.ProEt.topology X) A)).hom.app K = 𝟙 _ :=
      fun _ ↦ rfl
    rw [hi, hi] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  · finish_mate_proof

private theorem comparison_oplax_unit_formula
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat] :
    let C := ProEtale.comparisonUpperStar A X
    letI := C.mapDerivedCategoryOplaxMonoidal
    Functor.OplaxMonoidal.η C.mapDerivedCategory =
      C.mapDerivedCategory.map
          (_root_.DerivedCategory.singleFunctorObjUnitIso
            (Sheaf X.smallEtaleTopology A)).inv ≫
        (C.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) ≫
        (_root_.DerivedCategory.singleFunctor (Sheaf (Scheme.ProEt.topology X) A) 0).map
          (Functor.OplaxMonoidal.η C) ≫
        (_root_.DerivedCategory.singleFunctorObjUnitIso
          (Sheaf (Scheme.ProEt.topology X) A)).hom := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar A X
    let := C.mapDerivedCategoryOplaxMonoidal
    have h₁ : Functor.LaxMonoidal.ε
        (_root_.DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology
          A)) = 𝟙 _ := rfl
    have h₂ : Functor.LaxMonoidal.ε
        (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X)
          A)) = 𝟙 _ := rfl
    change _ ≫ _ ≫ _ ≫ inv (Functor.LaxMonoidal.ε _) = _
    have hi : inv (Functor.LaxMonoidal.ε
        (_root_.DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X)
          A))) = 𝟙 _ := by
      apply (cancel_epi (Functor.LaxMonoidal.ε _)).1
      rw [IsIso.hom_inv_id, Category.comp_id]
      exact h₂.symm
    rw [h₁, CategoryTheory.Functor.map_id, Category.id_comp, hi, Category.comp_id,
      C.mapHomotopyCategory_η]
    have hq₁ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf X.smallEtaleTopology A)).hom.app K = 𝟙 _ := fun _ ↦ rfl
    have hq₂ : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
        (Sheaf (Scheme.ProEt.topology X) A)).inv.app K = 𝟙 _ :=
      fun _ ↦ rfl
    have he₁ : (Functor.Monoidal.εIso (HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology A) (.up ℤ))).hom = 𝟙 _ := rfl
    have he₂ : (Functor.Monoidal.εIso (HomotopyCategory.quotient
        (Sheaf (Scheme.ProEt.topology X) A) (.up ℤ))).inv = 𝟙 _ := rfl
    simp only [_root_.DerivedCategory.singleFunctorObjUnitIso,
      Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, _root_.DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, asIso_hom, asIso_inv,
      h₁, hi, hq₁, hq₂, he₁, he₂, Functor.associator_hom_app,
      Functor.associator_inv_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
    erw [comparison_factors_eq A X, comparison_Qh_map A X]
    simp only [Functor.mapCochainComplex_η, Functor.mapCochainComplexεIso,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Functor.Monoidal.εIso_inv, Functor.map_comp,
      Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    rfl
  · finish_mate_proof

private def derivedComparisonUnitIso
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (e : (ProEtale.comparisonUpperStar A X).obj (𝟙_ _) ≅ 𝟙_ _) :
    (ProEtale.comparisonUpperStar A X).mapDerivedCategory.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (ProEtale.comparisonUpperStar A X).mapDerivedCategory.mapIso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((ProEtale.comparisonUpperStar A X).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

private theorem comparison_oplax_unit_iso
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (e : (ProEtale.comparisonUpperStar A X).obj (𝟙_ _) ≅ 𝟙_ _)
    (hη : Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar A X) = e.hom) :
    letI := (ProEtale.comparisonUpperStar A X).mapDerivedCategoryOplaxMonoidal
    Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar A X).mapDerivedCategory =
      (derivedComparisonUnitIso A X e).hom := by
  simpa only [derivedComparisonUnitIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, hη] using comparison_oplax_unit_formula A X

private theorem comparison_underived_unit
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Functor.OplaxMonoidal.η (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) =
      (ProEtale.comparisonUpperStarUnitIso A X).hom := by
  simp only [ProEtale.comparisonUpperStarUnitIso, asIso_hom]
  rfl

private theorem comparison_oplax_unit
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
    letI := C.mapDerivedCategoryOplaxMonoidal
    Functor.OplaxMonoidal.η C.mapDerivedCategory =
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A X).hom := by
  exact comparison_oplax_unit_iso (ModuleCat.{u + 1} A) X
    (ProEtale.comparisonUpperStarUnitIso A X) (comparison_underived_unit A X)

private theorem comparison_left_unitor_oplax
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let C := ProEtale.comparisonUpperStar A X
    letI := C.mapDerivedCategoryOplaxMonoidal
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso A (𝟙_ _)).hom.app J ≫
      Functor.OplaxMonoidal.η C.mapDerivedCategory ▷ C.mapDerivedCategory.obj J ≫
      (λ_ (C.mapDerivedCategory.obj J)).hom = C.mapDerivedCategory.map (λ_ J).hom := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar A X
    let := C.mapDerivedCategoryOplaxMonoidal
    rw [comparison_tensor_eq]
    simpa only [Functor.mapDerivedCategoryOplaxMonoidal_δ] using
      Functor.OplaxMonoidal.left_unitality_hom C.mapDerivedCategory J
  · finish_mate_proof

private theorem comparison_left_unitor
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (J : Etale.DerivedCategoryModule A X) :
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (𝟙_ _)).hom.app J ≫
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A X).hom ▷
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J ≫
      (λ_ ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J)).hom =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (λ_ J).hom := by
  start_mate_proof
  · let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
    let := C.mapDerivedCategoryOplaxMonoidal
    have h := comparison_left_unitor_oplax (ModuleCat.{u + 1} A) X J
    change (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) (𝟙_ _)).hom.app J ≫
        Functor.OplaxMonoidal.η C.mapDerivedCategory ▷ C.mapDerivedCategory.obj J ≫
        (λ_ (C.mapDerivedCategory.obj J)).hom = C.mapDerivedCategory.map (λ_ J).hom at h
    erw [comparison_oplax_unit A X] at h
    exact h
  · finish_mate_proof

private theorem etaleUnitPlus (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (Etale.DerivedCategoryModule A Y)) := by
  start_mate_proof
  · exact ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  · finish_mate_proof

private theorem proUnitPlus (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus (𝟙_ (D A Y)) := by
  start_mate_proof
  · exact ((ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).prop_of_iso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
      (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
        (etaleUnitPlus A Y))).plus
  · finish_mate_proof

private def standingUnitComparison
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.dualizingComplex A f) ≅ omega A f :=
  letI := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y (𝟙_ _) (etaleUnitPlus A Y)
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
    ((Etale.rightDerivedUpperShriek A f).mapIso
      (asIso ((ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} A) Y).unit.app (𝟙_ _)))) ≪≫
    (G A f).mapIso
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)

private def etaleMateSource
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} A)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (J : Etale.DerivedCategoryModule A Y) (M : D A Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J ≅ M) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.dualizingComplex A f ⊗
        (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj J) ≅
        (S A f).obj M ⊗ omega A f :=
  ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J ≪≫
    tensorIso (standingUnitComparison A f) ((S A f).mapIso e) ≪≫
    derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (omega A f) ((S A f).obj M)

private def normalizedStandingCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : D A Y) (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (F A f).obj ((G A f).obj K) ⟶ K :=
  (ProEtale.fixedCompactSupportComparisonIso A
    (HasCompactification.compactification f)).hom.app
      ⟨_, ProEtale.plus_etaleRightDerivedUpperShriek_obj f hK⟩ ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app _) ≫
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).counit.app K

private theorem standingHom_symm
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {M : D A X} (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    {K : D A Y} (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (b : M ⟶ (G A f).obj K) :
    (ProEtale.standingExceptionalHomEquiv A f hM hK).symm b =
      (F A f).map b ≫ normalizedStandingCounit A f K hK := by
  start_mate_proof
  · classical
    let hex : ∃ J : Etale.DerivedCategoryModule A X,
        _root_.DerivedCategory.TStructure.t.plus J ∧
          Nonempty ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J ≅ M) := hM
    let J := Classical.choose hex
    let hJ := (Classical.choose_spec hex).1
    let e := Classical.choice (Classical.choose_spec hex).2
    let VX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let VY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let UY := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor
    let H := Etale.rightDerivedUpperShriek A f
    let ad := Etale.rightDerivedUpperShriekAdjunction A f
    let av := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
    let B := ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)
    let hHK := ProEtale.plus_etaleRightDerivedUpperShriek_obj f hK
    obtain ⟨q, hq⟩ :=
      (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map J
        (H.obj (UY.obj K)) hHK).surjective (e.hom ≫ b)
    change VX.map q = e.hom ≫ b at hq
    have hn := B.inv.naturality (ObjectProperty.homMk q :
      (⟨J, hJ⟩ : _root_.DerivedCategory.Plus _) ⟶ ⟨H.obj (UY.obj K), hHK⟩)
    change VY.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) ≫
        B.inv.app ⟨H.obj (UY.obj K), hHK⟩ =
      B.inv.app ⟨J, hJ⟩ ≫ (F A f).map (VX.map q) at hn
    apply (ProEtale.standingExceptionalHomEquiv A f hM hK).injective
    rw [Equiv.apply_symm_apply]
    symm
    change e.inv ≫ VX.map (ad.homEquiv J (UY.obj K)
      (av.homEquiv _ K (B.inv.app ⟨J, hJ⟩ ≫
        (F A f).map e.hom ≫ (F A f).map b ≫
          normalizedStandingCounit A f K hK))) = b
    have hz : B.inv.app ⟨J, hJ⟩ ≫
        (F A f).map e.hom ≫ (F A f).map b ≫
          normalizedStandingCounit A f K hK =
      VY.map ((ad.homEquiv J (UY.obj K)).symm q) ≫ av.counit.app K := by
      rw [← Functor.map_comp_assoc, ← hq, ← Category.assoc, ← hn]
      simp only [normalizedStandingCounit, Category.assoc]
      change VY.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) ≫
          B.inv.app ⟨H.obj (UY.obj K), hHK⟩ ≫
            B.hom.app ⟨H.obj (UY.obj K), hHK⟩ ≫
              VY.map (ad.counit.app (UY.obj K)) ≫ av.counit.app K = _
      rw [Iso.inv_hom_id_app_assoc]
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [hz]
    change e.inv ≫ VX.map (ad.homEquiv J (UY.obj K)
      (av.homEquiv _ K ((av.homEquiv _ K).symm
        ((ad.homEquiv J (UY.obj K)).symm q)))) = b
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hq]
    simp
  · finish_mate_proof

private theorem standingHom_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {M N : D A X}
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hN : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X N)
    {K : D A Y} (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (a : M ⟶ N) (z : (F A f).obj N ⟶ K) :
    ProEtale.standingExceptionalHomEquiv A f hM hK ((F A f).map a ≫ z) =
      a ≫ ProEtale.standingExceptionalHomEquiv A f hN hK z := by
  start_mate_proof
  · apply (ProEtale.standingExceptionalHomEquiv A f hM hK).symm.injective
    rw [Equiv.symm_apply_apply, standingHom_symm, Functor.map_comp, Category.assoc,
      ← standingHom_symm A f hN hK, Equiv.symm_apply_apply]
  · finish_mate_proof

private theorem standingHom_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (Q : Etale.DerivedCategoryModule A X)
    (hQ : _root_.DerivedCategory.TStructure.t.plus Q)
    (J : Etale.DerivedCategoryModule A Y) (M : D A Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J ≅ M)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (z : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj Q ⟶ J) :
    ProEtale.standingExceptionalHomEquiv A f ⟨Q, hQ, ⟨Iso.refl _⟩⟩ hM
      ((ProEtale.fixedCompactSupportComparisonIso A
        (HasCompactification.compactification f)).hom.app ⟨Q, hQ⟩ ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map z ≫
          e.hom) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv Q J z) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek A f).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app J ≫
            (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor.map
              e.hom)) := by
  start_mate_proof
  · let VX := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let VY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let UY := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor
    let H := Etale.rightDerivedUpperShriek A f
    let ad := Etale.rightDerivedUpperShriekAdjunction A f
    let av := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
    let B := ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)
    let q := ad.homEquiv Q J z ≫ H.map (av.unit.app J ≫ UY.map e.hom)
    have hn := B.hom.naturality (ObjectProperty.homMk q :
      (⟨Q, hQ⟩ : _root_.DerivedCategory.Plus _) ⟶
      ⟨_, ProEtale.plus_etaleRightDerivedUpperShriek_obj f hM⟩)
    change (F A f).map (VX.map q) ≫
        B.hom.app ⟨H.obj (UY.obj M),
          ProEtale.plus_etaleRightDerivedUpperShriek_obj f hM⟩ =
      B.hom.app ⟨Q, hQ⟩ ≫ VY.map
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) at hn
    apply (ProEtale.standingExceptionalHomEquiv A f ⟨Q, hQ, ⟨Iso.refl _⟩⟩ hM).symm.injective
    rw [Equiv.symm_apply_apply, standingHom_symm]
    change B.hom.app ⟨Q, hQ⟩ ≫ VY.map z ≫ e.hom =
      (F A f).map (VX.map (ad.homEquiv Q J z) ≫
        VX.map (H.map (av.unit.app J ≫ UY.map e.hom))) ≫
        normalizedStandingCounit A f M hM
    rw [← VX.map_comp]
    change _ = (F A f).map (VX.map q) ≫ normalizedStandingCounit A f M hM
    unfold normalizedStandingCounit
    rw [← Category.assoc, ← Category.assoc, hn]
    simp only [Category.assoc]
    change B.hom.app ⟨Q, hQ⟩ ≫ VY.map z ≫ e.hom =
      B.hom.app ⟨Q, hQ⟩ ≫
        VY.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q) ≫
          VY.map (ad.counit.app (UY.obj M)) ≫ av.counit.app M
    rw [← VY.map_comp_assoc]
    have hq : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map q ≫
        ad.counit.app (UY.obj M) = z ≫ (av.unit.app J ≫ UY.map e.hom) := by
      change (ad.homEquiv Q (UY.obj M)).symm q = _
      dsimp only [q]
      rw [Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
    rw [hq]
    simp only [VY.map_comp, Category.assoc]
    erw [av.counit.naturality]
    erw [reassoc_of% (av.left_triangle_components J)]
    rfl
  · finish_mate_proof

private theorem epsilon_eq_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : D A Y) (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    epsilon A f K = normalizedStandingCounit A f K hK := by
  start_mate_proof
  · classical
    simp only [epsilon, dif_pos hK]
    rw [standingHom_symm, CategoryTheory.Functor.map_id, Category.id_comp]
  · finish_mate_proof

private theorem standingUnitComparison_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y] :
    (F A f).map (standingUnitComparison A f).hom ≫ epsilon A f (𝟙_ _) =
    (ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)).hom.app
        ⟨Etale.dualizingComplex A f,
          Etale.plus_rightDerivedUpperShriek_obj A f (𝟙_ _) (etaleUnitPlus A Y)⟩ ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom := by
  start_mate_proof
  · let hΩ := Etale.plus_rightDerivedUpperShriek_obj A f (𝟙_ _) (etaleUnitPlus A Y)
    have h := standingHom_comparison A f (Etale.dualizingComplex A f) hΩ
      (𝟙_ _) (𝟙_ _)
      (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y)
      (proUnitPlus A Y) ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))
    have hid : (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv
        (Etale.dualizingComplex A f) (𝟙_ _)
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) = 𝟙 _ := by
      rw [← Adjunction.homEquiv_symm_id]
      exact Equiv.apply_symm_apply _ _
    rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
    apply_fun (ProEtale.standingExceptionalHomEquiv A f
      ⟨Etale.dualizingComplex A f, hΩ, ⟨Iso.refl _⟩⟩ (proUnitPlus A Y)).symm at h
    rw [Equiv.symm_apply_apply, standingHom_symm] at h
    rw [epsilon_eq_normalized A f (𝟙_ _) (proUnitPlus A Y)]
    symm
    simpa only [standingUnitComparison, Iso.trans_hom, Functor.mapIso_hom,
      asIso_hom, Functor.map_comp, G, ProEtale.rightDerivedUpperShriek,
      Functor.comp_map] using h
  · finish_mate_proof

private theorem projection_iso_naturality
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {N N' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (r : N ≅ N') (e : K ≅ K') :
    let Fp := ProEtale.rightDerivedLowerShriek A f
    let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
    let pp := ProEtale.projectionMap A f
    (tensorIso (Fp.mapIso r) e).hom ≫ (pp.app N').app K' =
      (pp.app N).app K ≫ (Fp.mapIso (tensorIso r (Sp.mapIso e))).hom := by
  dsimp only
  let Fp := ProEtale.rightDerivedLowerShriek A f
  let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
  let pp := ProEtale.projectionMap A f
  have hn₁ := congr_app (pp.naturality r.hom) K
  have hn₂ := (pp.app N').naturality e.hom
  change Fp.map r.hom ▷ K ≫ (pp.app N').app K =
    (pp.app N).app K ≫ Fp.map (r.hom ▷ Sp.obj K) at hn₁
  change Fp.obj N' ◁ e.hom ≫ (pp.app N').app K' =
    (pp.app N').app K ≫ Fp.map (N' ◁ Sp.map e.hom) at hn₂
  simp only [tensorIso_hom, Functor.mapIso_hom, MonoidalCategory.tensorHom_def,
    Category.assoc]
  rw [hn₂, ← Category.assoc, hn₁]
  simp only [Category.assoc, ← Fp.map_comp]
  rfl

private theorem tensor_source_cancel
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {Q N N' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (c : Q ≅ N ⊗ (ProEtale.upperStar A f).leftDerivedFunctor.obj K)
    (r : N ≅ N') (e : K ≅ K') :
    let Fp := ProEtale.rightDerivedLowerShriek A f
    let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
    Fp.map (c ≪≫ tensorIso r (Sp.mapIso e) ≪≫
      derivedTensorKoszulSymmetry _ N' (Sp.obj K')).hom ≫
        Fp.map (derivedTensorKoszulSymmetry _ (Sp.obj K') N').hom =
      Fp.map c.hom ≫ (Fp.mapIso (tensorIso r (Sp.mapIso e))).hom := by
  dsimp only
  let Fp := ProEtale.rightDerivedLowerShriek A f
  let Sp := (ProEtale.upperStar A f).leftDerivedFunctor
  have hs := proEtale_derived_symmetry A X N' (Sp.obj K')
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [← Fp.map_comp, hs, Fp.map_id, Category.comp_id]
  rfl

private theorem genericTensorTranspose_expansion
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (ε : (ProEtale.rightDerivedLowerShriek A f).obj N ⟶ 𝟙_ _) :
    genericTensorTranspose A f N M ε =
      (ProEtale.rightDerivedLowerShriek A f).map
        (derivedTensorKoszulSymmetry (Sheaf (Scheme.ProEt.topology X) A)
          ((ProEtale.upperStar A f).leftDerivedFunctor.obj M) N).hom ≫
        inverseOnDomain (((ProEtale.projectionMap A f).app N).app M) ≫
          ε ▷ M ≫ (λ_ M).hom := by
  rfl

private theorem tensorTranspose_of_projection_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} A)]
    (J : Etale.DerivedCategoryModule A Y) (M : D A Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J ≅ M)
    [IsIso (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
      (Etale.dualizingComplex A f)).app J)]
    [IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (Etale.dualizingComplex A f))).app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J))]
    (hΩplus : _root_.DerivedCategory.TStructure.t.plus (Etale.dualizingComplex A f))
    (hQ : _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj (Etale.dualizingComplex A f)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj J)))
    (hs :
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
            (HasCompactification.compactification f)).app (Etale.dualizingComplex A f)).app J) ≫
        (ProEtale.fixedCompactSupportComparisonIso A
          (HasCompactification.compactification f)).inv.app ⟨_, hQ⟩ ≫
        (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).map
            (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom =
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A)
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).obj (Etale.dualizingComplex A f))).hom.app J ≫
        ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).map
          ((ProEtale.fixedCompactSupportComparisonIso A
            (HasCompactification.compactification f)).inv.app
              ⟨Etale.dualizingComplex A f, hΩplus⟩)).app
                ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J) ≫
        ((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).app
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              (Etale.dualizingComplex A f))).app
                ((ProEtale.comparisonUpperStar
                  (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj J)) :
    (F A f).map (etaleMateSource A f J M e).hom ≫
      genericTensorTranspose (ModuleCat.{u + 1} A) f
        (omega A f) M (epsilon A f (𝟙_ _)) =
    (ProEtale.fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)).hom.app
      ⟨_, hQ⟩ ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (inv (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
          (Etale.dualizingComplex A f)).app J) ≫
          (Etale.rightDerivedUpperShriekAdjunction A f).counit.app
            (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
  let : IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) :=
      inferInstance
  have hn : (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e).hom ≫
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) =
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) ≫ ((F A
      f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom := by
    exact projection_iso_naturality (ModuleCat.{u + 1} A) f (standingUnitComparison A f) e
  let : IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) :=
      inverse_square (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e) ((F A f).mapIso
      (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))) (((ProEtale.projectionMap
      (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
      X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) (((ProEtale.projectionMap (ModuleCat.{u +
      1} A) f).app (omega A f)).app M) hn
  have hn' := inverse_square_eq (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e) ((F A
      f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e)))
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
      (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) hn
  have hi := invert_projection_square
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
        (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app (Etale.dualizingComplex A f)).app J))
        (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))
        ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
        ⟨_, hQ⟩) ((F A f).mapIso (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f)
        J))
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
          (Etale.dualizingComplex A f))).app J)
    (tensorIso ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification
        f)).app ⟨(Etale.dualizingComplex A f), hΩplus⟩).symm (Iso.refl
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))) (by
      simpa only [F,
        ProEtale.projectionMap, Etale.projectionMap,
        ProEtale.rightDerivedLowerShriek, Etale.rightDerivedLowerShriek,
        ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
        Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
        ProEtale.derivedTensorRightDerivedLowerShriek,
        Etale.derivedTensorRightDerivedLowerShriek, ProEtale.derivedTensor,
        Etale.derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
        curriedTensor_obj_obj, Functor.comp_obj, Iso.app_hom, Iso.app_inv,
        Functor.mapIso_hom, tensorIso_hom, Iso.symm_hom, Iso.refl_hom,
        tensorHom_id] using hs)
  have hc := standingUnitComparison_counit A f
  have hc' : ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification
      f)).app ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ≫ (F A f).map (standingUnitComparison A
      f).hom ≫ epsilon A f (𝟙_ _) =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A Y).hom := by
    simp only [hc, Iso.app_inv]
    erw [Iso.inv_hom_id_app_assoc]
  have ht₀ := congr_app ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
      Y).mapDerivedCategoryTensorComparison.naturality
    ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))) J
  have ht : ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _) ▷ J) ≫
        (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          (ModuleCat.{u + 1} A) (𝟙_ _)).hom.app J =
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.dualizingComplex A f))).hom.app J ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
            ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ▷
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J := by
    rw [comparison_tensor_eq, comparison_tensor_eq]
    change ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
      ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _) ▷ J) ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
            Y).mapDerivedCategoryTensorComparison.app (𝟙_ _)).app J =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryTensorComparison.app
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj (Etale.dualizingComplex A
          f))).app J ≫
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
            ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ▷
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J at ht₀
    exact ht₀
  have htail :
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.dualizingComplex A f))).hom.app J ≫
        ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
            ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ▷ ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J ≫ (tensorIso ((F A f).mapIso
            (standingUnitComparison A f)) e).hom ≫
        epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
    change _ ≫ _ ≫ ((F A f).map (standingUnitComparison A f).hom ⊗ₘ e.hom) ≫ _ ≫ _ = _
    rw [← tensorHom_id, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    rw [hc', MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc,
      leftUnitor_naturality, ← Category.assoc, ← Category.assoc]
    rw [← reassoc_of% ht]
    simp only [Category.assoc]
    erw [reassoc_of% (comparison_left_unitor A Y J)]
    simp only [Functor.map_comp, Category.assoc]
  have hcancel : (F A f).map (etaleMateSource A f J M e).hom ≫
      (F A f).map (derivedTensorKoszulSymmetry _ ((S A f).obj M) (omega A f)).hom =
      (F A f).map (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom ≫ ((F A
          f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom := by
    exact tensor_source_cancel (ModuleCat.{u + 1} A) f (ProEtale.comparisonOpenTensorIso A f
        (Etale.dualizingComplex A f) J) (standingUnitComparison A f) e
  rw [genericTensorTranspose_expansion]
  change (F A f).map (etaleMateSource A f J M e).hom ≫
    ((F A f).map (derivedTensorKoszulSymmetry _ ((S A f).obj M) (omega A f)).hom ≫
      inverseOnDomain (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) ≫
          epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom) = _
  rw [← Category.assoc, hcancel]
  simp only [inverseOnDomain, dif_pos (inferInstance : IsIso (((ProEtale.projectionMap (ModuleCat.{u
      + 1} A) f).app (omega A f)).app M)), Category.assoc]
  simp only [Functor.mapIso_hom, Iso.app_hom, tensorIso_hom,
    Iso.symm_hom, Iso.refl_hom, Iso.app_inv] at hi
  have htailTensor :
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            (Etale.dualizingComplex A f))).hom.app J ≫
        (((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
            ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ⊗ₘ 𝟙 (((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)) ≫ (tensorIso ((F A f).mapIso
            (standingUnitComparison A f)) e).hom ≫
        epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
          ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
    rw [tensorHom_id]
    exact htail
  have hcalc := projection_tail_calculation
    ((F A f).map (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom) ((F A
        f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom (inv
        (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M)) (inv
        (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X).mapDerivedCategory).obj (Etale.dualizingComplex A f))).app
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J)))
        (tensorIso ((F A f).mapIso (standingUnitComparison A f)) e).hom
    (epsilon A f (𝟙_ _) ▷ M) (λ_ M).hom
    ((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app ⟨_,
        hQ⟩).hom (inv (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
        Y).mapDerivedCategory).map (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
        (Etale.dualizingComplex A f)).app J)))
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
          (Etale.dualizingComplex A f))).hom.app J)
    (((ProEtale.fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
        ⟨(Etale.dualizingComplex A f), hΩplus⟩).inv ⊗ₘ 𝟙 (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) Y).mapDerivedCategory).obj J))
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map
        ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app
      (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom) hn' hi htailTensor
  change (F A f).map (ProEtale.comparisonOpenTensorIso A f (Etale.dualizingComplex A f) J).hom ≫ ((F
      A f).mapIso (tensorIso (standingUnitComparison A f) ((S A f).mapIso e))).hom ≫ inv
      (((ProEtale.projectionMap (ModuleCat.{u + 1} A) f).app (omega A f)).app M) ≫
    epsilon A f (𝟙_ _) ▷ M ≫ (λ_ M).hom = _
  rw [hcalc]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc]
  rfl

private theorem comparison_square_replace
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (B B' : F ≅ G) (hB : B = B') (Q Ω : C) {P T U V : D}
    (p : P ⟶ G.obj Q) (i : F.obj Q ⟶ T) (t : P ⟶ U)
    (δ : (G.obj Ω ⟶ F.obj Ω) → (U ⟶ V)) (q : V ⟶ T)
    (h : p ≫ B'.inv.app Q ≫ i = t ≫ δ (B'.inv.app Ω) ≫ q) :
    p ≫ B.inv.app Q ≫ i = t ≫ δ (B.inv.app Ω) ≫ q := by
  cases hB
  exact h

private theorem tensorTranspose_comparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient)]
    (hf : f ≫ aY = aX)
    (J : Etale.DerivedCategoryModule P.Coefficient Y) (M : D P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M)
    (hJ : finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y J) :
    (F P.Coefficient f).map (etaleMateSource P.Coefficient f J M e).hom ≫
      genericTensorTranspose (ModuleCat.{u + 1} P.Coefficient) f
        (omega P.Coefficient f) M (epsilon P.Coefficient f (𝟙_ _)) =
    (ProEtale.fixedCompactSupportComparisonIso P.Coefficient
      (HasCompactification.compactification f)).hom.app
      ⟨_, ProEtale.finiteSiteProjectionInput_plus P f
        (Etale.dualizingComplex P.Coefficient f) J
        (dualizing_boundedConstructible P aY f) hJ⟩ ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map
        (inv (((Etale.projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
          (Etale.dualizingComplex P.Coefficient f)).app J) ≫
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).counit.app
            (𝟙_ _) ▷ J ≫ (λ_ J).hom) ≫ e.hom := by
  let Ω := Etale.dualizingComplex P.Coefficient f
  let hΩ := dualizing_boundedConstructible P aY f
  let hΩplus := ProEtale.finiteSiteProjectionInput_plus_source P X Ω hΩ
  let hQ := ProEtale.finiteSiteProjectionInput_plus P f Ω J hΩ hJ
  have hp := ProEtale.finiteSiteProjections_isIso P aX aY f hf
    (HasCompactification.compactification f) Ω J hΩ hJ
  let : IsIso (((Etale.projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app Ω).app J) := hp.1
  let : IsIso (((ProEtale.projectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
        Ω)).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J))
          := hp.2
  have hs := ProEtale.finiteSiteCounitProjectionTransport P aX aY f hf
    (HasCompactification.compactification f) Ω J hΩ hJ
  have hs' := comparison_square_replace
    (ProEtale.fixedCompactSupportComparisonIso P.Coefficient
      (HasCompactification.compactification f))
    (ProEtale.compactSupportSiteComparison P.Coefficient
      (HasCompactification.compactification f))
    (ProEtale.compactSupportComparisonNormalization P.Coefficient
      (HasCompactification.compactification f))
    ⟨_, hQ⟩ ⟨Ω, hΩplus⟩ _ _ _
    (fun z ↦ ((ProEtale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map z).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J))
    _ hs
  exact tensorTranspose_of_projection_square P.Coefficient f J M e hΩplus hQ hs'

private theorem etaleTheta_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (J : Etale.DerivedCategoryModule A Y) :
    (Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ J
      (inv (((Etale.projectionMap (ModuleCat.{u + 1} A) f).app
        (Etale.dualizingComplex A f)).app J) ≫
        (Etale.rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _) ▷ J ≫
          (λ_ J).hom) = Etale.dualizingComplexTensorMap A f J := by
  start_mate_proof
  · simp only [Etale.dualizingComplexTensorMap,
      Etale.lowerShriekRightAdjointUnitTensorMap, Etale.lowerShriekRightAdjointTensorMap,
      Adjunction.projectionTensorMap]
    erw [← Adjunction.homEquiv_naturality_right]
    simp only [Category.assoc]
    rfl
  · finish_mate_proof

private theorem standingTheta_comparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient)]
    (hf : f ≫ aY = aX)
    (J : Etale.DerivedCategoryModule P.Coefficient Y) (M : D P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M)
    (hJ : finiteTorConstructibleEtale P.coefficients.l P.extension
      P.level P.level_pos Y J) :
    (etaleMateSource P.Coefficient f J M e).hom ≫ theta P.Coefficient f M =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        (Etale.dualizingComplexTensorMap P.Coefficient f J) ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek P.Coefficient f).map
          ((ProEtale.derivedComparisonAdjunction
            (ModuleCat.{u + 1} P.Coefficient) Y).unit.app J ≫
            (ProEtale.comparisonLowerStar
              (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map e.hom)) := by
  start_mate_proof
  · let A := P.Coefficient
    let Ω := Etale.dualizingComplex A f
    let Q := Ω ⊗ (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj J
    let hQ := ProEtale.finiteSiteProjectionInput_plus P f Ω J
      (dualizing_boundedConstructible P aY f) hJ
    let hJplus := ProEtale.finiteSiteProjectionInput_plus_source P Y J hJ.1
    have hM : _root_.DerivedCategory.TStructure.t.plus M :=
      (show ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y M from
        ⟨J, hJplus, ⟨e⟩⟩).plus
    let hVQ : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj Q) :=
      ⟨Q, hQ, ⟨Iso.refl _⟩⟩
    let hW : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
        ((S A f).obj M ⊗ omega A f) := ⟨Q, hQ, ⟨etaleMateSource A f J M e⟩⟩
    have hn := standingHom_left A f hVQ hW hM
      (etaleMateSource A f J M e).hom
      (genericTensorTranspose (ModuleCat.{u + 1} A) f (omega A f) M
        (epsilon A f (𝟙_ _)))
    erw [tensorTranspose_comparison P aX aY f hf J M e hJ,
      standingHom_comparison A f Q hQ J M e hM, etaleTheta_mate] at hn
    symm
    convert hn using 1
    unfold theta genericTheta
    simp only [epsilon, dif_pos hM, dif_pos (show
      _root_.DerivedCategory.TStructure.t.plus (𝟙_ (D A Y)) from proUnitPlus A Y)]
    erw [dif_pos hW]
    rfl
  · finish_mate_proof

private theorem etaleCtfPresentation (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (M : D P.Coefficient Y)
    (hM : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) Y M) :
    ∃ J : Etale.DerivedCategoryModule P.Coefficient Y,
      finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos Y J ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅ M) := by
  obtain ⟨⟨J, hJ, ⟨e⟩⟩, a, b, ht⟩ := hM
  have hJ' : Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y J := by
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hJ.2 i), ?_⟩
    obtain ⟨r, hr⟩ := hJ.1.1
    obtain ⟨s, hs⟩ := hJ.1.2
    refine ⟨min r s, max r s, min_le_max, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff J r).mp hr i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff J s).mp hs i
        (lt_of_le_of_lt (le_max_right _ _) hi)
  have htor : Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} P.Coefficient) Y a b J :=
    (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b J).1
      ((ProEtale.DerivedCategory.torAmplitudeIn _ Y a b).prop_of_iso e.symm ht)
  exact ⟨J, ⟨hJ', min a b, max a b, min_le_max,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (htor.mono (min_le_left _ _) (le_max_right _ _))⟩, ⟨e⟩⟩

private theorem standingTheta_isIso (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [CompactSpace Y]
    [ProEtale.UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient)]
    (d : ℕ) [SmoothOfRelativeDimension d f] (M : D P.Coefficient Y)
    (hM : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) Y M) : IsIso (theta P.Coefficient f M) := by
  classical
  obtain ⟨J, hJ, ⟨e⟩⟩ := etaleCtfPresentation P Y M hM
  have ht := (ProEtale.isCohomologicallySmooth_of_smooth P f d).1.2.1 J
    ((ProEtale.DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso e.symm hM)
  let V := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  have hJplus : _root_.DerivedCategory.TStructure.t.plus J := by
    obtain ⟨a, b, _, hv⟩ := hJ.1.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff J a).mpr fun i hi ↦ hv i (.inl hi)⟩
  have hunit : IsIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} P.Coefficient) Y).unit.app J) :=
    ProEtale.isIso_derivedComparisonAdjunction_unit_app _ Y J hJplus
  have heq := standingTheta_comparison P (X ↘ Spec (.of P.field.k))
    (Y ↘ Spec (.of P.field.k)) f (CategoryTheory.comp_over f _) J M e hJ
  apply (isIso_comp_left_iff (etaleMateSource P.Coefficient f J M e).hom _).mp
  rw [heq]
  infer_instance

/-- Composite exceptional adjunction and tensor-map mate identity.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-base-change-and-composition/sk-prop-sp-composition/
thm-pur-composition-coherence.proof.md,
Steps 1--2 (blueprint: lem-pur-composition-tensor-mate).

Proof of the coefficient bridge: use the recorded normalized section-action encoding,
its specified encodingMonoidal tensorator and unit, and encodingDerivedPull. The balanced
pure-tensor description fixes these data and preserves the constructibility and Tor
predicates. Transpose the encoded evaluation by the recorded tensor-Hom adjunction; the
inverse encoding gives its inverse. This proves invertibility of the specific internal-Hom
comparison in Objects, without choosing an isomorphism. Use compactEncoding for the same
proper/open factors. The derived identity-on-sections proper comparison and the open
adjunction mate identify the actual projection components. Transport the normalized
standing finite Hom bijection by that compact-support comparison and the coefficient
adjunction: this is exceptionalHomEquiv, with the Hom equation in Arrow. Apply its inverse
to the identity to obtain nativeEpsilon. The Hom equation gives exactly Arrow.counit.
Apply the same Hom equation to the symmetry/inverse-projection/counit/unit composite;
monoidality and the projection equation give exactly Arrow.theta, with omegaComparison
including the monoidal unit comparison. Finally transpose nativeAlpha followed by the
native counit successively through g and f. The same two Hom equations identify this
nativeC with c, giving the displayed exceptional-composition transport equation. Thus
faithfulness of the encoding transports the following calculation, its unit specialization,
and its common transpose to the native Lambda_T categories.

Proof, following the complete twelve-step DAG split:

1. Apply [lem-sbc-smooth-relative-dimension-permanence](2) to $f,g$: $h=gf$ is smooth of pure
relative dimension $d+e$. Separatedness follows from [lem-weil-pbc-proper-fp-permanence](e), and
finite type from [lem-sfb-finite-type-composition-base-change](1). Thus all three morphisms
satisfy the hypotheses of the finite-coefficient operations and smooth tensor theorem. None of
these assertions requires $X,Y,Z$ to be separated over $k$.

2. The coefficient unit $\Lambda_T$ is a constant finite free rank-one sheaf in degree zero, hence
is bounded constructible with Tor interval $[0,0]$ by [def-weil-finite-tor-amplitude]. Apply
[cor-pur-general-admissibility-datum](2) to each of $f,g,h$: its hypotheses are exactly separated
finite type between finite-type $k$-schemes, so each $Rh^!$ preserves $D^b_{ctf}$. In particular
$\omega_f,\omega_g,\omega_h$ and $Rg^!K$ are in their stated finite-Tor categories. The first
clause of [thm-pur-cohomological-smoothness], applied separately to $f,g,h$, gives invertibility
of the specified $\theta_{a,M}$ for finite-Tor $M$. We do not use that theorem's composition
clause to prove the present identity.

3. By [lem-sf-pullback-tor-amplitude] and [lem-sf-tensor-ctf](ii), $W$, $Lh^*K\otimes^LW$ and
$Lf^*(Lg^*K\otimes^L\omega_g)\otimes^L\omega_f$ are bounded constructible of finite Tor amplitude.
The same applies to the sources formed with $Rg^!K$ and $Rf^!Rg^!K$. Every bounded constructible
source has an etale-origin witness by [lem-sf-proetale-constructible-origin](ii). Its
compact-support image is bounded constructible by [prop-finite-compact-support-constructibility],
and bounded below of etale origin by [thm-sf-comp-composition]. Consequently all successive Hom
bijections in [def-weil-exceptional-inverse-image] apply to the displayed objects, including the
intermediate $Rf_!$-images; no unrestricted ambient pro-etale adjunction is needed.

4. Use the two Hom bijections and [def-weil-pbc-composite-adjunction]. Their composite has counit
$\epsilon^c_M=\varepsilon_{g,M}\circ Rg_!(\varepsilon_{f,Rg^!M})$. By
[pur9-def-upper-shriek-composition], $c_M$ is exactly the transpose of
$\varepsilon_{h,M}\circ\alpha_{R h^!M}$, so $$\epsilon^c_M\circ
Rg_!Rf_!(c_M)=\varepsilon_{h,M}\circ\alpha_{Rh^!M}.$$ The isomorphism $\alpha$ identifies the left
functors. Apply [det-sp-unique-right-adjoint] on the bounded constructible categories (compact
support preserves them by Step 3). It makes this specified, counit-compatible $c$ a natural
isomorphism, rather than an arbitrary comparison of the same objects.

5. Step 2 applies to $M=\omega_g$ and to $M=Rg^!K$ for $f$, as well as to $K$ for $g,h$. Thus
every tensor map in the assertion is an isomorphism. Since $c_\Lambda$ and tensor symmetry are
isomorphisms, their composite $\sigma=c_\Lambda^{-1}\theta_{f,\omega_g}\mathrm{sym}$ is an
isomorphism. This proves the isomorphism assertions without choosing any purity orientation.

6. Write $q=\theta_{f,\omega_g}\mathrm{sym}:W\to Rf^!\omega_g$. Then $c_\Lambda\sigma=q$. Its
transpose through $f$ is exactly
$\mathrm{unitor}\circ(T_f\otimes1)\circ\operatorname{PF}_{f,\omega_f,\omega_g}^{-1}$ by
[def-pur-co-smoothness]; the two source symmetries cancel. Transposing once more through $g$
composes $Rg_!$ of that map with $\varepsilon_{g,\Lambda}=T_g$, by
[def-weil-pbc-composite-adjunction]. This is the displayed map $t$, including its unit constraint.
In particular $\epsilon^c_\Lambda\,Rg_!Rf_!(q)=t$.

7. Put $P_a=Ra_!$, $S_a=La^*$ and $G_a=Ra^!$ for $a=f,g,h$. Use the canonical symmetric monoidal
derived tensors of [lem-sf-ringed-derived-closed-symmetric-monoidal] and the canonical
pullback/tensor comparisons of [def-weil-derived-pullback-tensor-hom]; their pullback compositor
is [lem-weil-pbc-proetale-derived-pullback-composition]. For $B\in D^b_{ctf}$ on the target of $a$
and $M\in D^b_c$ on its source set
$$\pi^a_{B,M}=\mathrm{sym}\circ\operatorname{PF}_{a,M,B}^{-1}\circ P_a(\mathrm{sym}),$$
where $\operatorname{PF}$ is the specified projection transformation of [def-exchange-projection].
With the compactification and dimension-bound choices of Step 8 and the hypotheses verified in
Step 2 ($\omega_f,\omega_g\in D^b_{ctf}$, and $\theta_{f,B}$, $\theta_{g,B}$ invertible for
finite-Tor $B$), [lem-pur-compact-support-composite-transpose-domains] states that these inverses
exist on every object, arrow and naturality instance occurring in the two expressions
$\theta_{f,G_gK}(S_f\theta_{g,K}\otimes1)$ and $c_K\theta_{h,K}(1\otimes q)$, and that they
satisfy there the unit and coefficient-associativity equations, with the canonical monoidal
pullback comparisons. In particular no separate finite-Tor reflection to etale representatives is
needed here: invertibility on these domains is part of the cited statement. Their naturality is
that of the transformation [def-exchange-projection], restricted to these full domains. Thus these
are projection formulas on the full domains needed by the restricted-domain clause of
[lem-pur-composite-tensor-transpose].

8. The schemes $X,Y,Z$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied over
the Noetherian scheme $\operatorname{Spec}k$, hence quasi-compact and quasi-separated by
[lem-weil-pbc-locally-noetherian-quasi-separated]. By Step 1, $f$, $g$ and $h=gf$ are separated of
finite type, so [thm-nagata-compactification] supplies compactifications of $f$, $g$ and $h$. Each
proper ambient scheme is of finite type over the target ([def-weil-proper-morphism]), hence of
finite type over $k$ by [lem-sfb-finite-type-composition-base-change](1);
[lem-kun-dimension-finite-type] gives it finite Krull dimension, and we choose a nonnegative
integer bound (zero for an empty ambient scheme). These are exactly the choices required by
[lem-pur-compact-support-composite-transpose-domains]; its other hypotheses are the finite
coefficient datum and the Step 2 facts $\omega_f,\omega_g\in D^b_{ctf}$ and invertibility of
$\theta_{f,B},\theta_{g,B}$ for finite-Tor $B$. Its composite-projection clause says that for
$K\in D^b_{ctf}(Z,\Lambda)$ and $M\in D^b_c(X,\Lambda)$, identifying source and target through the
canonical compact-support compositor $\alpha$ of [thm-sf-comp-composition] and the pullback
compositor,
$$\pi^h_{K,M}=\pi^g_{K,P_fM}\circ P_g(\pi^f_{S_gK,M}).$$
Writing $\pi^c_{K,M}=\pi^g_{K,P_fM}\,P_g(\pi^f_{S_gK,M})$ for the composite inverse projection of
$P_gP_f$, this reads
$$(1_K\otimes\alpha_{M})\pi^c_{K,M}=\pi^h_{K,M}\;\alpha_{S_hK\otimes M},$$
with tensor symmetries and the pullback compositor inserted. This identifies the inverse composite
projection with the successive inverses for $f,g$, for the actual compact-support compositor;
since $\alpha$ is the canonical compositor, the identity does not depend on the chosen
compactifications. It is asserted only for finite-Tor $K$ and bounded constructible $M$, which
covers every instance used in Steps 9--11.

9. Apply the restricted-domain clause of [lem-pur-composite-tensor-transpose] to
$S_f,S_g,P_f,P_g,G_f,G_g$ and the projection formulas of Step 7. Step 3 checks every Hom-bijection
domain, including each compact-support image; Steps 7–8 supply the tensor and projection coherence
equations. Its maps $\tau^f_B,\tau^g_B$ are exactly $\theta_{f,B},\theta_{g,B}$ by
[def-pur-co-smoothness]: the coefficient-left convention for $\pi$ simply writes the same counit
transpose using symmetry. Set $V=\omega_g$, $U=S_fV\otimes\omega_f$ and $q'=\theta_{f,V}:U\to
G_fV$. The lemma gives $$\theta_{f,G_gK}(S_f\theta_{g,K}\otimes1)=\tau^c_K(1\otimes q')$$ and
identifies both inverse transposes as $$P_gP_fN\xrightarrow{P_g\pi^f_{S_gK\otimes
V,\omega_f}}P_g((S_gK\otimes V)\otimes P_f\omega_f)\xrightarrow{P_g(1\otimes T_f)}P_g(S_gK\otimes
V)\xrightarrow{\pi^g_{K,V}}K\otimes P_gV\xrightarrow{1\otimes T_g}K,$$ where $N=S_f(S_gK\otimes
V)\otimes\omega_f$ and unitors are understood. Here $\tau^c$ is formed from $G_fG_g\Lambda$ and
the composite counit, not from an independently chosen dualizing comparison.

10. Identify $S_h=S_fS_g$ by the pullback compositor, and put $W_c=G_fG_g\Lambda$. Steps 4 and 8
show directly that $$c_K\theta_{h,K}(1\otimes c_\Lambda^{-1})=\tau^c_K:S_hK\otimes
W_c\longrightarrow G_fG_gK.$$ Indeed transpose the left side through the composite Hom bijection:
Step 4 replaces the final $c_K$ by $\varepsilon_{h,K}\alpha$, naturality of $\alpha$ moves
$1\otimes c_\Lambda^{-1}$ to its source, and Step 8 replaces the projection by $\pi^c$. Naturality
of $\pi^c$ in its source factor then leaves $\varepsilon_{h,\Lambda}\alpha
P_gP_f(c_\Lambda^{-1})=\epsilon^c_\Lambda$, which is precisely the defining transpose of $\tau^c$.
This is an equality by the injectivity of the Hom bijection. Finally
$c_\Lambda\sigma=q'\mathrm{sym}$. Precomposing Step 9 with $r_K$ therefore gives exactly $(*)$,
with the displayed order of all three factors.

11. To identify the more precise transpose in the statement, use the source order $N\cong
S_hK\otimes U$ and define
$$b=(1_V\otimes T_f)\pi^f_{V,\omega_f}:P_fU\longrightarrow V.$$
The coefficient-associativity equation for $\pi^f$ supplied by
[lem-pur-compact-support-composite-transpose-domains], at $(S_gK,V,\omega_f)$, rewrites Step 9's
first two arrows as $P_g(1_{S_gK}\otimes b)P_g\pi^f_{S_gK,U}$. Naturality of $\pi^g$ in its source
factor moves $P_g(b)$ past $\pi^g_{K,-}$, giving
$$(1_K\otimes T_gP_gb)\,\pi^g_{K,P_fU}\,P_g\pi^f_{S_gK,U}=(1_K\otimes T_gP_gb)\pi^c_{K,U}.$$
Through $U\cong W$ the morphism $T_gP_gb$ is $t$ by Step 6. Tensor symmetry and the unit
constraints of [lem-sf-ringed-derived-closed-symmetric-monoidal] change coefficient-left order to
$P_gP_fW\otimes K$ and $t\otimes1_K$. Step 8 says that this $\pi^c$ is precisely the successive
inverse projections specified in the assertion. This proves the claimed common transpose, without
any assertion that compact support preserves finite Tor amplitude.

12. All constituent projections, pullback compositors, tensor constraints and counits are natural.
The defining Hom bijections are natural as well, so Steps 9–11 give the identity and the stated
common transpose naturally in $K$. For $K=\Lambda$ the unit equation reduces the calculation to
Step 6. Identities and relative dimension zero require no change; for empty schemes all source
objects and arrows in the calculation are zero. Thus no positive-dimension, nonemptiness or
absolute separatedness assumption has entered the proof.
-/
theorem composition_tensor_mate (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] :
    Assertion P f g d e := by
  classical
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let : UpperStarPreservesFlat (ModuleCat.{u + 1} P.Coefficient) :=
    upperStarPreservesFlat_moduleCat P.Coefficient
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of P.field.k))
  let := (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  let := (P.finiteComparedCompactification g (Z ↘ Spec (.of P.field.k))).hasCompactification
  let := (P.finiteComparedCompactification (f ≫ g)
    (Z ↘ Spec (.of P.field.k))).hasCompactification
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Y ↘ Spec (.of P.field.k))
      toCompactSpace := inferInstance }
  let : IsNoetherian Z :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Z ↘ Spec (.of P.field.k))
      toCompactSpace := inferInstance }
  let : HasInvertibleExponent P.Coefficient (Spec (.of P.field.k)) :=
    P.finiteComparedInvertibleExponent (𝟙 _)
  let : HasInvertibleExponent P.Coefficient Y :=
    P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  let : HasInvertibleExponent P.Coefficient Z :=
    P.finiteComparedInvertibleExponent (Z ↘ Spec (.of P.field.k))
  let : SmoothOfRelativeDimension (d + e) (f ≫ g) := inferInstance
  have huf := unitCtf P.Coefficient Y
  have hug := unitCtf P.Coefficient Z
  have hwf := omegaCtf P.Coefficient (Y ↘ Spec (.of P.field.k)) f
  have hwg := omegaCtf P.Coefficient (Z ↘ Spec (.of P.field.k)) g
  have hwh := omegaCtf P.Coefficient (Z ↘ Spec (.of P.field.k)) (f ≫ g)
  have htf := tensorClause P.Coefficient f hwf
    (WeilConjectures.PurityFiniteSetting.standingTheta_isIso P f d)
  have htg := tensorClause P.Coefficient g hwg
    (WeilConjectures.PurityFiniteSetting.standingTheta_isIso P g e)
  have hth := tensorClause P.Coefficient (f ≫ g) hwh
    (WeilConjectures.PurityFiniteSetting.standingTheta_isIso P (f ≫ g) (d + e))
  have hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X
      (W P.Coefficient f g) := tensorCtf P.Coefficient X hwf (pullCtf P.Coefficient f hwg)
  have hFf := boundedConstructible_rightDerivedLowerShriek P.Coefficient f
    (X ↘ Spec (.of P.field.k)) (Y ↘ Spec (.of P.field.k))
    (CategoryTheory.comp_over f (Spec (.of P.field.k)))
  have hFg := boundedConstructible_rightDerivedLowerShriek P.Coefficient g
    (Y ↘ Spec (.of P.field.k)) (Z ↘ Spec (.of P.field.k))
    (CategoryTheory.comp_over g (Spec (.of P.field.k)))
  have hGf := fun K hK ↦ boundedConstructible_rightDerivedUpperShriek P.Coefficient
    (Y ↘ Spec (.of P.field.k)) f (L := K) hK
  have hGg := fun K hK ↦ boundedConstructible_rightDerivedUpperShriek P.Coefficient
    (Z ↘ Spec (.of P.field.k)) g (L := K) hK
  have hGgK := fun (K : D P.Coefficient Z)
      (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Z K) =>
    upperShriekCtf P.Coefficient (Z ↘ Spec (.of P.field.k)) g hK
  have hFfW := hFf (W P.Coefficient f g) hW.1
  have hdomains := fun (K : D P.Coefficient Z)
      (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Z K) ↦
    domains P.Coefficient f g hK hwf hwg (hGgK K hK) hFfW
  obtain ⟨hm, hunit, hroute⟩ := compositionTensorRouteTransposes P.Coefficient f g
    huf hug htf htg hth hdomains
  have hinput : ∀ K : D P.Coefficient Z,
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Z K →
      InputClause P.Coefficient f g K := by
    intro K hK
    exact ⟨htf.2 _ (hGgK K hK), hdomains K hK, hroute K hK⟩
  obtain ⟨hbridge, hstanding⟩ := compositionTensorCoefficientBridge P f g hinput
  refine ⟨hbridge, inferInstance, inferInstance, inferInstance, inferInstance,
    hstanding, ?_⟩
  · exact packageAssembly P.Coefficient f g
      (adjunctionClause P.Coefficient f g hFf hGf hFg hGg)
      htf htg hth hug hW hm hunit hinput

private theorem packageAssembly (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (ha : AdjunctionClause A f g)
    (htf : TensorClause A f) (htg : TensorClause A g) (hth : TensorClause A (f ≫ g))
    (hu : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z (unit A Z))
    (hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X (W A f g))
    (hm : MateClause A f g) (hunit : UnitTransposeClause A f g)
    (hinput : ∀ K : D A Z,
      DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Z K →
      InputClause A f g K) : Package A f g := by
  exact ⟨ha, originClause A f, originClause A g, originClause A (f ≫ g),
    htg, hth, htf.1, htf.2 _ htg.1, hW, hm,
    sigmaIso A f g (htf.2 _ htg.1).2.2 (hm.2 _ hu.1).1, hunit, hinput⟩

private theorem sigmaIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (htheta : IsIso (theta A f (omega A g)))
    (hc : IsIso (c A f g (unit A Z))) : SigmaIsoClause A f g := by
  have := inverse_isIso (c A f g (unit A Z))
  unfold SigmaIsoClause genericSigmaIso genericSigma
  infer_instance

private theorem inverse_isIso {C : Type*} [Category C] [HasZeroMorphisms C]
    {U V : C} (a : U ⟶ V) [IsIso a] : IsIso (inverseOnDomain a) := by
  classical
  simp only [inverseOnDomain, dif_pos (inferInstance : IsIso a)]
  infer_instance

private theorem adjunctionClause (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z]
    (hFf : ∀ M : D A X, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X M →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y ((F A f).obj M))
    (hGf : ∀ K : D A Y, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X ((G A f).obj K))
    (hFg : ∀ M : D A Y, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y M →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z ((F A g).obj M))
    (hGg : ∀ K : D A Z, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y ((G A g).obj K)) :
    AdjunctionClause A f g := by
  refine ⟨hFf, hGf, hFg, hGg, fun K ↦ ?_⟩
  rw [Adjunction.comp_counit_app]
  change (F A g).map
    (((restrictedAdjunction A f hFf hGf).counit.app
      (((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y).lift
        ((DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Z).ι ⋙ G A g)
        (fun K ↦ hGg K.obj K.property)).obj K)).hom) ≫
      ((restrictedAdjunction A g hFg hGg).counit.app K).hom = _
  rw [restrictedCounit, restrictedCounit]
  rfl

private theorem restrictedCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (hF : ∀ M : D A X, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X M →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y ((F A f).obj M))
    (hG : ∀ K : D A Y, DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X ((G A f).obj K))
    (K : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} A) Y) :
    ((restrictedAdjunction A f hF hG).counit.app K).hom = epsilon A f K.obj := by
  rw [epsilon_eq A f K.property.plusEtaleOrigin.plus]
  change (rightDerivedUpperShriekHomEquiv f _ _).symm (𝟙 _) = _
  exact rightDerivedUpperShriekHomEquiv_symm_id f K.property.plusEtaleOrigin.plus

private theorem originClause (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : OriginClause A f := by
  intro M hM
  exact ⟨hM.plusEtaleOrigin, hM.plusEtaleOrigin.rightDerivedLowerShriek_obj f⟩

private theorem tensorClause (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (hw : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X (omega A f))
    (ht : ∀ K : D A Y, DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) Y K → IsIso (theta A f K)) : TensorClause A f := by
  exact ⟨hw, fun K hK ↦ tensorInput A f hw hK (ht K hK)⟩

private theorem epsilon_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] {K : D A Y}
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    epsilon A f K = rightDerivedUpperShriekCounit f K hK := by
  classical
  rw [epsilon, dif_pos hK, standingHom_eq, rightDerivedUpperShriekHomEquiv_symm_id]

private theorem standingHom_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    standingExceptionalHomEquiv A f hM hK = rightDerivedUpperShriekHomEquiv f hM hK := by
  apply (Equiv.symm_bijective).injective
  ext a
  let M' := Classical.choose hM
  let hM' := (Classical.choose_spec hM).1
  let e := Classical.choice (Classical.choose_spec hM).2
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let b := (Equiv.ofBijective (fun b ↦ ν.map b)
    (bijective_comparisonUpperStar_mapDerivedCategory_map M' _
      (plus_etaleRightDerivedUpperShriek_obj f hK))).symm (e.hom ≫ a)
  have hb : ν.map b = e.hom ≫ a := by
    exact (Equiv.ofBijective (fun b ↦ ν.map b)
      (bijective_comparisonUpperStar_mapDerivedCategory_map M' _
        (plus_etaleRightDerivedUpperShriek_obj f hK))).apply_symm_apply _
  rw [rightDerivedUpperShriekHomEquiv_symm_apply]
  have ht := rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit f hM' hK b
  change (rightDerivedLowerShriek _ f).map e.inv ≫
    ((fixedCompactSupportComparisonIso A (HasCompactification.compactification f)).app
      ⟨M', hM'⟩).hom ≫
    ((derivedComparisonAdjunction _ Y).homEquiv _ _).symm
      (((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _).symm b) = _
  rw [supportComparison]
  calc
    _ = (rightDerivedLowerShriek _ f).map e.inv ≫
        ((rightDerivedLowerShriek _ f).map (ν.map b) ≫
          rightDerivedUpperShriekCounit f K hK) :=
      congrArg (fun z ↦ (rightDerivedLowerShriek _ f).map e.inv ≫ z) ht.symm
    _ = _ := by
      rw [hb]
      simp only [← Category.assoc, ← Functor.map_comp, e.inv_hom_id, Category.id_comp]

private theorem supportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    fixedCompactSupportComparisonIso A (HasCompactification.compactification f) =
      rightDerivedLowerShriekComparisonIso (ModuleCat.{u + 1} A) f := by
  have hproper : rightDerivedLowerStarComparisonIso (ModuleCat.{u + 1} A)
      (HasCompactification.compactification f).g =
      (fixedDirectImageComparisonIso A (HasCompactification.compactification f).g).symm := by
    apply Iso.ext
    ext M
    simp [rightDerivedLowerStarComparisonIso, fixedDirectImageComparisonIso,
      fixedComparisonDirectImageMatePlus]
  apply Iso.ext
  ext K
  simp [rightDerivedLowerShriekComparisonIso,
    rightDerivedLowerShriekOfCompactificationComparisonIso,
    fixedCompactSupportComparisonIso, hproper]

private theorem domains {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    {K : D Λ Z}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z K)
    (hf : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (omega Λ f))
    (hg : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (omega Λ g))
    (hGK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((G Λ g).obj K))
    (hFW : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((F Λ f).obj (W Λ f g))) :
    genericDomains (ModuleCat.{u + 1} Λ) f g (omega Λ f) (W Λ f g) (omega Λ g)
      (G Λ g) (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X)
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y) K := by
  have hW : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (W Λ f g) :=
    tensorCtf Λ X hf (pullCtf Λ f hg)
  refine ⟨hGK, tensorCtf Λ X (pullCtf Λ (f ≫ g) hK) hW,
    tensorCtf Λ X (pullCtf Λ f (tensorCtf Λ Y (pullCtf Λ g hK) hg)) hf, ?_, ?_, ?_⟩
  · unfold genericR
    infer_instance
  · exact hasProjectionFormula_of_constructibleFiniteTor Λ f hW (pullCtf Λ g hK)
  · exact hasProjectionFormula_of_boundedConstructible Λ g hFW hK

private theorem tensorInput {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] {K : D Λ Y}
    (hw : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (omega Λ f))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K)
    (ht : IsIso (theta Λ f K)) : TensorInputClause Λ f K := by
  exact ⟨tensorCtf Λ X (pullCtf Λ f hK) hw,
    hasProjectionFormula_of_constructibleFiniteTor Λ f hw hK, ht⟩

private theorem upperShriekCtf {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (g : Y ⟶ Z) [HasCompactification g] [QuasiCompact g] [CompactSpace Z]
    [HasInvertibleExponent Λ Z]
    {K : D Λ Z}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y ((G Λ g).obj K) := by
  have : IsNoetherian Z :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian aZ
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace aZ }
  exact constructibleFiniteTor_rightDerivedUpperShriek Λ aZ g hK

private theorem omegaCtf {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [CompactSpace Y] :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (omega Λ f) := by
  have : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian aY
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace aY }
  exact constructibleFiniteTor_rightDerivedUpperShriek Λ aY f (unitCtf Λ Y)

private theorem pullCtf {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((S Λ f).obj K) := by
  exact constructibleFiniteTor_leftDerivedFunctor_upperStar_obj f hK

private theorem unitCtf (T : Scheme.{u}) [IsNoetherian T] :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T
      (𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))) := by
  exact DerivedCategory.constructibleFiniteTor_of_isDualizable Λ
    ⟨inferInstance⟩

private theorem tensorCtf (T : Scheme.{u})
    {K M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T K)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T M) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) T (K ⊗ M) := by
  obtain ⟨⟨K', hK', ⟨a⟩⟩, c, d, hKt⟩ := hK
  obtain ⟨⟨M', hM', ⟨b⟩⟩, e, f, hMt⟩ := hM
  have hKctf : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} Λ) T K' :=
    ⟨hK', c, d, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d K').1
      ((DerivedCategory.torAmplitudeIn _ T c d).prop_of_iso a.symm hKt)⟩
  have hMctf : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} Λ) T M' :=
    ⟨hM', e, f, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff e f M').1
      ((DerivedCategory.torAmplitudeIn _ T e f).prop_of_iso b.symm hMt)⟩
  exact (DerivedCategory.constructibleFiniteTor _ T).prop_of_iso
    (((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) K').app M') ≪≫ tensorIso a b)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_tensor Λ T hKctf hMctf))

end WeilConjectures.PurityFiniteSetting
