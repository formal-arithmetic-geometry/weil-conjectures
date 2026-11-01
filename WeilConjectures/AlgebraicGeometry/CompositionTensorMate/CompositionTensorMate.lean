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
