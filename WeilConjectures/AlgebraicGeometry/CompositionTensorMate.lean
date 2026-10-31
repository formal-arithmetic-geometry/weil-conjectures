/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.EtaleOriginDerivedCategory
public import WeilConjectures.AlgebraicGeometry.StandingExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.PurityAffineChartBounds
import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessTheorem
import WeilConjectures.AlgebraicGeometry.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientTensorCtf
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportConstructibility
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
public import WeilConjectures.CategoryTheory.DerivedTensorKoszulSymmetry
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaCoefficientCoherence
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.CompatibleCompactificationTriangle
import WeilConjectures.SixFunctors.CompositionProjectionMate
import WeilConjectures.CategoryTheory.CompositeTensorTranspose

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

/-- The successive inverse projections for f and g, in coefficient-right order.
The initial symmetry and pullback compositor retain the statement's source order.
Source: final paragraph of the statement (blueprint: lem-pur-composition-tensor-mate). -/
def compositePi {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] (K : D Λ Z) :=
  genericCompositePi (ModuleCat.{u + 1} Λ) f g (W Λ f g) K

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

/-- Composite exceptional adjunction and tensor-map mate identity.
Source: main-20261015, sk-prop-sp-composition/thm-pur-composition-coherence.proof.md,
Steps 1--2 (blueprint: lem-pur-composition-tensor-mate).

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

7. Put $P_a=Ra_!$, $S_a=La^*$ and $G_a=Ra^!$. Use the canonical symmetric monoidal derived tensors
of [lem-sf-ringed-derived-closed-symmetric-monoidal] and the strong monoidal pullbacks of
[lem-pur-derived-pullback-tensor-iso]; their pullback compositor is
[lem-weil-pbc-proetale-derived-pullback-composition]. On the bounded constructible source and
finite-Tor coefficient domains set
$$\pi^a_{B,M}=\mathrm{sym}\circ\operatorname{PF}_{a,M,B}^{-1}\circ P_a(\mathrm{sym}).$$ These
inverses exist by [lem-weil-finite-compact-projection-formula]. To apply its pro-etale clause,
take the witnesses from Step 3; [lem-sf-comparison-tor-amplitude](ii) gives exactly the finite Tor
hypothesis for their etale representatives. The unit and coefficient associativity equations for
these very $\pi$ are [lem-pur-projection-formula-coefficient-coherence]; their naturality follows
from the naturality of the specified projection transformations [def-exchange-projection]. Thus
these are projection formulas on the full domains needed by the restricted-domain clause of
[lem-pur-composite-tensor-transpose].

8. The schemes $X,Y,Z$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied over
the Noetherian field spectrum, hence quasi-compact and quasi-separated by
[lem-weil-pbc-locally-noetherian-quasi-separated]. Choose a compactification of $g$ by
[thm-nagata-compactification] and a compatible triangle by
[lem-weil-pbc-compatible-compactification-triangle]. Apply [lem-sf-composition-projection-mate] on
this triangle. Its finite-level identity applies to our specified pro-etale projection maps,
including arbitrary ambient inputs before restricting to Step 3's domains. Inverting its
projection components gives $$(1_K\otimes\alpha_{M})\pi^c_{K,M}=\pi^h_{K,M}\;\alpha_{S_hK\otimes
M},\qquad \pi^c_{K,M}=\pi^g_{K,P_fM}\,P_g(\pi^f_{S_gK,M}),$$ with tensor symmetries and the
pullback compositor inserted. This identifies the inverse composite projection with the successive
inverses for $f,g$, for the actual compact-support compositor. Its independence of the chosen
triangle is part of the cited normalized composition identity.

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
S_hK\otimes U$ and define $$b=(1_V\otimes T_f)\pi^f_{V,\omega_f}:P_fU\longrightarrow V.$$
Coefficient associativity of $\pi^f$ in [lem-pur-projection-formula-coefficient-coherence], at
$(S_gK,V,\omega_f)$, rewrites Step 9's first two arrows as $P_g(1_{S_gK}\otimes
b)P_g\pi^f_{S_gK,U}$. Naturality of $\pi^g$ in its source factor moves $P_g(b)$ past
$\pi^g_{K,-}$, giving $$(1_K\otimes T_gP_gb)\,\pi^g_{K,P_fU}\,P_g\pi^f_{S_gK,U}=(1_K\otimes
T_gP_gb)\pi^c_{K,U}.$$ Through $U\cong W$ the morphism $T_gP_gb$ is $t$ by Step 6. Tensor symmetry
and the unit constraints of [lem-sf-ringed-derived-closed-symmetric-monoidal] change
coefficient-left order to $P_gP_fW\otimes K$ and $t\otimes1_K$. Step 8 says that this $\pi^c$ is
precisely the successive inverse projections specified in the assertion. This proves the claimed
common transpose, without any assertion that compact support preserves finite Tor amplitude.

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
  sorry

end CompositionTensorMate
end AlgebraicGeometry.ProEtale
