/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GoodTruncationNormalization
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerFiniteSiteComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GoodTruncationNormalization
import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerRealization
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated

/-! # Integral representing pairs from supplied exceptional systems

Source: blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction, Hom display
and unit/counit paragraph (blueprint: lem-pur-integral-reconstructed-representing-pair).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (RX : CoefficientDerivedSystemCalculus l E X)
  (RY : CoefficientDerivedSystemCalculus l E Y)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

attribute [local irreducible] supportPresentation PurIntegralSupportComparison.beta
  PurIntegralSupportComparison.normalized finiteCoordinates finiteCounit transpose
  Padic coordinates purCoefficientModel

/-- The representing pairs and trace maps on the dependency's own integralSupport
and alpha. The coordinate presentation is the fixed normalized beta; alpha_transport
pins its compatibility with the actual published reconstruction counit.
Source: blueprint integral Hom display and final unit/counit paragraph
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
structure PublishedFamily
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) where
  coordinate : Family l E (R X) (R Y) S G H D hD
  alpha_transport : ∀ K : CondensedERealization.Integral l E X,
    (reduction l E Y (R Y)).map
        ((supportPresentation l E (R X) S G H D (beta l E S G H D)).hom.app K.obj) ≫
      (coordinates l E Y).functor.map
        ((CompactSupportCondensedRealization.alpha l E c R M).app K) =
    alpha l E (R X) (R Y) S G H D K.obj ≫
      (beta l E S G H D).hom.app
        ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj))
  hom : ∀ (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (K : CondensedERealization.Integral l E X),
    (K ⟶ A.object) ≃ₗ[PbcIntegralRing l E]
      ((CompactSupportCondensedRealization.integralSupport l E c R M).obj K ⟶ L)
  hom_formula : ∀ L A K h,
    (hom L A K h).hom =
      (supportPresentation l E (R X) S G H D (beta l E S G H D)).inv.app K.obj ≫
        (coordinate.pair L A).hom K h
  hom_natural : ∀ L A (K K' : CondensedERealization.Integral l E X)
    (b : K' ⟶ K) (h : K ⟶ A.object),
    hom L A K' (b ≫ h) =
      (CompactSupportCondensedRealization.integralSupport l E c R M).map b ≫ hom L A K h
  trace_reduction : ∀ L A,
    (reduction l E Y (R Y)).map ((hom L A A.object (𝟙 A.object)).hom) =
      (coordinates l E Y).functor.map
          ((CompactSupportCondensedRealization.alpha l E c R M).app A.object) ≫
        (beta l E S G H D).inv.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj A.object.obj)) ≫
        D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system) ≫
        D.compact.functor.map (coordinate.pair L A).theta.hom ≫
        D.counit _ (coordinate.pair L A).origin (coordinate.pair L A).normalized
          (coordinate.pair L A).finiteTor (coordinate.pair L A).lowerBound
  trace_evaluation : ∀ L A (n : ℕ),
    (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
      ((reduction l E Y (R Y)).map ((hom L A A.object (𝟙 A.object)).hom))) =
    (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
      ((coordinates l E Y).functor.map
          ((CompactSupportCondensedRealization.alpha l E c R M).app A.object) ≫
        (beta l E S G H D).inv.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj A.object.obj)) ≫
        D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system))) ≫
      (D.compactEvaluation n).hom.app A.system ≫
      (FiniteCoefficientAdjoints.lower
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) c).map
        ((D.siteX.realization n).derived.map (A.phi n).hom ≫
          (finiteCoordinates l E S G H D hD n).hom.app
            ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y (R Y)).obj L.obj))) ≫
      finiteCounit l E S G H D n ((reduction l E Y (R Y)).obj L.obj)
        ((coordinate.pair L A).finite_etale_bound n)
  input_natural : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (A' : Supplied l E (R X) (R Y) S G H D L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (coordinate.pair L' A').theta.hom = (coordinate.pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y (R Y)).map b.hom) →
    ∀ (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object),
      hom L' A' K (ObjectProperty.homMk (h.hom ≫ (totalLimit l E X).map a)) =
        hom L A K h ≫ b
  trace_natural : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (A' : Supplied l E (R X) (R Y) S G H D L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (coordinate.pair L' A').theta.hom = (coordinate.pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y (R Y)).map b.hom) →
    (CompactSupportCondensedRealization.integralSupport l E c R M).map
        (ObjectProperty.homMk ((totalLimit l E X).map a)) ≫
      hom L' A' A'.object (𝟙 A'.object) = hom L A A.object (𝟙 A.object) ≫ b


end WeilConjectures.PurIntegralRepresentingPair
