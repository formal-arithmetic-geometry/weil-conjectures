/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteModuleEquivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.AlgebraicGeometry.ScalarUnitRestrictionSingle
public import WeilConjectures.SixFunctors.DualizingSupportEvaluation.DualizingSupportEvaluation
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # The exceptional mapping comparison defined by a system trace

Source: prop-coef-integral-dualizing, second paragraph, the projection/evaluation
and exceptional-counit transpose (blueprint: def-coef-system-exceptional-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe a b c d v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.CoefPairingFrame

variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {HA : Aᵒᵖ × A ⥤ A} {HC : Cᵒᵖ × C ⥤ C}
  (SA : WeilConjectures.CoefficientClosedStructure HA)
  (SC : WeilConjectures.CoefficientClosedStructure HC)
  {TB : B × B ⥤ B} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame SA.tensor TB SC.tensor TD J P R RX)

/-- Projection and evaluation before applying base sections. This retains the base
quotient scalars, so a trace into the base unit can be transposed there.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-exceptional-transpose). -/
def basePairing (M Q : A) :
    SC.tensor.obj (F.sstar.obj (RX.obj (HA.obj (op M, Q))), P.obj (J.obj M)) ⟶
      P.obj (J.obj Q) :=
  leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor
      (F.sstar.obj (RX.obj (HA.obj (op M, Q)))) (J.obj M) ≫
    P.map (F.openTensor (F.pstar.obj (F.sstar.obj (RX.obj (HA.obj (op M, Q))))) M).inv ≫
    P.map (J.map
      (SA.tensor.map
          (Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M)) ≫
        SA.evaluation M Q))

/-- The actual exceptional comparison, transposed first over the base quotient ring
and then under base sections. No family of evaluated arrows is lifted.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-exceptional-transpose). -/
def exceptionalMap (Q : A) (U : C) (t : P.obj (J.obj Q) ⟶ U) (M : A) :
    RX.obj (HA.obj (op M, Q)) ⟶ R.obj (HC.obj (op (P.obj (J.obj M)), U)) :=
  F.sectionsAdjunction.homEquiv _ _
    (SC.transpose _ _ _ (basePairing SA SC F M Q ≫ t))

end CategoryTheory.CoefPairingFrame

namespace WeilConjectures
universe u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
