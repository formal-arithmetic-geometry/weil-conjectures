/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralRepresentingPairData

/-! # Coordinate representing families

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
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
/-- Coordinate reduction of an integral input has the Brown origin, normalization,
and finite Tor amplitude.
Source: blueprint sk-prop-sp-integral-adjunction, first and last Hom bijections;
uniform reduction and normalized reconstruction
(blueprint: lem-pur-coordinate-integral-input).

Proof: apply pur_integral_reduction_uniform_tor to the singleton input after
transport to the completed integral coefficient presentation. Its retained etale
origins and common Tor interval give bounded-below origin and constructible finite
Tor amplitude. The reduction calculus makes its actual reduction normalized.
The exact quotient-coordinate equivalence commutes with all evaluations and
transition adjoints, so transports these statements to the Brown coordinates.
The canonical fixed-coefficient realization has the same sectionwise quotient
maps, hence carries the finite Tor statement to the recorded realization.
All comparisons are the fixed section-normalized maps.
The zero input and empty scheme obey the same argument with interval [0,0]. -/
theorem coordinateIntegralInput
    (p : ℕ) [Fact p.Prime] (hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (W : Scheme.{u}) [W.Over (Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    (R : CoefficientDerivedSystemCalculus l E W)
    (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site W (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P)
    (K : CondensedERealization.Integral l E W) :
    V.Origin ((reduction l E W R).obj K.obj) ∧
      IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
        (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
        V.proEvaluation ((reduction l E W R).obj K.obj) ∧
      (∀ n, FiniteCoefficientAdjoints.ctf
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) W
        ((V.realization n).derived.obj
          ((V.proEvaluation.evaluation n).obj ((reduction l E W R).obj K.obj)))) := by sorry

end WeilConjectures.PurIntegralRepresentingPair
