/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeWeilScalar.NativePinnedCounitData

/-! Existence of the ordinary native counit datum.
Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph.
The first part of the native construction builds the ordinary comparison, its
transported adjunction, and the Frobenius pullback data. (blueprint:
lem-sf-native-counit-data-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeWeilScalar
open AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (R : Family l D)
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
  [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (c₀ : Compactification f₀.left)
variable [I : ExceptionalFieldDescent.IntegralInput l D hl
  (FrobeniusExchange.geometricCompactification D f₀ c₀)]
  [J : ExceptionalFieldDescent.RationalOutput l D hl
    (FrobeniusExchange.geometricCompactification D f₀ c₀)]
  (S : ExceptionalFieldDescent.CommonStageData l D hl
    (FrobeniusExchange.geometricCompactification D f₀ c₀) (PadicAlgCl l))
  (O : ExceptionalFieldDescent.CommonOutput l D hl
    (FrobeniusExchange.geometricCompactification D f₀ c₀) (PadicAlgCl l) S)

/--
The native finite-stage construction supplies the ordinary comparison, the transported
constructible adjunction, and its scalar normalization. Its proof must assemble the finite
proper/open mates, the common-stage adjunction, and the scalar comparison. This is strictly
smaller than also constructing the Frobenius normalization.
Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph.
(blueprint: lem-sf-native-counit-data-existence)
-/
theorem native_counit_scalar_data_exists
    (P : ConstructibleExceptionalCoefficients.CoefficientConstruction l
      (ULift.{u} (PadicAlgCl l)) D hl
      (f := FrobeniusExchange.fiberMap D f₀))
    [G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l] :
    ∃ A : CounitData l D R f₀ c₀ S.leftSystem.functor
      S.rightSystem.functor O.adjunction G,
      Nonempty (ScalarNormalization l D hl R f₀ c₀ S O P A) := by
  sorry

end WeilConjectures.NativeWeilScalar
