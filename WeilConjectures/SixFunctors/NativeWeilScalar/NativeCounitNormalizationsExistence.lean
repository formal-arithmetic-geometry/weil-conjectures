/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeWeilScalar.NativePinnedCounitData

/-! Existence of the native scalar and Frobenius normalizations.
Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph.
For a fixed ordinary counit datum, the finite reduction tower and Frobenius square
supply the two normalization witnesses. (blueprint:
lem-sf-native-counit-normalizations-existence)
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
Fix a scalar-normalized ordinary comparison. Paste its finite-stage scalar mates with
the Frobenius square, then restrict the pasted exchange to the constructible categories.
Choose the inverse exchange by inverse reindexing and obtain its mate and counit identities.
This gives a counit datum with the same alpha and a Frobenius normalization. The source and
target equivalences and exchanges may be replaced; only alpha is held fixed. This is strictly
smaller than constructing the scalar comparison: that comparison is already supplied.
Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph.
(blueprint: lem-sf-native-counit-normalizations-existence)
-/
theorem native_counit_frobenius_normalization_exists
    (P : ConstructibleExceptionalCoefficients.CoefficientConstruction l
      (ULift.{u} (PadicAlgCl l)) D hl
      (f := FrobeniusExchange.fiberMap D f₀))
    [G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l]
    (A : CounitData l D R f₀ c₀ S.leftSystem.functor S.rightSystem.functor O.adjunction G)
    (hscalar : ScalarNormalization l D hl R f₀ c₀ S O P A) :
    ∃ B : CounitData l D R f₀ c₀ S.leftSystem.functor
      S.rightSystem.functor O.adjunction G,
      B.alpha = A.alpha ∧ Nonempty (FrobeniusNormalization l D hl R f₀ c₀ S O G B) := by
  sorry

end WeilConjectures.NativeWeilScalar
