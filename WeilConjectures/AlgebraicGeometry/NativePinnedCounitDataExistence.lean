/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativePinnedCounitData
import WeilConjectures.AlgebraicGeometry.NativeCounitDataExistence
import WeilConjectures.AlgebraicGeometry.NativeCounitNormalizationsExistence

/-! Existence of the pinned native scalar and Frobenius counit datum.
Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph
(blueprint: lem-sf-native-weil-scalar-frobenius-counit).
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

/-- The seventeen-step native construction supplies one pinned datum. The finite-stage
mate formula fixes the scalar comparison and its cocycles; the Frobenius square and its
mate fix the exchange, inverse exchange, and invariant counit. These are the exact
components required by `PinnedCounitData`, so all compatibility witnesses refer to the
same `CounitData`. Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final paragraph
(blueprint: lem-sf-native-pinned-counit-data-existence). -/
theorem native_pinned_counit_data_exists
    (P : ConstructibleExceptionalCoefficients.CoefficientConstruction l
      (ULift.{u} (PadicAlgCl l)) D hl
      (f := FrobeniusExchange.fiberMap D f₀))
    [G : LocallyFiniteAdicCompactSupport.NativeGeometry.{u} l] :
    Nonempty (PinnedCounitData l D hl R f₀ c₀ S O P) := by
  obtain ⟨A, ⟨hs⟩⟩ := native_counit_scalar_data_exists l D hl R f₀ c₀ S O P
  obtain ⟨B, h, ⟨hf⟩⟩ :=
    native_counit_frobenius_normalization_exists l D hl R f₀ c₀ S O P A hs
  let hsB : ScalarNormalization l D hl R f₀ c₀ S O P B := {
    stage := hs.stage
    bridge := hs.bridge
    bridge_normalized := hs.bridge_normalized
    change := hs.change
    change_source := hs.change_source
    change_target := hs.change_target
    nativeAlpha := hs.nativeAlpha
    integral := hs.integral
    sections := by simpa only [h] using hs.sections
    shift := by simpa only [h] using hs.shift }
  exact ⟨{ data := B, scalar := hsB, frobenius := hf }⟩

end WeilConjectures.NativeWeilScalar
