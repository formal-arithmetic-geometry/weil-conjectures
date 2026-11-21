/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedIntegralScalarUnitUnderlyingBridge

/-! # Integral normalization of a restricted scalar unit

## References

* [Stacks, Tag 03DA]
* [Stacks, Tag 06YY]
* [Stacks, Tag 07A6]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Multiplication normalization gives the specified integral scalar-unit arrow. -/
theorem normalized_integral_scalar_unit_underlying
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral E)
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)) T)
    (hS : S.functor ⋙ RingStage.inclusion.{u, v} l Ω T (.integral E) =
      RingStage.inclusion.{u, v} l Ω T (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T)
    (hχ : ∀ K : C.{u, v} l Ω T (.integral E),
      HEq (S.realization.inv.app K)
        ((completedScalarComparison l E.carrier E.carrier
          (AlgHom.id (Padic l) E.carrier) T).app K.obj))
    (h : ∀ W : Scheme.{max u v},
      (PurCompactSupport.completedChange l E.carrier E.carrier
        (AlgHom.id (Padic l) E.carrier)).map W = 𝟙 _)
    (e : ScalarIdentity.{u, v} l Ω h T S)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((e.iso.hom.app K).hom)
      (((sfIntegralScalarUnit l E.carrier T 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K)).hom) := by
  have hb := normalized_integral_scalar_unit_underlying_bridge
    l Ω E T S hS hχ h e K
  have hc := (CompletedLineTensor.canonical_restriction l E.carrier E.carrier
    (AlgHom.id (Padic l) E.carrier) E.carrier (AlgHom.id (Padic l) E.carrier)
    T 0 (Fact.out : l.Prime).ne_zero).2.1
    ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K)
  exact hb.trans hc.symm

end WeilConjectures.ConstructibleExceptionalCoefficients
