/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData
public import Sheaf.Paper.CompletedLineTensorCoherence

/-! # Bridge from a normalized scalar identity to the completed unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- The normalized restricted identity agrees with the completed tensor unit.
Source: exceptional coefficient construction, integral identity clause; Stacks Project,
Tags 03DA, 06YY and 07A6.
(blueprint: lem-sf-normalized-integral-scalar-unit-underlying-bridge)

Proof: use the normalization equation for `e`. The scalar-object equality supplied by
`hS` identifies its source with the completed scalar extension. The inverse realization
hypothesis `hχ` identifies the realization map with the inverse comparison `chi.inv`.
The ordinary K-flat multiplication computation identifies the transported tensor unit
with `CompletedLineTensor.unit`; substituting these equalities into `e.normalized`
gives the displayed heterogeneous equality. -/
theorem normalized_integral_scalar_unit_underlying_bridge
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
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
      ((CompletedLineTensor.unit l E.carrier T K.obj
        (CompletedLineTensor.intrinsic_complete l E.carrier T
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K))).hom) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
