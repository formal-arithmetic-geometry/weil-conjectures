/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierCoreEquations
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFiniteCoherence
import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierBidualityDescent
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierEvaluationDescent

/-! # Descent of finite-origin Verdier duality and evaluation

Source: blueprint thm-coef-qbar-verdier, proof steps 1--4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.CoefQbarTensor
  WeilConjectures.CoefQbarPullback

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

omit [IsAlgClosure (Padic l) Ω] in
/-- Simultaneous finite data from rational Verdier duality and finite Hom identification.
Source: blueprint thm-coef-qbar-verdier, proof steps 1 and 5
(blueprint: lem-coef-qbar-verdier-core-descent).

Proof: apply the simultaneous rational duality theorem. Choose integral dualizing
presentations at each finite coefficient field, specialize its duality and scalar
families, and use the finite Hom-identification theorem for each identity field map.
The normalized scalar comparisons themselves supply beta, so betaNormalized is reflexive. -/
theorem finite_data_exists : Nonempty (Finite D l hl Ω X) := by
  exact finiteData_nonempty D l hl Ω X

/-- Biduality already gives a quasi-inverse, without a second Hom calculation. -/
private theorem antiEquivalence {C : Type*} [Category C]
    (V : Cᵒᵖ ⥤ C) (δ : 𝟭 C ≅ V.rightOp ⋙ V) : V.IsEquivalence := by
  let c : V ⋙ V.rightOp ≅ 𝟭 Cᵒᵖ :=
    NatIso.ofComponents (fun K ↦ (δ.app K.unop).op) (by
      intro K M f
      apply Quiver.Hom.unop_inj
      exact (δ.hom.naturality f.unop).symm)
  exact Functor.IsEquivalence.mk' V.rightOp c.symm δ.symm

/-- Coherent finite Verdier functors and their canonical evaluation descend to the
actual common-stage category, with its prescribed coefficient action.
Source: blueprint thm-coef-qbar-verdier, proof steps 1--4
(blueprint: lem-coef-qbar-verdier-core-descent).

Proof: choose coherent integral dualizing presentations and the simultaneous rational
Verdier data. Their normalized unit and tower equations give the finite beta equations.
Reverse representatives to identify the opposite-stage pair category with the opposite
pair category, and apply coherent pair-functor descent. A representative at L maps to
beta composed with the rational dual arrow and inverse beta at its other endpoint.
The tower equation proves independence of extension and representative. The resulting
object is literally the pair at the original stage, so the inclusion comparisons have
identity components. Use intrinsicQbarLinear, whose multiplication by c is computed
after a finite extension containing c and the representative; its finite-representative
formula and tower compatibility give the coefficient normalization. Finite linearity
gives additivity and Omega-linearity. Descend omega using the canonical u comparisons,
and descend evaluation and biduality using
the finite scalar squares. Finite biduality and its inverse are inverse on every
representative. The finite shift comparisons descend, and a distinguished triangle
has a finite-stage representative, proving exactness for the prescribed triangles.
The scalar, evaluation and biduality normalization equations are their finite-stage
squares, transported through the canonical inclusion-transition comparisons. Evaluation
naturality follows at a common stage from finite rational evaluation naturality. -/
theorem core_descent :
    ∃ B : DualityData D l hl Ω X, CoreProperties D l hl Ω X B := by
  obtain ⟨F⟩ := finite_data_exists D l hl Ω X
  have hF := finite_coherent D l hl Ω X F
  obtain ⟨δ, hexact, hlinear, hcoeff, hscalar, hbidual⟩ :=
    descended_duality_exists D l hl Ω X F hF
  have hequiv := antiEquivalence (descendedDual D l hl Ω X F hF) δ
  obtain ⟨homega, hnatural⟩ := descendedEvaluation_equations D l hl Ω X F hF
  let B : DualityData D l hl Ω X := {
    finite := F
    duality := {
      dual := descendedDual D l hl Ω X F hF
      exact := hexact
      equivalence := hequiv
      bidual := δ }
    linearCategory := intrinsicQbarLinear l Ω X
    comparison := descendedComparison D l hl Ω X F hF
    omega := descendedOmega D l hl Ω X F
    omegaComparison := descendedOmegaComparison D l hl Ω X F
    evaluation := descendedEvaluation D l hl Ω X F hF }
  refine ⟨B, ?_⟩
  constructor
  · exact hF
  constructor
  · let := hequiv
    let : (descendedDual D l hl Ω X F hF).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_preserves_initial_object
    exact Functor.additive_of_preserves_binary_products _
  constructor
  · exact hcoeff
  constructor
  · exact hlinear
  constructor
  · exact descendedDual_obj D l hl Ω X F hF
  constructor
  · intro E K
    apply descendedComparison_hom D l hl Ω X F hF E K
  constructor
  · exact hscalar
  constructor
  · exact hbidual
  constructor
  · exact homega
  exact ⟨descendedEvaluation_finite D l hl Ω X F hF, hnatural⟩

end WeilConjectures.CoefQbarVerdier
