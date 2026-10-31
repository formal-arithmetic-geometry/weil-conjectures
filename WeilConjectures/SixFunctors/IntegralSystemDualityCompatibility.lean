/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites

/-! # Integral duality for the specified system limit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Integral duality for the actual limit of the specified dualizing system.
Source: prop-coef-integral-exceptional-adjoint, paragraph 1; steps 1, 5 and 8 of
lem-coef-integral-dual-exceptional-system
(blueprint: lem-coef-integral-system-duality-compatibility).

Proof: Use the normalized dualizing system and its DualizingSpec to identify its
limit, including all projection adjuncts, with the integral dualizing object.
The actual reconstruction counit is invertible by purNormalizedReconstruction.
Its finite projection adjuncts followed by a.finiteOmega are the prescribed
reductions of that integral dualizing object. Apply integral_verdier_biduality
to this object. Its preservation clause gives constructibility of every dual.
The tensor-Hom structures in the system calculus and in integral Verdier duality
compute the same derived internal Hom: their K-flat/K-injective representative
comparisons preserve evaluation, hence adjunction uniqueness identifies their
transposes. Under reductionEvaluation and fiberHom, beta followed by the actual
counit is exactly the evaluation-defined finite Verdier comparison. These maps
are invertible; isIso_iff_evaluations proves invertibility of the system map.
The Tor-bound clause of integral Verdier, with natural-number bound d.toNat,
gives [-b-2d,-a]; d ≥ 0 identifies its integer coercion with d. The argument
applies to the zero complex and to an empty scheme with dimension bound zero. -/
theorem integralSystemDualityCompatibility
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (SS : CoefficientDerivedSystemCalculus l E (Spec (.of D.k)))
    (a : DualizingOperation (D := D) (hl := hl) W S SS) :
    let ω := (coefficientSequenceLimit l E W).obj a.omega.obj
    let dual := (Functor.curry.obj (coefficientIntegralInternalHom l E W)).flip.obj ω
    (∀ P : sfIntegralConstructibleCategory l E W,
      sfIntegralConstructible l E W (dual.obj (op P.obj))) ∧
    (∀ P : sfIntegralConstructibleCategory l E W,
      IsIso (coefficientBaseChangeHom S.integralClosed S.systemClosed
          S.reduction S.reductionTensor P.obj ω ≫
        (coefficientSequenceInternalHom l E W).map
          (Prod.mkHom (𝟙 _) (S.adjunction.counit.app a.omega.obj)))) ∧
    (∀ (P : sfIntegralConstructibleCategory l E W) (a b d : ℤ),
      a ≤ b → 0 ≤ d → topologicalKrullDim W ≤ (d.toNat : WithBot ℕ∞) →
      (∀ n : ℕ, HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E W n).obj P.obj) a b) →
      ∀ n : ℕ, HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E W n).obj (dual.obj (op P.obj)))
        (-b - 2 * d) (-a)) := by sorry

end WeilConjectures
