/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FdCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.PbcDescentInterfaces

/-! # The coherent inverse of a coefficient comparison

Source: the inverse-comparison calculation in step 2 of
lem-sf-package-common-stage-transport
(blueprint: lem-sf-coefficient-coherent-inverse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The forward comparison is exact, and the inverse finite equivalences form an
exact coherent family, whose inverse
unit is a scalar-compatible isomorphism to the identity family.
Source: blueprint, six-functor package clause (1), inverse-equivalence calculation
in step 2 of lem-sf-package-common-stage-transport
(blueprint: lem-sf-coefficient-coherent-inverse).

Proof: choose HT at E by changing the forward functor of J.stage E.rational to
J.family.Φ E using finite_functor. Give its inverse the adjunction-induced shift;
finite_shift_normalization identifies the forward shift with the recorded one.
First transport rational exactness along finite_functor and finite_shift_normalization
to prove exactness of every J.family.Φ E. The inverse is additive and exact by the
equivalence and inverse_triangles.
For E ≤ L define the inverse scalar comparison as the mate of J.family.β:
its image under HT L is the inverse forward scalar comparison at HT E inverse K,
followed by scalar extension of the counit at E, followed by the inverse counit
at L evaluated at the scalar extension of K.
Full faithfulness gives this map and its inverse uniquely. Apply the faithful
forward functor at the largest stage to the tower equation. Naturality of the
counit cancels the two middle counit factors; the remaining equality is precisely
J.family.coh. The same calculation at repeated stages gives the unit equation.
The adjunction shift compatibility and J.scalar_shift give compatibility with
shifts. Finally set ν E to the inverse unit of HT E. Apply the faithful forward
functor to its scalar square: the defining mate equation and the triangle identity
cancel the counit factors, leaving naturality of the forward scalar comparison.
Its components are invertible because they are inverse-unit components. This
argument uses only equivalences at each fixed stage, never faithfulness of scalar
extension; it also applies when E = L. -/
theorem sfCoefficientCoherentInverse
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ m : ℕ, topologicalKrullDim T ≤ (m : WithBot ℕ∞))]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (J : FdCoefficientComparison l Ω T) :
    (∀ E : Padic.FiniteCoefficientFields l Ω, (J.family.Φ E).IsTriangulated) ∧
    ∃ HT : ∀ E : Padic.FiniteCoefficientFields l Ω,
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ≌ pbcStageCategory l Ω T E,
      (∀ E, (HT E).functor = J.family.Φ E) ∧
      ∃ H : StageSystem.CoherentExactMorphism
          (pbcScalarSystem l Ω T dT.out iT.out)
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T),
        (∀ E, H.base.Φ E = (HT E).inverse) ∧
        ∃ ν : StageSystem.Morphism.Hom (J.family.comp H.base)
            (StageSystem.Morphism.id
              (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)),
          (∀ E, IsIso (ν.τ E)) ∧
          ∀ (E : Padic.FiniteCoefficientFields l Ω)
            (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
            HEq ((ν.τ E).app K) ((HT E).unitIso.inv.app K) := by sorry

end WeilConjectures
