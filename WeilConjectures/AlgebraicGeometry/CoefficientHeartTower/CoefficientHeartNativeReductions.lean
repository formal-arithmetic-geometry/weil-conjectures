/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.CoefficientHeartCanonicalReductions
import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.CoefficientHeartPointFreeness

/-! # Native complete reductions and their finite free completed stalk

Source: coefficient-heart proof (1), reductions, completeness and completed fibres.
(blueprint: lem-sfb-coefficient-heart-native-reductions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower

/-- The explicitly constructed scalar quotients of a single native lisse integral module
admit complete reductions with finite locally constant etale origins. Their specified
completed stalk is finite free.
Source: latest blueprint, part-six-operations/sec-reduction-finite-coefficients/
sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/
sk-lem-coefficient-heart.proof.md, proof (1), reductions and completed fibres.
(blueprint: lem-sfb-coefficient-heart-native-reductions)

Proof: identify the pulled-back condensed coefficient ring with the sheaf of continuous
functions using its canonical ring isomorphism, and use the internal/sectionwise module
equivalence, preserving underlying abelian sheaves and scalar multiplication. Use the
already constructed categorical scalar-cokernel diagram, retaining its canonical
transitions and projections. On a free chart these are free over the finite quotient
of the coefficient ring. The finite-local-system comparison descends their underlying module
sheaves to etale sheaves. Descend the A-actions by full faithfulness; their scalar
relations and annihilation descend as well. Quotient universal properties give the
specified native cokernel cones and compatibility of the origins. Completeness of the
coefficient ring and the integral-lisse completeness theorem give the original module
as the limit of this actual quotient system. This is invariant under replacing the
chosen uniformizer by pi, since the generators of the maximal ideal are associates.
At the specified geometric point, point_freeness supplies a native free presentation. Stalk
comparison identifies each finite quotient stalk with a fixed finite power of A/pi^(n+1),
compatibly with reductions. Coefficient completion identifies the actual limit of these
stalks with the same finite power of A. Transport its free and finite module instances.
Return the resulting Reduction together with the completion of the fixed scalar-cokernel
diagram and their equality. The argument includes rank zero. No simultaneous tower, morphism,
fundamental-group action, or completed scalar-extension realization is asserted here. -/
theorem nativeReductionData (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (pi : Padic.coefficientExtensionIntegers l E)
      (_hpi : Ideal.span {pi} = Padic.coefficientExtensionMaximalIdeal l E)
      (V : Scheme.{u}) [IsAffine V] [IsLocallyNoetherian V] [ConnectedSpace V]
      {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
      (M : Modules (Padic.coefficientExtensionIntegers l E) V)
      (_hM : IsLisseCoefficientModule
        (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)) M),
      ∃ R : Reduction (Padic.coefficientExtensionIntegers l E) V pi M,
        (∃ C : (canonicalScalarReductions M pi).Completion, R = C.toReduction) ∧
        Module.Free (Padic.coefficientExtensionIntegers l E)
          (R.fibre (Padic.coefficientExtensionIntegers l E) v) ∧
        Module.Finite (Padic.coefficientExtensionIntegers l E)
          (R.fibre (Padic.coefficientExtensionIntegers l E) v) := by sorry

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
