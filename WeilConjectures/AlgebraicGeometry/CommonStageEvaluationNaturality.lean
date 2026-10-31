/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation

/-! # Naturality of evaluation on permitted common-stage Hom pairs

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, exceptional-adjunction coefficient passage.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- Evaluation is natural covariantly in the second Hom input and dinatural
contravariantly in the first, on the actual common-stage morphisms.

Source: the evaluation clause of the exceptional-adjunction coefficient passage
in prop-functor-package.proof.md, step 5 of the parent node.

Proof: represent both components of g at a common finite field L, enlarged to
contain the coefficient fields of P, Q, their Hom objects and the tensor objects
occurring in the two composites. Use the representative formulas for the common
Hom and tensor functors. PodCommonTransposeNormalization identifies evaluation
there with the inverse rational transpose of the identity, with exactly the
recorded tensor and Hom comparisons. Rational transposition is the localization
of integral transposition. On integral maps, the ordinary derived Hom evaluation
satisfies ev(f tensor identity) = ev(identity tensor a) followed by b for the
pair map (a.op,b): this is the naturality of the derived tensor-Hom adjunction,
transported across the completion-unit tensor comparison. Localization preserves
this equation: expand arbitrary rational arrows into sums of scalar multiples
of integral arrows and use bilinearity. The scalar-extension comparisons are
the transposes of extended evaluation, so they identify this rational equation
at L with the representatives of the displayed composites. Cancel the adjacent
inverse comparisons. The representatives are equal at L, hence their classes
are equal. Enlarging L or changing representatives preserves the same equality
by the tower identities. The argument uses only permitted Hom pairs, and does
not require the first input to be perfect or any arrow to be invertible.
(blueprint: lem-sf-common-stage-evaluation-naturality). -/
theorem commonStageEvaluation_naturality
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)]
    (P Q : (commonStageHomPairs l Ω W).FullSubcategory) (g : P ⟶ Q) :
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom ((commonStageDerivedInternalHom l Ω W).map g) (𝟙 Q.obj.1.unop)) ≫
      (podCommonClosed l Ω W).evaluation Q =
    (commonStageDerivedTensor l Ω W).map
        (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom l Ω W).obj P)) g.hom.1.unop) ≫
      (podCommonClosed l Ω W).evaluation P ≫ g.hom.2 := by sorry

end WeilConjectures
