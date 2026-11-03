/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedCoefficientTowers

/-! # Ordinary quotient-transition tensor adjuncts

Source: latest blueprint, sk-lem-sp-tower, reduction-image step, and
sk-prop-sp-integral-towers-reduction, Normalization paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The ordinary tensor adjunct of the specified strict transition.
Source: sk-prop-sp-integral-towers-reduction, Normalization
(blueprint: lem-sp-current-ordinary-transition-adjunct). -/
def ordinaryTransitionAdjunct (D : Model l E T) {m n : ℕ} (h : m ≤ n) :
    SheafOfModules.systemEvaluation (rings l E T) n ⋙
        SheafOfModules.systemTensor D.scalar (rings l E T) h ⟶
      SheafOfModules.systemEvaluation (rings l E T) m :=
  (((SheafOfModules.systemTensorAdj D.scalar (rings l E T) h).whiskerRight
    (Towers l E T)).homEquiv _ _).symm
      (SheafOfModules.strictSystemTransition (rings l E T) h)

/-- On ordinary quotient reduction the actual tensor-transition adjunct is invertible.
Source: latest blueprint, sk-lem-sp-tower.proof.md, paragraph 1, reduction-image
sentence; sk-prop-sp-integral-towers-reduction.proof.md, Normalization;
Stacks 03EK and 06YY (blueprint: lem-sp-current-ordinary-transition-adjunct).

Proof: reconstruct each finite internal scalar extension as the ordinary sheafified
section-ring extension, with the comparison fixed by its adjunction unit. The
ordinaryLevels comparisons identify the levels of ordinaryRed with those tensor
extensions. ReductionTransitions fixes the consecutive transitions on 1 tensor x.
The strict composition law propagates this identity from consecutive transitions
to every m ≤ n; at equal indices use the strict identity law. Equality on these
unit generators determines the transposed linear map by the tensor adjunction.
The resulting map is the associativity isomorphism
(A_n tensor_R P) tensor_{A_n} A_m → A_m tensor_R P, with inverse inserting 1.
Use the generator-preserving section comparison to identify this isomorphism with
the displayed adjunct for D.scalar, whose ordinary adjunction is normalized on
unit tensors. This proves invertibility without flatness or geometric assumptions.
For P=0 and m=n the same formulas give the zero-object isomorphism and unitor. -/
theorem ordinaryTransitionAdjunct_isIso (D : Model l E T)
    (P : AdicCompletion.Modules l E T) (m n : ℕ) (h : m ≤ n) :
    IsIso ((ordinaryTransitionAdjunct l E T D h).app (D.ordinaryRed.obj P)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
