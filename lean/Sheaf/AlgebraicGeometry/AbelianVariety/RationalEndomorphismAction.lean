module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Rational endomorphisms and their Tate action

Source: Milne, Abelian Varieties, I section 10, pp. 43--47
(blueprint: def-sfb-rational-abelian-endomorphism-action).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry.IsAbelianVariety

/-- The rational endomorphism space, with the integral endomorphisms bundled as morphisms
of group objects. Its additive group law is the group-scheme law, and its tensor product
is over the integers. Source: Milne, I section 10, p. 43
(blueprint: def-sfb-rational-abelian-endomorphism-action). -/
abbrev RationalEndomorphisms {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A] : Type u :=
  Additive (Grp.mk A ⟶ Grp.mk A) ⊗[ℤ] ℚ

/-- The componentwise Tate action is additive in the integral endomorphism.
Source: Milne, I section 10, pp. 44--45
(blueprint: def-sfb-rational-abelian-endomorphism-action).

Proof: on a geometric point, the sum of two group-scheme homomorphisms is the
pointwise sum. Apply this equality in every coordinate of the inverse limit defining
the integral Tate module, and then extend scalars from the adic integers to the adic field. -/
theorem rationalTateModuleMap_add {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime] (f g : Additive (Grp.mk A ⟶ Grp.mk A)) :
    rationalTateModuleMap (ℓ := ℓ) (f + g).toMul.hom.hom =
      rationalTateModuleMap (ℓ := ℓ) f.toMul.hom.hom +
        rationalTateModuleMap (ℓ := ℓ) g.toMul.hom.hom := by
  sorry

/-- The integral endomorphism action as a linear map over the integers.
Source: Milne, I section 10, pp. 44--45
(blueprint: def-sfb-rational-abelian-endomorphism-action). -/
noncomputable def integralEndomorphismTateAction {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Additive (Grp.mk A ⟶ Grp.mk A) →ₗ[ℤ] Module.End ℚ_[ℓ] (rationalTateModule ℓ A) :=
  (AddMonoidHom.mk' (fun f : Additive (Grp.mk A ⟶ Grp.mk A) ↦
    rationalTateModuleMap (ℓ := ℓ) f.toMul.hom.hom)
    (rationalTateModuleMap_add A ℓ)).toIntLinearMap

/-- The canonical rational extension of the componentwise action: a pure tensor
`f ⊗ q` acts by `q` times the existing Tate action of `f`. Source: Milne, I section 10,
pp. 44--47 (blueprint: def-sfb-rational-abelian-endomorphism-action). -/
noncomputable def rationalEndomorphismTateAction {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    RationalEndomorphisms A →ₗ[ℤ] Module.End ℚ_[ℓ] (rationalTateModule ℓ A) :=
  TensorProduct.lift
    (((LinearMap.lsmul ℚ_[ℓ] (Module.End ℚ_[ℓ] (rationalTateModule ℓ A))).restrictScalars₁₂
      ℤ ℤ).flip.compl₁₂ (integralEndomorphismTateAction A ℓ)
        (algebraMap ℚ ℚ_[ℓ]).toAddMonoidHom.toIntLinearMap)

end AlgebraicGeometry.IsAbelianVariety
