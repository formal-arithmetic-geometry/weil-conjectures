module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Sheaf.GroupTheory.TorsionfreeRationalizationInjective

/-! # Rational homomorphisms of abelian varieties

Source: Milne, Abelian Varieties, I §10 and §14 opening.
(blueprint: def-sfb-abelian-rational-hom)

The factor order is `ℚ ⊗[ℤ] Hom`, canonically exchanged with `Hom ⊗[ℤ] ℚ`.
The additive type tag changes only notation for the pointwise group law.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Integral group-scheme homomorphisms with additive notation for pointwise multiplication.
Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-hom). -/
abbrev abelianHom {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] :=
  Additive (Grp.mk A ⟶ Grp.mk B)

/-- The underlying morphism of schemes over the field.
Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-hom). -/
def abelianHomMap {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    (f : abelianHom A B) : A ⟶ B :=
  (Additive.toMul f).hom.hom

/-- Rational homomorphisms, with the rational tensor factor first.
Source: Milne AV I §14 opening (blueprint: def-sfb-abelian-rational-hom). -/
abbrev abelianRationalHom {k : Type u} [Field k]
    (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B] [IsAbelianVariety B] :=
  ℚ ⊗[ℤ] abelianHom A B

/-- The integral-to-rational map `f ↦ 1 ⊗ f`.
Source: Milne AV I §14 opening (blueprint: def-sfb-abelian-rational-hom). -/
abbrev abelianHomToRational {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsAbelianVariety B]
    (f : abelianHom A B) : abelianRationalHom A B :=
  AddCommGroup.rationalizationMap (abelianHom A B) f

/-- Composition of integral group-scheme homomorphisms, in categorical order.
Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-hom). -/
def abelianHomComp {k : Type u} [Field k]
    {A B C : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [GrpObj C]
    (f : abelianHom A B) (g : abelianHom B C) : abelianHom A C :=
  Additive.ofMul (Additive.toMul f ≫ Additive.toMul g)

/-- The identity group-scheme homomorphism.
Source: Milne AV I §10 (blueprint: def-sfb-abelian-rational-hom). -/
def abelianHomId {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] : abelianHom A A :=
  Additive.ofMul (𝟙 (Grp.mk A))

end AlgebraicGeometry
