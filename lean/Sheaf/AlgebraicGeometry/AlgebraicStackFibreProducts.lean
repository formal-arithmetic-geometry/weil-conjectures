/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Algebraic stacks admit 2-fibre products

Source: Stacks Project, Algebraic Stacks, Tags 04T2 and 04TF
(blueprint: lem-sfb-algebraic-stack-fibre-products).

The product is the existing category of triples, with its actual comma projections.
The universal property is expressed by essential surjectivity on cones and unique
lifting of compatible pairs of 2-isomorphisms. Its comparison isomorphism is fixed
pointwise to be the comparison arrow of each triple.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

open AlgebraicGeometry

namespace CategoryTheory

/-- The triple 2-fibre product is algebraic and has the full 2-categorical universal
property, with the tautological comparison and both canonical projections.
Source: Stacks Project, Algebraic Stacks, Tags 04T2 and 04TF
(blueprint: lem-sfb-algebraic-stack-fibre-products).

Proof:
1. Descend the two components of a triple in A and B; the sheaf of isomorphisms
in C glues their comparison. Arrows glue componentwise, with their compatibility
checked locally. This proves etale descent for the triple category, using
`def-sfb-stable-pointed-moduli-groupoids`.
2. By `lem-sfb-stack-diagonal-space-source-representability`, the isomorphism
sheaves of A, B and C are algebraic spaces. The isomorphism sheaf between two
triples is the fibre product of the A and B isomorphism sheaves over the C
isomorphism sheaf, with maps u ↦ alpha' a(u) and v ↦ b(v) alpha. It is an algebraic
space by `lem-trf-space-fibre-products-etale-covers`; hence the diagonal is representable.
3. Choose smooth surjective scheme atlases U → A and V → B, using
`def-sfb-algebraic-moduli-stack`. The space U ×_C V exists by
`lem-sfb-stack-diagonal-space-source-representability`. Its map to the triple
category is a composite of two base changes of the atlases, hence representable,
smooth and surjective by `lem-sfb-fibred-groupoid-representable-smooth-calculus`.
4. Choose an etale surjective scheme chart W of U ×_C V by
`def-trf-algebraic-space`. The same calculus makes W → A ×_C B a smooth surjective
atlas. No quasi-compactness or finite type is imposed; all charts respect
`def-weil-size-convention`. This proves algebraicity.
5. The comparison at a triple is its third component. Given a cone from H,
assemble its two functors and comparison into a functor to the triple category.
A compatible pair of vertical natural isomorphisms gives a unique natural
isomorphism by pairing its components; projecting recovers the original pair.
These constructions commute with precomposition in H. Thus the hom groupoid
comparison is essentially surjective and fully faithful, proving the universal
property in the full 2-category of algebraic stacks. -/
theorem algebraicStack_twoFiberProduct {S : Scheme.{u}}
    (A : BasedCategory.{v₁, w₁} (Over S)) (B : BasedCategory.{v₂, w₂} (Over S))
    (C : BasedCategory.{v₃, w₃} (Over S))
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C) (a : BasedFunctor A C) (b : BasedFunctor B C) :
    IsAlgebraicModuliStack (moduliTwoFiberProduct a b) ∧
      ∃ κ : (moduliTwoFiberFst a b).comp a ≅ (moduliTwoFiberSnd a b).comp b,
        (∀ z : (moduliTwoFiberProduct a b).obj, κ.hom.toNatTrans.app z = z.obj.hom) ∧
        (∀ (H : BasedCategory.{v₄, w₄} (Over S)), IsAlgebraicModuliStack H →
          ∀ (p : BasedFunctor H A) (q : BasedFunctor H B) (e : p.comp a ≅ q.comp b),
            ∃ (l : BasedFunctor H (moduliTwoFiberProduct a b))
              (α : l.comp (moduliTwoFiberFst a b) ≅ p)
              (β : l.comp (moduliTwoFiberSnd a b) ≅ q),
              ∀ x : H.obj,
                a.map (α.hom.toNatTrans.app x) ≫ e.hom.toNatTrans.app x =
                  κ.hom.toNatTrans.app (l.obj x) ≫ b.map (β.hom.toNatTrans.app x)) ∧
        (∀ (H : BasedCategory.{v₄, w₄} (Over S)), IsAlgebraicModuliStack H →
          ∀ (l m : BasedFunctor H (moduliTwoFiberProduct a b))
            (α : l.comp (moduliTwoFiberFst a b) ≅ m.comp (moduliTwoFiberFst a b))
            (β : l.comp (moduliTwoFiberSnd a b) ≅ m.comp (moduliTwoFiberSnd a b)),
            (∀ x : H.obj,
              a.map (α.hom.toNatTrans.app x) ≫ κ.hom.toNatTrans.app (m.obj x) =
                κ.hom.toNatTrans.app (l.obj x) ≫ b.map (β.hom.toNatTrans.app x)) →
            ∃! θ : l ≅ m,
              BasedCategory.whiskerRight θ.hom (moduliTwoFiberFst a b) = α.hom ∧
                BasedCategory.whiskerRight θ.hom (moduliTwoFiberSnd a b) = β.hom) := by
  sorry

end CategoryTheory
