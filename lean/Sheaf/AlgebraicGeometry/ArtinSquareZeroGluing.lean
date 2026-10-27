/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion

/-! # Square-zero gluing for fibred groupoids

Source: Stacks Project, artin.tex, definition-RS-star, remark-strong-effectiveness,
and Tag 0CXU, over Spec Z (blueprint: def-sfb-artin-square-zero-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ArtinCriterion

/-- Square-zero gluing for arbitrary rings, with its universal property on arrows.
The common object over B and its two cartesian arrows specify the isomorphism
between restrictions. A gluing is universal among objects over the ring pullback:
its arrows are exactly the pairs of arrows agreeing on that common restriction.
Thus this is equivalence with the groupoid 2-fibre product, not just gluing of
isomorphism classes. No Artinian, local, or finite type condition is imposed.
Source: Stacks Project, artin.tex, definition-RS-star (RS*)
(blueprint: def-sfb-artin-square-zero-gluing). -/
def SquareZeroGluing (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (A B B' P : CommRingCat.{u}) (f : A ⟶ B) (g : B' ⟶ B)
    (p : P ⟶ A) (q : P ⟶ B'),
    Function.Surjective g.hom → RingHom.ker g.hom ^ 2 = ⊥ →
    IsPullback p q f g →
    ∀ (z : Object F (integerScheme (Spec B)))
      (x : Object F (integerScheme (Spec A)))
      (y : Object F (integerScheme (Spec B')))
      (a : Lift (overMap (Spec.map f)) z x)
      (b : Lift (overMap (Spec.map g)) z y),
      ∃ (t : Object F (integerScheme (Spec P)))
        (c : Lift (overMap (Spec.map p)) x t)
        (d : Lift (overMap (Spec.map q)) y t),
        a.val ≫ c.val = b.val ≫ d.val ∧
        ∀ (t' : Object F (integerScheme (Spec P)))
          (c' : Lift (overMap (Spec.map p)) x t')
          (d' : Lift (overMap (Spec.map q)) y t'),
          a.val ≫ c'.val = b.val ≫ d'.val →
          ∃! e : t ⟶ t', c.val ≫ e.val = c'.val ∧ d.val ≫ e.val = d'.val

end AlgebraicGeometry.ArtinCriterion
