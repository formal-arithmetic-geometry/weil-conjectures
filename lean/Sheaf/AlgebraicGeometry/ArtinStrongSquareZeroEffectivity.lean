/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion

/-! # Strong square-zero effectivity for fibred groupoids

Source: Stacks Project, artin.tex, definition-RS-star, remark-strong-effectiveness,
and Tag 0CXU, over Spec Z (blueprint: def-sfb-artin-strong-square-zero-effectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ArtinCriterion

/-- A compatible system of objects over a countable inverse system of rings.
Index n here is index n+1 in the source. The cartesian arrows specify the
transition isomorphisms, including their identity and composition coherences.
Source: Stacks Project, artin.tex, remark-strong-effectiveness
(blueprint: def-sfb-artin-strong-square-zero-effectivity). -/
structure SquareZeroSystem (F : BasedCategory.{v, w} (Over Base.{u}))
    (D : ℕᵒᵖ ⥤ CommRingCat.{u}) where
  obj : ∀ n : ℕ, Object F (integerScheme (Spec (D.obj (op n))))
  transition : ∀ (n m : ℕ) (h : n ≤ m),
    Lift (overMap (Spec.map (D.map (homOfLE h).op))) (obj n) (obj m)
  identity : ∀ n : ℕ, (transition n n le_rfl).val = 𝟙 (obj n).val
  composition : ∀ (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k),
    (transition n m h).val ≫ (transition m k h').val =
      (transition n k (h.trans h')).val

/-- Every compatible system is induced by an object over the ring inverse limit,
with compatible isomorphisms at all stages. All transition maps, including
nonconsecutive ones, are surjective and have square-zero kernels.
Source: Stacks Project, artin.tex, Tag 0CXU, assumption (4), and
remark-strong-effectiveness
(blueprint: def-sfb-artin-strong-square-zero-effectivity). -/
def StrongSquareZeroEffectivity (F : BasedCategory.{v, w} (Over Base.{u})) : Prop :=
  ∀ (D : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone D), Nonempty (IsLimit c) →
    (∀ (n m : ℕ) (h : n ≤ m),
      Function.Surjective (D.map (homOfLE h).op).hom ∧
        RingHom.ker (D.map (homOfLE h).op).hom ^ 2 = ⊥) →
    ∀ s : SquareZeroSystem F D,
      ∃ (x : Object F (integerScheme (Spec c.pt)))
        (a : ∀ n : ℕ, Lift (overMap (Spec.map (c.π.app (op n)))) (s.obj n) x),
        ∀ (n m : ℕ) (h : n ≤ m),
          (s.transition n m h).val ≫ (a m).val = (a n).val

end AlgebraicGeometry.ArtinCriterion
