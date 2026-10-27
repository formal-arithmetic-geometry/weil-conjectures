/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids

/-! # The class presheaf of a representable pullback

Source: Stacks Project, algebraic.tex, Tag 0300,
lemma-base-change-by-space-representable-by-space, first part of the proof;
categories.tex, Tags 0045 and 04SC
(blueprint: lem-sfb-representable-pullback-presheaf-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A representable pullback along a presheaf has a small class presheaf, with an
inverse class equivalence that respects its projection to the original presheaf.
There is no sheaf or algebraicity assertion about `P` or `Q`.

Source: Stacks Project, algebraic.tex, Tag 0300, first part of the proof of
lemma-base-change-by-space-representable-by-space; categories.tex, Tag 0045,
lemma-setoid-fibres, and Tag 04SC, lemma-2-category-fibred-setoids
(blueprint: lem-sfb-representable-pullback-presheaf-presentation).

Proof:
1. Write H = Q x_G F. It is fibred in groupoids: pull back the two entries of
   an object along a base arrow, and lift the comparison isomorphism using the
   strong cartesian properties. The uniqueness clauses give the universal
   property of the paired cartesian arrow.
2. An automorphism in H(T) has identity Q-coordinate. For z in Q(T), test f
   on the composite h_T -> Q -> G. The automorphism is then an automorphism
   in that test fibre product, at the object whose h_T-coordinate is id_T.
   The scheme test is equivalent over the base to an algebraic space, whose
   fibres are discrete. Full faithfulness therefore makes the automorphism
   the identity. Quotients of arrows show that H(T) is a thin groupoid.
3. Take isomorphism classes in every fibre. These class sets are u-small:
   for each z in Q(T), choose a representing algebraic space A_z for the
   preceding scheme test. Its sections at T parametrize the classes whose
   Q-coordinate is z, so the disjoint union of the sets A_z(T), indexed by
   the u-small set Q(T), surjects onto the class set. Shrink that quotient
   to Type u. This argument also covers empty fibres and arbitrary total
   category universes.
4. Restrict a class by choosing a cartesian lift. Any two choices are
   vertically isomorphic, so restriction is well defined. The identity
   and composition comparisons give the strict presheaf laws on classes.
   Projection sends a class to its Q-coordinate and gives a natural map a.
5. The class functor from H to discreteModuli P is essentially surjective.
   An arrow over a base map factors through a cartesian lift; its vertical
   factor exists exactly when the classes agree and is unique by step 2.
   Thus the class functor is fully faithful. Choose its inverse over the
   base using representatives in the exact fibres. This is e. Its counit
   identifies projection with discreteModuliMap a over identity base maps,
   giving the required ModuliTwoIso. -/
theorem representable_pullback_presheaf_presentation {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    (Q : (Over S)ᵒᵖ ⥤ Type u) (g : BasedFunctor (discreteModuli Q) G) :
    ∃ (P : (Over S)ᵒᵖ ⥤ Type u) (a : P ⟶ Q)
      (e : BasedFunctor (discreteModuli P) (moduliTwoFiberProduct g f)),
      e.toFunctor.IsEquivalence ∧
        Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst g f)) (discreteModuliMap a)) := by
  sorry

end CategoryTheory
