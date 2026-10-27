/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids

/-! # Scheme tests of a presheaf presentation of a representable pullback

Source: Stacks Project, algebraic.tex, Tag 0300,
lemma-base-change-by-space-representable-by-space, comparison of the scheme tests
(blueprint: lem-sfb-representable-pullback-presheaf-scheme-tests).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A presheaf presentation over `Q` of `Q x_G F` inherits the scheme tests of f.
Neither presheaf is assumed to be a sheaf or an algebraic space.

Source: Stacks Project, algebraic.tex, Tag 0300,
lemma-base-change-by-space-representable-by-space, second part of its proof;
Tag 04SY, lemma-map-fibred-setoids-representable-algebraic-spaces
(blueprint: lem-sfb-representable-pullback-presheaf-scheme-tests).

Proof:
1. Fix a scheme T and t : h_T -> Q. Apply hf to the based composite
   discreteModuli h_T -> discreteModuli Q -> G, obtaining an algebraic space
   B and an equivalence from discreteModuli B to h_T x_G F.
2. Base change e along t, using the supplied projection two-isomorphism.
   The resulting equivalence identifies h_T x_Q P with h_T x_G F as fibred
   groupoids. Explicitly, a pair (u,p) with t(u)=a(p) is sent using e(p)
   to a triple (u,x,phi). The Q-coordinate of e(p) is identified with a(p)
   by the supplied two-isomorphism. Conversely, use essential surjectivity
   of e to represent (t(u),x,phi); the same two-isomorphism gives the required
   equation t(u)=a(p). Full faithfulness gives exactly the arrows between
   these representatives, so the constructions are inverse up to unique
   vertical isomorphism and commute with restriction.
3. Combine with the equivalence in step 1. Both ends are discrete fibred
   groupoids, so the equivalence induces bijections of their section sets
   on every scheme. Yoneda identifies the section sets of the first with
   the sections of the presheaf pullback. The bijections commute with
   restriction, hence give an isomorphism pullback t a = B as presheaves.
   This argument works for empty section sets as well as nonempty ones. -/
theorem representable_pullback_presheaf_scheme_tests {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    {P Q : (Over S)ᵒᵖ ⥤ Type u} (g : BasedFunctor (discreteModuli Q) G)
    (a : P ⟶ Q) (e : BasedFunctor (discreteModuli P) (moduliTwoFiberProduct g f))
    (he : e.toFunctor.IsEquivalence)
    (hprojection : Nonempty
      (ModuliTwoIso (e.comp (moduliTwoFiberFst g f)) (discreteModuliMap a))) :
    ∀ (T : Over S) (t : yoneda.obj T ⟶ Q),
      ∃ B : AlgebraicSpace S, Nonempty (Limits.pullback t a ≅ B.obj.obj) := by
  sorry

end CategoryTheory
