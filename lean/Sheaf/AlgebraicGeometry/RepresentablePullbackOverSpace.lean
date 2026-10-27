/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.RepresentablePullbackPresheafPresentation
import Sheaf.AlgebraicGeometry.RepresentablePullbackPresheafSchemeTests
import Sheaf.AlgebraicGeometry.PresheafSpaceTargetBootstrap

/-! # Algebraic-space base change of a representable morphism of fibred groupoids

Source: Stacks Project, algebraic.tex, Tag 0300,
lemma-base-change-by-space-representable-by-space
(blueprint: lem-sfb-representable-pullback-over-space).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A morphism representable by algebraic spaces has an algebraic-space 2-fibre product
with every algebraic space mapping to its target. The equivalence is over `Sch/S`.

Source: Stacks Project, algebraic.tex, Tag 0300
(blueprint: lem-sfb-representable-pullback-over-space).

Proof:
1. Put H = Z ×_G F using `moduliTwoFiberProduct`. An automorphism of an object
(z, x, phi) gives an automorphism of the corresponding object in the scheme test at
z. Representability makes that test equivalent to a discrete algebraic space, so the
automorphism is trivial. Each fibre of H is therefore a setoid.
2. Form the presheaf P of isomorphism classes of objects of H in each fibre. Cartesian
lifts define its restriction maps, independently of choices. Uniqueness of arrows in
these fibres makes the class functor an equivalence over Sch/S from H to the discrete
fibred groupoid of P. Projection induces the natural transformation P → Z.
3. For every scheme T and t : h_T → Z, identify h_T ×_Z P with the presheaf of
isomorphism classes of h_T ×_G F by sending (a, x, phi) to (a, [(t(a), x, phi)]).
This is a natural bijection, and representability of f makes this test an algebraic space.
4. Apply `lem-sfb-presheaf-space-target-bootstrap` (Stacks Tag 02YS) to P → Z.
It makes P an algebraic space W. The class equivalence from step 2, inverted if
necessary, supplies the asserted equivalence from the discrete groupoid of W to H.
No property of the map Z → G beyond being a morphism is used. -/
theorem representable_pullback_over_space {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (f : BasedFunctor F G) (hf : IsRepresentableByAlgebraicSpaces f)
    (Z : AlgebraicSpace S) (g : BasedFunctor (discreteModuli Z.obj.obj) G) :
    ∃ (W : AlgebraicSpace S)
      (e : BasedFunctor (discreteModuli W.obj.obj) (moduliTwoFiberProduct g f)),
      e.toFunctor.IsEquivalence := by
  obtain ⟨P, a, e, he, hprojection⟩ :=
    representable_pullback_presheaf_presentation hF hG f hf Z.obj.obj g
  have htests := representable_pullback_presheaf_scheme_tests f hf g a e he hprojection
  obtain ⟨hP, hspace⟩ := AlgebraicSpace.presheaf_space_target_bootstrap P Z a htests
  let W : AlgebraicSpace S := ⟨⟨P, hP⟩, hspace⟩
  exact ⟨W, e, he⟩

end CategoryTheory
