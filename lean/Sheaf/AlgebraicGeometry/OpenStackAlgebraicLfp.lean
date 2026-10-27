/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q146
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Open fibred subcategories of algebraic stacks

Source: Stacks Project, algebraic.tex, Tags 05UN and 05UM; stacks-morphisms.tex,
Tags 06Q7 and 06Q3; morphisms.tex, Tags 01TT and 01TR
(blueprint: lem-sfb-open-stack-algebraic-lfp).

The open-fibre hypothesis concerns an arbitrary functor over schemes. Local finite
presentation is expressed by a smooth surjective atlas with locally finitely presented
structural map, exactly as in the node. Neither an atlas nor a fibre representative is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- Open scheme fibres imply algebraicity and preserve local finite presentation.
Source: Stacks Project, algebraic.tex, Tags 05UN and 05UM; stacks-morphisms.tex,
Tags 06Q7 and 06Q3; morphisms.tex, Tags 01TT and 01TR
(blueprint: lem-sfb-open-stack-algebraic-lfp).

Proof:
1. The open scheme representatives make `j` scheme-representable. Since `Y` is an
   etale stack, lem-sfb-representable-fibred-category-stack gives etale descent for `U`.
2. For objects `x,x'` over `T` and an isomorphism between their images, the two associated
   sections of the open fibre over `j(x)` agree by open-immersion monomorphy
   (lem-weil-pbc-open-immersion-monomorphism). The representing equivalence gives a unique
   arrow between the corresponding triples. Its comma equation is exactly the unique lift
   of the given isomorphism. Thus `j` is fully faithful on fibres.
3. The scheme test of the diagonal of `U` is the discrete isomorphism functor:
   `(z,a,b)` maps to `b a⁻¹`, with inverse `β` mapping to `(x,1,β)`. Full faithfulness in
   step 2 identifies it with the corresponding diagonal test of `Y`. This test is an
   algebraic space by def-sfb-algebraic-moduli-stack, so the diagonal of `U` is representable.
4. Pull a smooth surjective atlas `A → Y` back to the open scheme `W` over `A` supplied
   by the hypothesis. The projection `W → U` is smooth and surjective by
   lem-sfb-fibred-groupoid-representable-smooth-calculus, hence an atlas. Steps 1 and 3
   now give algebraicity of `U` by def-sfb-algebraic-moduli-stack.
5. An open immersion is locally of finite presentation: around each point choose an
   affine neighbourhood in its open image. Its inverse image maps isomorphically to
   that neighbourhood, so its ring map has zero generators and relations. The condition
   is vacuous for an empty open (def-weil-open-immersion,
   def-sbc-locally-finite-presentation).
6. If `Y` has an atlas `A` locally of finite presentation over `S`, use that atlas in
   step 4. Step 5 and lem-sbc-locally-finite-presentation-composition show that
   `W → A → S` is locally of finite presentation. Thus `W → U` witnesses the final clause.
-/
theorem openStackAlgebraicLfp {S : Scheme.{u}}
    (U : BasedCategory.{v₁, w₁} (Over S)) (Y : BasedCategory.{v₂, w₂} (Over S))
    (j : BasedFunctor U Y) (hU : IsFibredInGroupoids U)
    (hY : IsAlgebraicModuliStack Y)
    (hOpen : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
      ∃ (W : Over S) (i : W ⟶ T), IsOpenImmersion i.left ∧
        ∃ e : BasedFunctor (discreteModuli (yoneda.obj W)) (moduliTwoFiberProduct t j),
          e.toFunctor.IsEquivalence ∧
            Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t j))
              (discreteModuliMap (yoneda.map i)))) :
    IsAlgebraicModuliStack U ∧
      ((∃ (A : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj A)) Y),
          IsSmoothModuliAtlas Y A a ∧ LocallyOfFinitePresentation A.hom) →
        ∃ (W : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj W)) U),
          IsSmoothModuliAtlas U W a ∧ LocallyOfFinitePresentation W.hom) := by
  sorry

end CategoryTheory
