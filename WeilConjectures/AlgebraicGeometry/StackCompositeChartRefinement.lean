/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids

/-! # Compatible scheme charts for a composite representable stack map

Source: Stacks Project, algebraic.tex, Tags 0300 and 045B; spaces-morphisms.tex,
Tag 03MJ (blueprint: lem-sfb-stack-composite-chart-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- The charts of a composite admit pointwise étale refinements through charts of
its two factors. This statement contains no morphism property of the horizontal maps.

Source: Stacks Project, algebraic.tex, Tags 0300 and 045B; spaces-morphisms.tex,
Tag 03MJ (blueprint: lem-sfb-stack-composite-chart-refinement).

Proof: Represent the pullback B of g to T by the given ZB. Pull f back over B,
using representability over algebraic spaces (Tag 0300), and call the resulting
space A. Reassociating triples (t,y,x,alpha,beta) by composing alpha with g(beta)
identifies A with the scheme test of the composite. This gives ZA, pA and hA,
with pA the actual projection to T. Given an étale chart U of A and x in U,
choose a surjective étale scheme atlas W of B. The pullback U times_B W is a
space étale and surjective over U. Choose an étale scheme chart of this pullback
and a point above x; call a suitable such chart V and its projection r. The map
W to B gives tW by composition with B to G. For any presentation M of the test
of f on tW, reassociation identifies A times_B W with M. Thus V to M is étale,
being a base change of U to A followed by an étale chart. These constructions
preserve the projections, which gives the displayed equality of scheme maps.
The atlas W is surjective, so every x lifts after passing to the scheme chart V.
For empty U the last assertion is vacuous; no nonemptiness assumption is needed. -/
theorem stack_composite_chart_refinement
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {H : BasedCategory.{v₃, w₃} (Over S)}
    (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (hH : IsFibredInGroupoids H) (f : BasedFunctor F G) (g : BasedFunctor G H)
    (hf : IsRepresentableByAlgebraicSpaces f)
    (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) H)
    (ZB : AlgebraicSpace S) (pB : ZB.obj.obj ⟶ yoneda.obj T)
    (hB : HasSpaceBaseChange g T t ZB pB) :
    ∃ (ZA : AlgebraicSpace S) (pA : ZA.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange (f.comp g) T t ZA pA ∧
        ∀ (U : Over S) (a : yoneda.obj U ⟶ ZA.obj.obj),
          AlgebraicSpace.IsEtale a → ∀ x : U.left,
          ∃ (W : Over S) (c : yoneda.obj W ⟶ ZB.obj.obj),
            AlgebraicSpace.IsEtale c ∧
              ∃ tW : BasedFunctor (discreteModuli (yoneda.obj W)) G,
                ∀ (M : AlgebraicSpace S) (q : M.obj.obj ⟶ yoneda.obj W),
                  HasSpaceBaseChange f W tW M q →
                    ∃ (V : Over S) (r : V ⟶ U) (b : yoneda.obj V ⟶ M.obj.obj)
                      (v : V.left),
                      Etale r.left ∧ AlgebraicSpace.IsEtale b ∧ r.left v = x ∧
                        r ≫ yoneda.preimage (a ≫ pA) =
                          yoneda.preimage (b ≫ q) ≫ yoneda.preimage (c ≫ pB) := by
  sorry

end CategoryTheory
