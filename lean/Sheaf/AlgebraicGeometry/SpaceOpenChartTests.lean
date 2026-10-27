/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Open scheme tests and composites with étale charts

Source: Stacks Project, Spaces, Tag 02WK and the discussion following
`definition-immersion`; Schemes, Tag 01L7; Morphisms, Tags 02GP and 02GN
(blueprint: lem-a1-space-open-chart-tests).

The scheme-test hypothesis uses the existing `IsRepresentableWith` interface.
The pullback comparison is characterized by its inverse's two projections, so it is
canonical. The scheme representing its right side has the stated étale projection,
and its map to the original test scheme is the composite of the two scheme maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Open scheme tests imply section injectivity and sheaf monomorphy, and every
representable étale scheme chart remains representable étale after composition.
The final clause applies to every representing square for the open scheme test.
The equations for `e.inv` characterize the canonical comparison uniquely; `d`
represents its right side, and `d.hom ≫ e.inv` represents its left side.

Source: Stacks Project, Spaces, Tag 02WK and discussion following
`definition-immersion`; Schemes, Tag 01L7; Morphisms, Tags 02GP and 02GN
(blueprint: lem-a1-space-open-chart-tests).

Proof:
1. Given two sections over `H` with common image `c`, Yoneda turns them into maps
   from `h_H`. The representing square for the open scheme test turns them into
   sections of its projection `p : U → H`. Open immersions are monomorphisms by
   lem-weil-pbc-open-immersion-monomorphism, so these sections agree. Evaluating
   their maps to `O` at the identity of `H` proves section injectivity.
2. For maps from any sheaf to `O` whose composites with `j` agree, apply step 1 to
   each section on each scheme. Equality of components gives equality of sheaf maps.
3. The open scheme projections are étale by lem-weil-pbc-open-immersion-etale.
   Any other representing square is uniquely isomorphic to the chosen square, so
   its projection is also étale.
4. Fix a representable étale chart `v : h_V → O` and a test `c : h_H → Y`.
   Let `U` represent the open test, with projections `p : U → H` and `r : h_U → O`.
   Apply the scheme-test definition in def-trf-algebraic-space to `v` and `r`.
   It gives a scheme `W` representing `h_V ×_O h_U` with étale map `q : W → U`.
   The canonical comparison sends `(x,t)` to `(x,(t,v(x)))`; its inverse forgets
   the `O` component. Both formulas commute with restriction, and their projections
   characterize them uniquely. Compatible pairs glue componentwise, so these
   presheaf pullbacks are the sheaf pullbacks of
   lem-trf-space-fibre-products-etale-covers.
5. The scheme projection to `H` is `q ≫ p`. It is étale by step 3 and clause (2)
   of lem-weil-pbc-etale-composition-cancellation. Thus `W` represents every test
   of the composite with étale projection, proving its representable étaleness. -/
theorem space_open_chart_tests {S : Scheme.{u}} (O Y : AlgebraicSpace S)
    (j : O ⟶ Y)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom) :
    (∀ H : Over S, Function.Injective (j.hom.hom.app (op H))) ∧
    Mono j.hom ∧
    (∀ (H U : Over S) (c : yoneda.obj H ⟶ Y.obj.obj) (p : U ⟶ H)
      (r : yoneda.obj U ⟶ O.obj.obj),
      IsPullback r (yoneda.map p) j.hom.hom c → Etale p.left) ∧
    ∀ (V : Over S) (v : yoneda.obj V ⟶ O.obj.obj), IsEtale v →
      IsEtale (v ≫ j.hom.hom) ∧
      ∀ (H U : Over S) (c : yoneda.obj H ⟶ Y.obj.obj) (p : U ⟶ H)
        (r : yoneda.obj U ⟶ O.obj.obj),
        IsPullback r (yoneda.map p) j.hom.hom c →
        ∃ e : Limits.pullback (v ≫ j.hom.hom) c ≅ Limits.pullback v r,
          e.inv ≫ Limits.pullback.fst (v ≫ j.hom.hom) c = Limits.pullback.fst v r ∧
          e.inv ≫ Limits.pullback.snd (v ≫ j.hom.hom) c =
            Limits.pullback.snd v r ≫ yoneda.map p ∧
          ∃ (W : Over S) (q : W ⟶ U) (d : yoneda.obj W ≅ Limits.pullback v r),
            d.hom ≫ Limits.pullback.snd v r = yoneda.map q ∧
            Etale q.left ∧ Etale (q ≫ p).left ∧
            (d.hom ≫ e.inv) ≫ Limits.pullback.snd (v ≫ j.hom.hom) c =
              yoneda.map (q ≫ p) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
