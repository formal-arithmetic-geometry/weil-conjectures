/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Limits in total categories fibred in groupoids

Source: Stacks Project, stacks-sheaves.tex, Tags 06WY, lemma-fibre-products (1), (3),
and 06WZ, lemma-fibre-products-morphism (1), (2)
(blueprint: lem-sfb-fibred-limit-calculus).

These are ordinary limits in the total categories, with no restriction on the
base maps of the parallel arrows. The functor commutes with the base projections.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

namespace CategoryTheory

open Limits

/-- Pullbacks exist and are preserved by functors over the scheme base; algebraic
stacks have total-category equalizers, and faithful such functors preserve equalizers.

Source: Stacks Project, stacks-sheaves.tex, Tags 06WY (1), (3), and 06WZ (1), (2)
(blueprint: lem-sfb-fibred-limit-calculus).

Proof:
1. Given arrows x → y ← z, form the pullback of their base schemes over S by
   def-pc-fibre-product. Lift its projection to the base of z to an arrow w → z,
   using def-sfb-stable-pointed-moduli-groupoids. Every arrow is strongly cartesian.
   Apply lem-sfb-cartesian-lift-pullback-square to construct w → x and obtain the
   universal pullback square in the total category.
2. A based functor preserves the base square. Its image arrows are again strongly
   cartesian, so lem-sfb-cartesian-lift-pullback-square gives the image pullback.
   Uniqueness identifies the upper image arrow with the constructed one. Every
   other pullback is uniquely isomorphic to this one by its universal property;
   the functor preserves this comparison isomorphism, hence preserves all pullbacks.
3. If C is algebraic, lem-sfb-algebraic-stack-total-equalizers gives equalizers of
   every pair of parallel arrows, including ones with different base maps, without
   any separatedness assumption on the diagonal.
4. An equalizer arrow e is monic by uniqueness of factorization. The square with
   both projections the identity is therefore a pullback of e with itself. Step 2
   preserves it, proving that F(e) is monic as well.
5. For t : w → F(x) equalizing F(r), F(s), lift its base map to c : x_h → x.
   The strongly cartesian properties of F(c) and t identify w with F(x_h) by
   mutually inverse arrows over the identity. Cancel this isomorphism from the
   equalizing equation and use faithfulness to get c ≫ r = c ≫ s. The source
   equalizer supplies l : x_h → z with l ≫ e = c. Composing its image with the
   comparison isomorphism gives a factorization of t through F(e).
6. Functoriality gives the equalizing equation for F(e); step 5 supplies existence
   of every factorization and monicity from step 4 supplies uniqueness. -/
theorem fibred_limit_calculus
    {S : AlgebraicGeometry.Scheme.{u}}
    (C : BasedCategory.{v₁, w₁} (Over S))
    (D : BasedCategory.{v₂, w₂} (Over S))
    (F : BasedFunctor C D)
    (hC : IsFibredInGroupoids C) (hD : IsFibredInGroupoids D) :
    HasPullbacks C.obj ∧
      PreservesLimitsOfShape WalkingCospan F.toFunctor ∧
      (IsAlgebraicModuliStack C → HasEqualizers C.obj) ∧
      (HasEqualizers C.obj → F.toFunctor.Faithful →
        PreservesLimitsOfShape WalkingParallelPair F.toFunctor) := by
  sorry

end CategoryTheory
