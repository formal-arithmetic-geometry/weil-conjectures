/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import Sheaf.CategoryTheory.SiteStackification
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Effective fppf descent for relative finite Hilbert groupoids

Source: Stacks Project, examples-stacks.tex, Tags 05WB and 05WC
(blueprint: lem-sfb-finite-hilbert-stack-descent).

The finite Hilbert construction is a stack for every morphism between fppf stacks.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory

namespace AlgebraicGeometry.RelativeFiniteHilbert

/-- The relative degree-d finite Hilbert groupoid is an fppf stack: its isomorphism
presheaves are sheaves and every object descent datum is effective. The stack
predicate also includes being fibred in groupoids.
Source: Stacks Project, examples-stacks.tex, Tag 05WB, with the construction of 05WC
(blueprint: lem-sfb-finite-hilbert-stack-descent).

Proof:
1. Use the explicit scheme and object pullbacks of
   def-sfb-relative-finite-hilbert-groupoids. Finite locally free degree is preserved
   by base change (lem-sfb-finite-locally-free-fppf-descent). The cartesian universal
   properties give cartesian lifts and their uniqueness. In each fibre all three
   components of an arrow are invertible, and their inverses satisfy its equation.
2. For compatible local Hilbert isomorphisms, glue the scheme component uniquely
   by lem-sfb-finite-locally-free-fppf-descent and the target component by the
   isomorphism-sheaf condition for Y. Do this after every base change as well.
3. The base-changed covering covers Z by the covering pullback axiom of
   def-weil-pbc-sites-and-cohomology. Glue the source component by the
   isomorphism-sheaf condition for X. The comparison equation holds locally and
   therefore globally by the isomorphism-sheaf condition for Y. This proves unique
   gluing of Hilbert arrows on the whole slice site.
4. For object descent data, forget to the finite covers and descend them using
   lem-sfb-finite-locally-free-fppf-descent. Identify the local covers with the
   pullbacks of the descended Z. All double and triple overlaps are consequently
   the pullbacks of the corresponding base overlaps.
5. Project the cocycle to Y and descend y. Project the remaining cocycle to X on
   the induced fppf cover of Z (def-weil-pbc-sites-and-cohomology) and descend x.
   Write the resulting local identifications as b_i and a_i.
6. Transport each local comparison to the fixed objects by
   F(a_i)⁻¹ α_i (b_i restricted to Z_i). On overlaps the original arrow equation
   F(a_ij) α_i = α_j b_ij and the cocycle identifications make these comparisons
   equal. Glue them using the isomorphism sheaf of Y to obtain α. The triples
   consisting of the cover identifications, b_i and a_i give local Hilbert
   isomorphisms inducing exactly the original descent datum. Thus it is effective.
Only the two stack hypotheses and the fact that F is a functor over the base enter.
-/
theorem isFppfModuliStack_groupoid {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (F : BasedFunctor X Y) (d : ℕ+)
    (hX : IsFppfModuliStack X) (hY : IsFppfModuliStack Y) :
    IsFppfModuliStack (groupoid F d hX hY) := by
  sorry

end AlgebraicGeometry.RelativeFiniteHilbert
