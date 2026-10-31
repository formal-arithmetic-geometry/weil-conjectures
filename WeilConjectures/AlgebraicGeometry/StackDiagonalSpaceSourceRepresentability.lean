/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Algebraic-space sources over a fibred groupoid with representable diagonal

Source: Stacks Project, Algebraic Stacks, Tag 045G, implication (1) => (7)
(blueprint: lem-sfb-stack-diagonal-space-source-representability).

The conclusion includes every scheme test and its algebraic-space projection to that
scheme, through `IsRepresentableByAlgebraicSpaces`. No stack or atlas is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Every map from an algebraic space to a category fibred in groupoids with
algebraic-space diagonal is representable by algebraic spaces.
Source: Stacks Project, Algebraic Stacks, Tag 045G, implication (1) => (7)
(blueprint: lem-sfb-stack-diagonal-space-source-representability).

Proof:
1. For scheme maps x : U → F and y : V → F, set W = U ×_S V using
   def-pc-fibre-product. The conventions of def-sfb-stable-pointed-moduli-groupoids
   identify U ×_F V with the base change of the diagonal by (x,y) on W.
   Fibrewise, send (u,v,φ) to (u,v,z=y(v),α=φ,β=1), and send
   (u,v,z,α,β) back to (u,v,β⁻¹α). An arrow r between two latter objects
   satisfies rα=α' and rβ=β', so is uniquely β'β⁻¹, and exists exactly when
   β⁻¹α=(β')⁻¹α'. The first composite is the identity; the second is isomorphic
   to the identity by β⁻¹. These formulas commute with pullback and preserve
   the projections, giving an equivalence over W.
2. The diagonal hypothesis makes this base change an algebraic space. Thus every
   scheme-source map to F is representable, by the definition in
   def-sfb-stable-pointed-moduli-groupoids, without assuming effective descent in F.
3. Given a : A → F and t : T → F, step 2 makes t representable. Apply
   lem-sfb-representable-pullback-over-space (Stacks Tag 0300) to t and the space A.
   It represents A ×_F T by an algebraic space. The projection to T equips it
   with its structure over T. As t was arbitrary, this is representability of a.
   No stack, atlas, smoothness or surjectivity hypothesis has been used. -/
theorem stack_diagonal_space_source_representability {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    (hF : IsFibredInGroupoids F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (A : AlgebraicSpace S) (a : BasedFunctor (discreteModuli A.obj.obj) F) :
    IsRepresentableByAlgebraicSpaces a := by
  sorry

end CategoryTheory
