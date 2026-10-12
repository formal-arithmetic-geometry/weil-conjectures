/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDescentDataCategory

/-! Auxiliary steps for Stacks Project, Descent, Lemma 0241. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

/-- Pullback of descent data exists for every morphism of schemes.
Source: Stacks Project, Descent, Lemma 023Y (pullback), specialized to a fixed base.
(blueprint: lem-galois-descent-pullback-construction).

Proof: For each datum A, use V' = V ×_X X' with projections q and p. Given f₀,f₁
with equal composites to S and a point z over f₀, compose z with q, apply A's
transport to (f₀r,f₁r), and lift the resulting point together with f₁ to V'.
The two projection equations prove naturality, the identity law and the cocycle law.
For a compatible morphism, use its usual pullback map. Its compatibility follows
by projecting to V and X' and applying the original compatibility equation.
The functor laws follow from those of Over.pullback. The pullback square is the
canonical one, and its first projection gives both IsBaseChange and naturality. -/
theorem descent_pullback_construction
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X) :
    ∃ (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
      (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left),
      (∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
        IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
        Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum) ∧
      ∀ A B (f : A ⟶ B), (F.map f).hom.left ≫ q B = q A ≫ f.hom.left := by
  sorry

end CategoryTheory
