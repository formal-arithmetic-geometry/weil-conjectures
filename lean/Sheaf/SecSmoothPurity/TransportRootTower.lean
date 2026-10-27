/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.TransportRoot

/-! # The finite root tower under inverse image

Source: Bhatt--Scholze, Section 6.8; the canonical root comparison clause of
`sk-thm-purity-transport` in the current blueprint.
(blueprint: lem-pur-transport-normalized-root-tower).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The finite root pullbacks form an isomorphism of the actual integral root diagrams.

Source: Bhatt--Scholze, Section 6.8, finite roots and their power transition maps;
Stacks 03PK, pullback of roots of unity.
(blueprint: lem-pur-transport-normalized-root-tower).

Proof: when ell is invertible the finite root sheaf is represented by the finite
etale group scheme of ell-power roots. Its base change is the same group scheme
over X, and the inverse-image map is its canonical base-change isomorphism.
Conjugate by the generator-normalized root comparisons. The coefficient map is
an isomorphism, and strong monoidal inverse image carries a free module to the
free module on the inverse image. Thus tensoring the coefficient map with the
root map gives the finite module isomorphism. Its underlying map, after the
specified scalar comparison, is exactly rootTensorPull. Pullback of a root
commutes with taking its ell-th power, so these maps commute with every
transition and assemble into a natural isomorphism. Level zero is the zero
module, and on an empty scheme all assertions are the unique maps. -/
theorem normalizedRootTower (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    ∃ e : tateModuleSystem Y ell ⋙
        CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f ≅
      tateModuleSystem X ell,
      ∀ n : ℕ, PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f
        (e.app (Opposite.op n)) (rootTensorPull ell f n) := by sorry

end AlgebraicGeometry.ProEtale.PurityTransport
