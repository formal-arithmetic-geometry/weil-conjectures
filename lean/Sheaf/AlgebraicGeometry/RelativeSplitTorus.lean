/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Split tori over arbitrary schemes

Source: Stacks Project, Groupoid Schemes, Example 022U (multiplicative group scheme),
and finite products of that construction.
(blueprint: def-sfb-relative-split-torus).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The rank-r split torus over S, including rank zero. Put A = Γ(S, O_S).
The group algebra A[ℤ^r] has basis e_m with comultiplication e_m ↦ e_m ⊗ e_m,
counit e_m ↦ 1 and antipode e_m ↦ e_{-m}. Take its Hopf spectrum over Spec A
and pull back along the canonical S → Spec A. This is (G_m,S)^r, with its actual
coordinate group law. No affineness or field hypothesis is imposed on S.
Source: Stacks Project, Groupoid Schemes, Example 022U, and finite products.
(blueprint: def-sfb-relative-split-torus). -/
noncomputable def relativeSplitTorus (S : Scheme.{u}) (r : ℕ) : Grp (Over S) :=
  (Over.pullback S.toSpecΓ).mapGrp.obj
    ((hopfSpec Γ(S, ⊤)).obj
      (op (CommHopfAlgCat.of Γ(S, ⊤) (AddMonoidAlgebra Γ(S, ⊤) (Fin r → ℤ)))))

end AlgebraicGeometry
