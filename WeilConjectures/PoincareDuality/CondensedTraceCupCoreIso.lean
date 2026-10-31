/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex

/-! # Module-level cancellation for condensed Tate lines
Source: the untwisted module cancellation step of `sk-def-trace-cup`.
(blueprint: sk-def-trace-cup-core-isIso)

The displayed module-level cancellation composite is the inverse of the normalized
line pullback tensored with the identity, the tensorator of the strong monoidal
inverse image, inverse image of the evaluation, and the inverse unit comparison.
Once the evaluation is known to be invertible (sk-def-trace-cup-evaluation-isIso),
every factor is an isomorphism, hence so is the composite.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCup
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The normalized module-level cancellation map is invertible.
Source: untwisted cancellation in `sk-def-trace-cup`.
(blueprint: sk-def-trace-cup-core-isIso)
Proof: `e.inv ⊗ 𝟙` is invertible; the inverse image is strong monoidal, so its
tensorator `μ` and unit comparison `ε` are invertible; `F.map v` is invertible
because `v` is. A composite of isomorphisms is an isomorphism. -/
theorem core_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ)
    (e : (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y d) ≅
      c.line ell X d)
    (v : c.line ell Y d ⊗ StrictWeil.tateLine ell c Y (-(d : ℤ)) ⟶ 𝟙_ _)
    (hv : IsIso v) :
    IsIso ((e.inv ⊗ₘ 𝟙 _) ≫
      Functor.LaxMonoidal.μ (CondensedRing.upperStar (c.obj ell) f)
        (c.line ell Y d) (StrictWeil.tateLine ell c Y (-(d : ℤ))) ≫
      (CondensedRing.upperStar (c.obj ell) f).map v ≫
      (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) f)).inv) := by
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCup
