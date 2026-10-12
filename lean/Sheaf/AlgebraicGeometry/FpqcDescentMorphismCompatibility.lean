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

/-- A descended underlying morphism preserves the original descent data.
Source: Stacks Project, Descent, Lemma 0241, verification after refinement.
(blueprint: lem-galois-fpqc-descent-morphism-compatibility).

Proof: The two sides of the compatibility equation are morphisms over X ×_S X.
Pull back along X' ×_S X' → X ×_S X. By the base-change equations for both data
and the reconstruction equation for α, their pullbacks are equal by β.commutes.
Factor the refinement as the two successive base changes of r. Each is fpqc,
so the injectivity part of Tag 02W0, applied twice, reflects this equality.
Evaluate the resulting equation at arbitrary test points to obtain the stated
transport identity. No existence or uniqueness of α is used in this step. -/
theorem fpqc_descent_morphism_compatibility
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X)
    (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
    (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left)
    (hq : ∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
      IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
      Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum)
    (A B : Over.DescentDataCategory a) (β : F.obj A ⟶ F.obj B)
    (α : A.V ⟶ B.V) (hα : q A ≫ α.left = β.hom.left ≫ q B) :
    ∀ {T : Scheme.{u}} (f₀ f₁ : T ⟶ X) (h : f₀ ≫ a = f₁ ≫ a)
      (z : Over.mk f₀ ⟶ A.V),
      B.datum.transport f₀ f₁ h (z ≫ α) = A.datum.transport f₀ f₁ h z ≫ α := by
  sorry

end CategoryTheory
