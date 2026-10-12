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

/-- Underlying morphisms of pulled-back descent data descend uniquely over X.
Source: Stacks Project, Descent, Lemma 0241, overlap argument and Lemma 02W0.
(blueprint: lem-galois-fpqc-descent-underlying-morphism).

Proof: Restrict the compatibility equation of β to X' ×_X X'. Both original
transport maps there are identities, since the two maps to X coincide. Thus β
satisfies the canonical overlap equation. Apply fpqc descent of scheme morphisms
over X, Tag 02W0, and identify the chosen cartesian squares with canonical fibre
products. This gives an X-morphism α with the displayed reconstruction equation.
The injectivity part of Tag 02W0 proves uniqueness of α. -/
theorem fpqc_descent_underlying_morphism
    {S X X' : Scheme.{u}} (a : X ⟶ S) (r : X' ⟶ X)
    (hr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage X)
    (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory (r ≫ a))
    (q : ∀ A : Over.DescentDataCategory a, (F.obj A).V.left ⟶ A.V.left)
    (hq : ∀ A, ∃ hq : q A ≫ A.V.hom = (F.obj A).V.hom ≫ r,
      IsPullback (q A) (F.obj A).V.hom A.V.hom r ∧
      Over.DescentDatum.IsBaseChange rfl hq A.datum (F.obj A).datum)
    (A B : Over.DescentDataCategory a) (β : F.obj A ⟶ F.obj B) :
    ∃! α : A.V ⟶ B.V, q A ≫ α.left = β.hom.left ≫ q B := by
  sorry

end CategoryTheory
