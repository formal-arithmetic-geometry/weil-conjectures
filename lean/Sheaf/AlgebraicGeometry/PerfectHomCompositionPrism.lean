/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle

/-! # A prism equation for the fixed derived-pullback composition -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Pasting two three-arrow triangles gives the comparison around a commuting
prism. Source: Stacks Project, Tag 0D5S.

Proof: Apply the fixed composition triangle to `h,f,p` and to `m,d,p`.
Both paths end with the same comparison for `(m ≫ d) ≫ p`; cancel that
comparison, leaving the transport across `h ≫ f = m ≫ d`. -/
theorem compositionTo_prism
    {W X Y T Z : Scheme.{u}}
    (h : W ⟶ X) (f : X ⟶ Y) (p : Y ⟶ Z)
    (m : W ⟶ T) (d : T ⟶ Y)
    (q : X ⟶ Z) (q' : T ⟶ Z) (r : W ⟶ Z)
    (hf : f ≫ p = q) (hd : d ≫ p = q')
    (hh : h ≫ q = r) (hm : m ≫ q' = r)
    (ht : h ≫ f = m ≫ d) (M : schemeDerivedCategory Z) :
    (derivedPullback h).mapIso ((compositionTo f p q hf).app M) ≪≫
        (compositionTo h q r hh).app M =
      ((compositionTo h f (m ≫ d) ht).app ((derivedPullback p).obj M) ≪≫
        ((compositionTo m d (m ≫ d) rfl).app ((derivedPullback p).obj M)).symm) ≪≫
        ((derivedPullback m).mapIso ((compositionTo d p q' hd).app M) ≪≫
          (compositionTo m q' r hm).app M) := by
  have h₁ := compositionTo_triangle h f p q r (m ≫ d) hf hh ht M
  have h₂ := compositionTo_triangle m d p q' r (m ≫ d) hd hm rfl M
  calc
    _ = (compositionTo h f (m ≫ d) ht).app ((derivedPullback p).obj M) ≪≫
        (compositionTo (m ≫ d) p r (by rw [← ht, Category.assoc, hf, hh])).app M := h₁
    _ = ((compositionTo h f (m ≫ d) ht).app ((derivedPullback p).obj M) ≪≫
          ((compositionTo m d (m ≫ d) rfl).app ((derivedPullback p).obj M)).symm) ≪≫
          ((compositionTo m d (m ≫ d) rfl).app ((derivedPullback p).obj M) ≪≫
            (compositionTo (m ≫ d) p r
              (by rw [Category.assoc, hd, hm])).app M) := by
                simp [Iso.trans_assoc]
    _ = _ := by rw [← h₂]

end AlgebraicGeometry
