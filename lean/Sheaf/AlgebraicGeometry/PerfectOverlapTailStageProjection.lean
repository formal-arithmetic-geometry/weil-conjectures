/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Cartesian projection for a restricted tail -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Raw cartesian projection equation for the canonical tail.
Source: Stacks Project, Tag 08DW. This is the named cartesian projection theorem
with its pinned scheme isomorphism replaced by its defining pasted square.
(blueprint: lem-pc-perfect-overlap-tail-stage-projection). -/
theorem perfectOverlapTailStageProjection
    {X Y S C : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ C)
    (pY : Y ⟶ S) (b : C ⟶ S) (hg : IsPullback g pX pY b)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L) :
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫
        (X.homOfLE (fun _ hx ↦ hWL hx) ≫ (g ∣_ L)) =
      pullback.fst ((U ⊓ V).ι ≫ pY) b ≫ Y.homOfLE hWL := by
  have restricted : X.homOfLE (fun _ hx ↦ hWL hx) ≫ (g ∣_ L) =
      (g ∣_ (U ⊓ V)) ≫ Y.homOfLE hWL := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  rw [restricted, ← Category.assoc,
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback_inv_fst]

end AlgebraicGeometry
