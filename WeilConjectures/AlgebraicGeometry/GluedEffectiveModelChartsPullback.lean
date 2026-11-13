/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- Each chart square is cartesian when gluing identifies its inverse image
(Stacks, Tag 0AP4). -/
theorem glued_model_chart_pullbacks
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀)
    (hpreimage : ∀ i, q₀ ⁻¹ᵁ (j i).opensRange = U i) :
    ∀ i, IsPullback (q i) (U i).ι (j i) q₀ := by
  intro i
  have _ := hcart
  have _ := hcover
  have _ := hover
  have : IsOpenImmersion (j i) := hopen i
  exact IsOpenImmersion.isPullback _ _ _ _ (hcomm i).symm
    (by simpa only [Scheme.Opens.opensRange_ι] using hpreimage i)

end CategoryTheory.Over.DescentDatum
