module

public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
public import Sheaf.Paper.RelativeCompactSupportPasting

/-! # Compatibility of the specified and expanded compact-support exchanges

The strict composition exchange and the expanded tower exchange are the same natural
transformation after the canonical associators are inserted.  The equality is isolated so
that evaluation proofs can use the already established finite tower evaluation theorem.
Source: the unit--square--counit mate expansion in Stacks Tag 0F7F
(blueprint: lem-pur-finite-compact-support-evaluation-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.StrictTower
private theorem whiskered_eq_associator_expansion
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
    [Category.{w} C₃] [Category.{w} C₄] [Category.{w} C₅]
    (J : C₀ ⥤ C₁) (R : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (S : C₁ ⥤ C₄) (R' : C₄ ⥤ C₃) (G' : C₀ ⥤ C₅) (J' : C₅ ⥤ C₄)
    (e : R ⋙ G ⟶ S ⋙ R') (b : J ⋙ S ⟶ G' ⋙ J') :
    Functor.whiskerLeft J e ≫ Functor.whiskerRight b R' =
      (Functor.associator J R G).hom ≫ Functor.whiskerLeft J e ≫
        (Functor.associator J S R').inv ≫ Functor.whiskerRight b R' ≫
        (Functor.associator G' J' R').hom := by
  ext M
  simp

variable (B : Type (u + 1)) [CommRing B]

/-- The composition exchange agrees with the expanded relative compact-support exchange.
Source: Stacks Tag 0F7F; the source and target are obtained by inserting the functor
associators into the same proper mate followed by the open beta comparison.
Proof: expand `compositionE`, `exchange`, and `towerH`; naturality of the associators and
identity laws for composition reduce both sides to the same mate--beta composite.
(blueprint: new-finite-compact-support-composition-tower-exchange). -/
theorem compositionE_eq_towerH {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s)
    (sp : IsPullback s c'.g c.g y) :
    compositionE B c c' x y s wi wp si =
      RelativeCompactSupport.towerH B c c' y x s sp si := by
  exact whiskered_eq_associator_expansion
    (J B c.i) (R B c.g) (G B y) (G B s) (R B c'.g) (G B x) (J B c'.i)
    (exchange B s c'.g c.g y wp) (beta B x c'.i c.i s wi si).hom

end AlgebraicGeometry.ProEtale.StrictTower
