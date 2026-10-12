module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
/-- Construction of the canonical restriction transformation in the affine continuity argument.
Source: Stacks Project, Tag 03Q6, degree-zero continuity on affine neighbourhoods.
The transformation is obtained by composing the adjunction unit with restriction along the
pullback lift from each affine stage to the limiting object. Naturality is the functoriality
of restriction and the naturality of the adjunction unit.
(blueprint: affine-open-sections-canonical-transformation) -/
theorem affineOpenSections_exists_canonical_transformation
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ ν₀ : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))),
      (∀ j, ν₀.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
        (H.obj F).obj.map (MorphismProperty.Over.homMk
          (B := p.Etale.obj (D.obj j))
          (pullback.lift (c.π.app j) (𝟙 c.pt) (by
            change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
            rw [Category.id_comp]
            exact hp j))
          (by exact pullback.lift_snd _ _ _)).op) := by
  sorry
