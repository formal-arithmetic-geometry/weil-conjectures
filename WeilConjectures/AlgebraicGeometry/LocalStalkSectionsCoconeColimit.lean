/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsCanonicalColimit
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero continuity for a cofiltered system of affine open subschemes
(Stacks, Tag 03Q6). -/
theorem affineOpenSections_cocone_isColimit
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
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ν : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν : ∀ j, ν.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (B := p.Etale.obj (D.obj j))
        (pullback.lift (c.π.app j) (𝟙 c.pt) (by
          change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
          rw [Category.id_comp]
          exact hp j))
        (by exact pullback.lift_snd _ _ _)).op) :
    Nonempty (IsColimit (Cocone.mk _ ν)) := by
  obtain ⟨ν₀, hν₀, hcol⟩ := affineOpenSections_exists_canonical_colimit
    D c p hp hc H hH F
  have h_eq : ν = ν₀ := by
    apply NatTrans.ext
    funext j
    exact (hν (unop j)).trans (hν₀ (unop j)).symm
  rw [h_eq]
  exact hcol
