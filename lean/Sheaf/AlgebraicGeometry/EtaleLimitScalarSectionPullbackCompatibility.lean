/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Naturality of scalar inverse-image section maps

Source: Stacks Project, Sites Tags 03CB and 03CC, and Etale Cohomology Tag 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The normalized unit sections commute with the prescribed sheaf transitions.
Source: Stacks Project, Sites Tags 03CB and 03CC, adjunction unit naturality
and composition, used in the degree-zero proof of Etale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-pullback-compatibility).

Proof: Cancel the comparison isomorphisms eG on both sides and substitute hG.
Naturality moves the transition morphism phi across the projection unit.
The unit form of upperStarComp identifies the two successive units with the
unit for their composite, followed by the pullback composition comparison.
Evaluate this equation at Tj j. Naturality of the section restrictions moves
these comparisons across gamma and delta. Both resulting maps from the
iterated pullback to Tlim have the same first projection by the hypotheses;
they have the same second projection by their equations over the base and
cone naturality. Pullback uniqueness identifies them. This gives the stated
commuting square after restoring eG. No limit, compactness, filteredness or
sheaf colimit assertion is used. Empty objects and zero coefficients obey the
same morphism equations. -/
theorem etale_limit_scalar_section_pullback_compatibility
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale)
    :
    let J := {j : I // i₀ ≤ j}
    let Tj := fun j : J ↦
      (MorphismProperty.Over.pullback @Etale ⊤
        (D.map (homOfLE j.property).op)).obj T₀
    let Tlim := (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj T₀
    ∀ (γ : ∀ (j k : J) (a : j ⟶ k),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j) ≅ Tj k)
      (δ : ∀ j : J,
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op j.val))).obj (Tj j) ≅ Tlim),
      (∀ (j k : J) (a : j ⟶ k),
        (γ j k a).hom.left ≫ pullback.fst T₀.hom (D.map (homOfLE k.property).op) =
          pullback.fst (Tj j).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
      (∀ j : J,
        (δ j).hom.left ≫ pullback.fst T₀.hom (c.π.app (op i₀)) =
          pullback.fst (Tj j).hom (c.π.app (op j.val)) ≫
            pullback.fst T₀.hom (D.map (homOfLE j.property).op)) →
    let ρ := fun (j k : J) (a : j ⟶ k) ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (φ (show j.val ⟶ k.val from a)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (D.map (show j.val ⟶ k.val from a).op)).obj (Tj j))) ≫
        (F k.val).obj.map (γ j k a).inv.op
    let ν := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (G.obj j.val).obj.map (δ j).inv.op
    ∀ (j k : J) (a : j ⟶ k),
      ν j ≫ (G.map (show j.val ⟶ k.val from a)).hom.app (op Tlim) =
        ρ j k a ≫ ν k := by sorry

end AlgebraicGeometry.Etale
