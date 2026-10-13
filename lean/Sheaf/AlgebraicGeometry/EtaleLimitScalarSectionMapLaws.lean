/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Scalar section comparison along an inverse system
Source: Stacks Project, Tags 09YN and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The displayed stage maps form a diagram and the limit maps form a cocone.
Source: Stacks Project, Sites, Tag 09YN, proof of lemma-colimit, and Etale
Cohomology, Tag 09YQ, inverse-image composition comparisons.
(blueprint: lem-weil-pbc-etale-limit-scalar-section-map-laws).

Proof: The first-projection equations and the equations over the base determine
all pullback comparisons uniquely. Pullback uniqueness therefore gives the identity
and composition laws for gamma and the compatibility of gamma with delta.
Transpose the stage maps through the inverse-image adjunction. Naturality of its
unit, the identity and composition assumptions on phi, and the preceding pullback
laws give the identity and composition equations for rho. Transpose the cocone
legs in the same way. The transition formula hG and cocone naturality of L then
give rho followed by mu equal to mu. These calculations use no continuity theorem,
and remain valid on empty objects and for zero sheaves. -/
theorem etale_limit_scalar_section_map_laws
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale) :
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
    let μ := fun j : J ↦
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Tj j)) ≫
        (eG j.val).inv.hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        (L.ι.app j.val).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤
            (c.π.app (op j.val))).obj (Tj j))) ≫
        L.pt.obj.map (δ j).inv.op
    (∀ j : J, ρ j j (𝟙 j) = 𝟙 _) ∧
    (∀ (j k l : J) (a : j ⟶ k) (b : k ⟶ l),
      ρ j l (a ≫ b) = ρ j k a ≫ ρ k l b) ∧
    (∀ (j k : J) (a : j ⟶ k), ρ j k a ≫ μ k = μ j) := by sorry

end AlgebraicGeometry.Etale
