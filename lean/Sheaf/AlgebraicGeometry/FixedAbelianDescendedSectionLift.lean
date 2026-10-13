/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.ColimitSiteSections
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos

/-! # Fixed-coefficient lifting on a descended qcqs étale object

Source: Stacks Project, Sites Tags 09YM and 09YN, and Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-fixed-abelian-descended-section-lift).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A section of the inverse image of one stage sheaf lifts to a later stage.
Source: Stacks Project, Sites Tag 09YN, proof of lemma-colimit, and Étale
Cohomology Tag 09YQ, degree-zero affine-site comparison.
(blueprint: lem-weil-pbc-fixed-abelian-descended-section-lift).

Proof: Restrict the scheme diagram to the directed upper tail of i. Its limit
is the same scheme, since the tail is cofinal. Present its full affine étale
sites by the category colimit, using descent of finitely presented objects,
arrows, and equalities. The affine-site topos equivalence identifies inverse
images with their affine-site inverse images. The section formula of 09YN
for the single coefficient sheaf H expresses each inverse-image section as a
filtered colimit of its stage inverse-image sections. The first-projection
conditions on gamma and delta, and their equations over the base schemes,
uniquely identify their composites with the pullback-pasting comparison.
Uniqueness of adjoints identifies the section-colimit legs with the unit for
the limit projection followed by the inverse of upperStarComp and restriction
along that pasting comparison. Thus every affine section has a representative.
For a qcqs object, choose a finite affine cover and finite affine covers of its
pairwise intersections. Lift the finitely many sections on the cover to a
common stage; descend their overlap equalities to one further stage, using
the eventual equality assertion in the same filtered section colimits. The
sheaf condition glues the resulting matching family, and separatedness
identifies its limit image with the original section. The empty cover yields
the zero section; a nonempty tail supplies its stage. No varying coefficients,
transition maps between different coefficient sheaves, or sheaf colimit occur
in this assertion. -/
theorem fixed_abelian_descended_section_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) (T₀ : (D.obj (op i₀)).Etale)
    [CompactSpace T₀.left] [QuasiSeparatedSpace T₀.left] :
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
    ∀ (i : J) (H : Sheaf (D.obj (op i.val)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (y : ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i.val))).obj H).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op i.val))).obj (Tj i)))),
      ∃ (k : J) (a : i ⟶ k)
        (s : ((upperStar AddCommGrpCat.{u + 1}
          (D.map (show i.val ⟶ k.val from a).op)).obj H).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤
              (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i)))),
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
          (c.π.app (op k.val))).unit.app
            ((upperStar AddCommGrpCat.{u + 1}
              (D.map (show i.val ⟶ k.val from a).op)).obj H)).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤
                  (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i))) ≫
          ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op k.val))
            (D.map (show i.val ⟶ k.val from a).op) (c.π.app (op i.val))
              (c.w (show i.val ⟶ k.val from a).op).symm).inv.app H).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤
                  (c.π.app (op k.val))).obj
                    ((MorphismProperty.Over.pullback @Etale ⊤
                      (D.map (show i.val ⟶ k.val from a).op)).obj (Tj i)))) ≫
          ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i.val))).obj H).obj.map
            ((δ i).hom ≫ (δ k).inv ≫
              (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op k.val))).map
                (γ i k a).inv).op) s = y := by sorry

end AlgebraicGeometry.Etale
