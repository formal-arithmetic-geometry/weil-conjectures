/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Every section of the inverse image on the affine limit descends to an affine stage. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Every section of the inverse image on the affine limit descends to an affine stage.
Source: Stacks Project, Tag 03Q6, degree zero of lemma-colimit, proof steps (1)--(3);
Sites, Tag 0A35, lemma-pullback-to-limit; Etale Cohomology, Tag 0EYL.
Proof: Fix a stage j0 (the given j for zero detection). Restrict to the category of
stages equipped with an arrow to j0. Cofilteredness makes its projection initial, so
this restricted diagram has the same limit. Replace it by a cofinal directed system.
Every stage and every transition is affine. Over the fixed affine stage D(j0), the
affine etale site of the limit is the colimit site: affine etale objects, morphisms,
equalities of morphisms, and finite covering families all descend to stages (0EYL).
The inverse-image section formula for this colimit site (0A35), evaluated at the
terminal affine etale object, is the filtered colimit of the stage sections.
For each open immersion D(k) to X, the localization-restriction comparison identifies
these sections with F(D(k)); its unit formula identifies transitions with restriction
along D arrows. The unique comparison of left adjoints to p_* carries the standard
unit to hH.unit. Its naturality with respect to the terminal-object pullback maps,
together with hν₀, identifies the formula's legs with ν₀.
Every element of that filtered colimit has a representative at some stage. This gives
the required j and s.
A singleton system reduces to restriction along an open immersion, an isomorphism on
these terminal sections. A zero sheaf has only the zero section. If the affine limit
is empty, its finite empty cover descends to an empty stage by 0EYL, so the same formula
handles that case. No empty indexing category is allowed by IsCofiltered.
(blueprint: affine-open-sections-descent) -/
theorem affineOpenSections_descent
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
    (ν₀ : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν₀ : ∀ j, ν₀.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (B := p.Etale.obj (D.obj j))
        (pullback.lift (c.π.app j) (𝟙 c.pt) (by
          change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
          rw [Category.id_comp]
          exact hp j))
        (by exact pullback.lift_snd _ _ _)).op) :
    ∀ t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))),
      ∃ (j : J) (s : F.obj.obj (op (D.obj j))), ν₀.app (op j) s = t := by sorry
