/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel

/-! # Horizontal coherence of the canonical additive Roos comparison

Source: Stacks Tag 0941, lemma-derived-limit-is-ok, product-cone context, and the
agent-written coordinate calculation in the DAG proof
(blueprint: lem-pur-roos-comparison-horizontal-coherence).

The comparison is constructed directly by Mathlib's `mappingCocone.lift` on the fixed
`roosF` model, using the two mapped projections and the canonical product comparison.
No exactness or preservation of products is assumed for its definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe uA vA uB vB uD vD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasCountableProducts D]

/-- Termwise application of an additive functor to a complex of strict towers.
Source: Stacks Tag 0941, product-cone context
(blueprint: lem-pur-roos-comparison-horizontal-coherence). -/
def roosTowerAction (F : A ⥤ B) [F.Additive] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The product comparison as a cochain map, determined by its product projections.
Source: Stacks Tag 0941, product-cone context
(blueprint: lem-pur-roos-comparison-horizontal-coherence). -/
def roosProductComparison (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (roosP X) ⟶
      roosP ((roosTowerAction F).obj X) :=
  piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ))
    (fun n : ℕ ↦ X.asFunctor.obj (op n))

private lemma productComparison_u (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosU X) ≫
        roosProductComparison F X =
      roosProductComparison F X ≫ roosU ((roosTowerAction F).obj X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
    change FC.map (roosU X) ≫ piComparison FC _ =
      piComparison FC _ ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ FC.map (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    apply Pi.hom_ext
    intro n
    simp [roosU, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Functor.map_comp]

private lemma cocone_snd_delta (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0 (CochainComplex.mappingCocone.snd (roosU X)) =
      -CochainComplex.HomComplex.Cochain.ofHom
        (CochainComplex.mappingCocone.fst (roosU X) ≫ roosU X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    open CochainComplex.HomComplex in
    dsimp only [CochainComplex.mappingCocone.snd]
    rw [Cochain.δ_leftShift _ (-1) (-1) 0 (by omega) 1 (by omega),
      CochainComplex.mappingCone.δ_snd]
    simp [CochainComplex.mappingCocone.fst]

/-- The compatibility equation for the two coordinates of the additive Roos lift.
Source: Stacks Tag 0941, product-cone context
(blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG steps 1-3. The mapping cocone projections satisfy
δ(snd) + ofHom(fst ≫ u) = 0, by the signed cone differential. Applying the additive
functor preserves this equation, since it preserves sums, negatives and composition.
Postcompose both coordinates with the product comparison. Its square with u = 1-s
commutes: after the nth product projection both sides are F(π_n - π_(n+1) ≫ t_n),
using `towerTransitionEndomorphism` and additivity. The differential of a cochain
postcomposed with a chain map is its differential postcomposed with that map.
Thus the mapped cocone equation becomes exactly the displayed lift condition. -/
theorem roosAdditiveComparison_lift_condition (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (((CochainComplex.mappingCocone.snd (roosU X)).map F).comp
          (CochainComplex.HomComplex.Cochain.ofHom (roosProductComparison F X))
          (add_zero (-1))) +
      CochainComplex.HomComplex.Cochain.ofHom
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (CochainComplex.mappingCocone.fst (roosU X)) ≫
          roosProductComparison F X) ≫ roosU ((roosTowerAction F).obj X)) = 0 := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    open CochainComplex.HomComplex in
    rw [δ_comp_ofHom, δ_map, cocone_snd_delta]
    simp only [Cochain.map_neg, Cochain.map_ofHom, Cochain.neg_comp,
      ← Cochain.ofHom_comp, Functor.map_comp]
    rw [Category.assoc, productComparison_u]
    simp only [Category.assoc, neg_add_cancel]

/-- The canonical two-coordinate comparison in the fixed `roosF` model, constructed
by the mapping cocone lift of the mapped projections followed by the product
comparison on both coordinates. The product comparison commutes with 1-s, as used
in `roosAdditiveComparison_lift_condition`.
Source: Stacks Tag 0941, product-cone context
(blueprint: lem-pur-roos-comparison-horizontal-coherence). -/
def roosAdditiveComparison (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (roosF.obj X) ⟶
      roosF.obj ((roosTowerAction F).obj X) :=
  CochainComplex.mappingCocone.lift (roosU ((roosTowerAction F).obj X))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCocone.fst (roosU X)) ≫ roosProductComparison F X)
    (((CochainComplex.mappingCocone.snd (roosU X)).map F).comp
      (CochainComplex.HomComplex.Cochain.ofHom (roosProductComparison F X))
      (add_zero (-1)))
    (roosAdditiveComparison_lift_condition F X)

private lemma cocone_fst_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.fst (roosU X)).f (p + 1) =
      (roosχ X p).hom ≫ biprod.snd := roosProj_f X p

private lemma cocone_snd_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.snd (roosU X)).v (p + 1) p (by omega) =
      (roosχ X p).hom ≫ biprod.fst := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
        HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
          (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hq).hom ≫
            biprod.snd := by
      obtain rfl := (ComplexShape.up ℤ).next_eq' hq
      dsimp only [HomologicalComplex.homotopyCofiber.sndX]
      rw [dif_pos hq]
    simp [roosχ, CochainComplex.mappingCocone.snd,
      CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.snd,
      hs p (p + 1) rfl, show Int.negOnePow 2 = 1 by rfl]

/-- The fixed degree-p+1 formula: biproduct comparison followed by the product
comparisons in degrees p and p+1.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG steps 1-3. The biproduct comparison is determined by the images of the
projections, with inverse determined by the images of the inclusions. Additivity
preserves negatives and sums. The product comparison commutes with d and 1-s after
each product projection. The signed differential matrix therefore commutes with
the displayed comparison. The two projection identities for `mappingCocone.lift`,
transported through `roosχ`, give precisely the displayed coordinate formula. -/
theorem roosAdditiveComparison_coordinates (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom =
      F.map (roosχ X p).hom ≫ F.biprodComparison ((roosP X).X p)
        ((roosP X).X (p + 1)) ≫
        biprod.map ((roosProductComparison F X).f p)
          ((roosProductComparison F X).f (p + 1)) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc]
      rw [← cocone_snd_coordinates]
      dsimp only [roosAdditiveComparison]
      rw [CochainComplex.mappingCocone.lift_f_snd_v]
      simp only [CochainComplex.HomComplex.Cochain.comp_v (n₁ := -1) (n₂ := 0) _ _ _
          (p + 1) p p (by omega) (add_zero p),
        CochainComplex.HomComplex.Cochain.map_v,
        CochainComplex.HomComplex.Cochain.ofHom_v, cocone_snd_coordinates,
        Functor.map_comp, Category.assoc]
    · simp only [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc]
      rw [← cocone_fst_coordinates]
      dsimp only [roosAdditiveComparison]
      rw [CochainComplex.mappingCocone.lift_f_fst_f]
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        cocone_fst_coordinates, Functor.map_comp, Category.assoc]

private lemma comparison_fst (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.fst =
      F.map ((roosχ X p).hom ≫ biprod.fst) ≫ (roosProductComparison F X).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma comparison_snd (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.snd =
      F.map ((roosχ X p).hom ≫ biprod.snd) ≫
        (roosProductComparison F X).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma productComparison_natural (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (h : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosPmap h) ≫
        roosProductComparison F Y =
      roosProductComparison F X ≫ roosPmap ((roosTowerAction F).map h) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply Pi.hom_ext
    intro n
    change (_ ≫ roosProductComparison F Y) ≫ Pi.π (fun n : ℕ ↦
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Y.asFunctor.obj (op n))) n = _
    simp only [Category.assoc, roosProductComparison, piComparison_comp_π, roosPmap,
      Pi.map_π, ← Functor.map_comp]
    change _ = piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
      Pi.π (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (X.asFunctor.obj (op n))) n ≫ _
    rw [piComparison_comp_π_assoc, Functor.map_comp]
    rfl

private lemma roos_map_fst {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (h : X ⟶ Y) (p : ℤ) :
    (roosF.map h).f (p + 1) ≫ (roosχ Y p).hom ≫ biprod.fst =
      (roosχ X p).hom ≫ biprod.fst ≫ (roosPmap h).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosF_map_χ]
    simp

private lemma roos_map_snd {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (h : X ⟶ Y) (p : ℤ) :
    (roosF.map h).f (p + 1) ≫ (roosχ Y p).hom ≫ biprod.snd =
      (roosχ X p).hom ≫ biprod.snd ≫ (roosPmap h).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosF_map_χ]
    simp

/-- Naturality is equality of strict cochain maps.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 4. Postcompose with each product projection of each biproduct
coordinate. Both sides are the functor image of the same coordinate of the tower
map, by functoriality. Product and biproduct extensionality give equality. -/
theorem roosAdditiveComparison_natural (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (h : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosF.map h) ≫
        roosAdditiveComparison F Y =
      roosAdditiveComparison F X ≫ roosF.map ((roosTowerAction F).map h) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosF.map h) ≫
      roosAdditiveComparison F Y).f (p + 1) =
        (roosAdditiveComparison F X ≫ roosF.map ((roosTowerAction F).map h)).f (p + 1)
    apply (cancel_mono (roosχ ((roosTowerAction F).obj Y) p).hom).1
    simp only [HomologicalComplex.comp_f]
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [comparison_fst F Y p, roos_map_fst ((roosTowerAction F).map h) p]
      erw [reassoc_of% comparison_fst F X p]
      simp only [Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ← F.map_comp, roos_map_fst]
      have hp := congrArg (fun f ↦ f.f p) (productComparison_natural F h)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
      simp only [F.map_comp, Category.assoc]
      rw [hp]
    · simp only [Category.assoc]
      erw [comparison_snd F Y p, roos_map_snd ((roosTowerAction F).map h) p]
      erw [reassoc_of% comparison_snd F X p]
      simp only [Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ← F.map_comp, roos_map_snd]
      have hp := congrArg (fun f ↦ f.f (p + 1)) (productComparison_natural F h)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
      simp only [F.map_comp, Category.assoc]
      rw [hp]

private lemma productComparison_horizontal
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (L : A ⥤ D) [L.Additive] (α : F ⋙ G ⟶ L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosProductComparison F X) ≫
        roosProductComparison G ((roosTowerAction F).obj X) ≫
        roosPmap ((NatTrans.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X) =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosP X) ≫
        roosProductComparison L X := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let aX := (NatTrans.mapHomologicalComplex
      ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, roosPmap, Pi.map_π]
    change (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosProductComparison F X) ≫
      piComparison (G.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
        Pi.π (fun n : ℕ ↦ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((roosTowerAction F).obj X).asFunctor.obj (op n))) n ≫ _ = _
    rw [piComparison_comp_π_assoc, ← Functor.map_comp_assoc]
    change (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
        Pi.π (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (X.asFunctor.obj (op n))) n) ≫ _ = _
    rw [piComparison_comp_π]
    change _ = (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosP X) ≫
      piComparison (L.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
        Pi.π (fun n : ℕ ↦ (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (X.asFunctor.obj (op n))) n
    rw [piComparison_comp_π]
    ext p
    exact α.naturality ((Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p)

/-- Horizontal coherence for an arbitrary natural transformation GF → L.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 5. For either coordinate e and any product level, the left side
becomes alpha at that level followed by GF(e), while the right side is L(e)
following alpha at the Roos object. These agree by naturality of alpha at e.
Product and biproduct projections jointly detect equality of cochain maps.
Neither alpha nor either product comparison needs to be invertible. -/
theorem roosComparison_horizontal_coherence
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (L : A ⥤ D) [L.Additive] (α : F ⋙ G ⟶ L)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosAdditiveComparison F X) ≫
        roosAdditiveComparison G ((roosTowerAction F).obj X) ≫
        roosF.map ((NatTrans.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X) =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosF.obj X) ≫
        roosAdditiveComparison L X := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let aX := (NatTrans.mapHomologicalComplex
      ((Functor.whiskeringRight ℕᵒᵖ A D).map α) (ComplexShape.up ℤ)).app X
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (roosAdditiveComparison F X) ≫
        roosAdditiveComparison G ((roosTowerAction F).obj X) ≫ roosF.map aX).f (p + 1) =
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app (roosF.obj X) ≫
        roosAdditiveComparison L X).f (p + 1)
    apply (cancel_mono (roosχ ((roosTowerAction L).obj X) p).hom).1
    simp only [HomologicalComplex.comp_f]
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [roos_map_fst aX p, reassoc_of% comparison_fst G ((roosTowerAction F).obj X) p,
        comparison_fst L X p]
      simp only [Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
      rw [← G.map_comp_assoc, comparison_fst, G.map_comp]
      have hp := congrArg (fun f ↦ f.f p) (productComparison_horizontal F G L α X)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f] at hp
      rw [Category.assoc, hp]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ (roosProductComparison L X).f p)
          (α.naturality ((roosχ X p).hom ≫ biprod.fst))
    · simp only [Category.assoc]
      erw [roos_map_snd aX p, reassoc_of% comparison_snd G ((roosTowerAction F).obj X) p,
        comparison_snd L X p]
      simp only [Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
      rw [← G.map_comp_assoc, comparison_snd, G.map_comp]
      have hp := congrArg (fun f ↦ f.f (p + 1)) (productComparison_horizontal F G L α X)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f] at hp
      rw [Category.assoc, hp]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ (roosProductComparison L X).f (p + 1))
          (α.naturality ((roosχ X p).hom ≫ biprod.snd))

/-- Preservation of countable products makes this very comparison an isomorphism.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 6. Each product comparison is invertible by preservation of its
product cone. The biproduct comparison is invertible by additivity. Thus the
coordinate formula gives degreewise inverses; the chain-map equation implies
that these inverses commute with differentials, giving an inverse chain map. -/
theorem roosAdditiveComparison_isIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (roosAdditiveComparison F X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have : IsIso (roosProductComparison F X) := by
      dsimp only [roosProductComparison]
      infer_instance
    have : ∀ k : ℤ, IsIso ((roosAdditiveComparison F X).f k) := by
      intro k
      obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
      change IsIso ((roosAdditiveComparison F X).f (p + 1))
      have : IsIso ((roosAdditiveComparison F X).f (p + 1) ≫
          (roosχ ((roosTowerAction F).obj X) p).hom) := by
        rw [roosAdditiveComparison_coordinates]
        have : ∀ r : ℤ, IsIso ((roosProductComparison F X).f r) := fun r ↦
          inferInstanceAs (IsIso ((HomologicalComplex.eval B (ComplexShape.up ℤ) r).map
            (roosProductComparison F X)))
        have : PreservesBinaryBiproduct ((roosP X).X p) ((roosP X).X (p + 1)) F :=
          preservesBinaryBiproduct_of_preservesBiproduct F _ _
        have : IsIso (F.biprodComparison ((roosP X).X p) ((roosP X).X (p + 1))) :=
          (F.mapBiprod ((roosP X).X p) ((roosP X).X (p + 1))).isIso_hom
        have hfirst : IsIso (F.map (roosχ X p).hom) := (F.mapIso (roosχ X p)).isIso_hom
        have hlast : IsIso (biprod.map ((roosProductComparison F X).f p)
            ((roosProductComparison F X).f (p + 1))) :=
          (biprod.mapIso (asIso ((roosProductComparison F X).f p))
            (asIso ((roosProductComparison F X).f (p + 1)))).isIso_hom
        exact IsIso.comp_isIso' hfirst (IsIso.comp_isIso' inferInstance hlast)
      exact IsIso.of_isIso_comp_right _ (roosχ ((roosTowerAction F).obj X) p).hom
    exact HomologicalComplex.Hom.isIso_of_components _

/-- The identity comparison is the canonical identity identification.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 6. Every coordinate of the comparison for the identity functor is
unchanged. Joint monicity of the two sets of product projections proves equality. -/
theorem roosAdditiveComparison_id (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosAdditiveComparison (𝟭 A) X =
      (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app (roosF.obj X) ≫
        roosF.map ((Functor.mapHomologicalComplexIdIso (ℕᵒᵖ ⥤ A)
          (ComplexShape.up ℤ)).inv.app X) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hp : roosProductComparison (𝟭 A) X = 𝟙 (roosP X) := by
      apply Pi.hom_ext
      intro n
      change piComparison ((𝟭 A).mapHomologicalComplex (ComplexShape.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n = _
      erw [piComparison_comp_π]
      ext p
      change (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p =
        𝟙 _ ≫ (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p
      exact (Category.id_comp _).symm
    change roosAdditiveComparison (𝟭 A) X =
      𝟙 (roosF.obj X) ≫ roosF.map (𝟙 X)
    rw [roosF.map_id, Category.id_comp]
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change (roosAdditiveComparison (𝟭 A) X).f (p + 1) = 𝟙 _
    apply (cancel_mono (roosχ X p).hom).1
    apply biprod.hom_ext
    · erw [Category.assoc, comparison_fst (𝟭 A) X p]
      simp only [hp, HomologicalComplex.id_f, Functor.id_map, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, comparison_snd (𝟭 A) X p]
      simp only [hp, HomologicalComplex.id_f, Functor.id_map, Category.id_comp]
      exact Category.comp_id _

/-- A strict augmentation retains its zero shifted coordinate and its mapped family.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 7. Compose the coordinate formula with F(q). Its first product
coordinates are F(0)=0 and its second product coordinates are F(q_n).
The original compatibility equation remains true after applying F. Product
extensionality gives the displayed biproduct-coordinate equality. -/
theorem roosAdditiveComparison_augmentation (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (q : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hq : ∀ n : ℕ, q (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = q n)
    (p : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosAugment q hq) ≫
        roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom =
      biprod.lift 0
        ((Pi.lift (fun n : ℕ ↦
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (q n))).f (p + 1)) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    apply biprod.hom_ext
    · simp only [Category.assoc, comparison_fst]
      have h := congrArg (fun f ↦ f ≫ biprod.fst) (roosAugment_χ q hq p)
      simp only [Category.assoc, biprod.lift_fst] at h
      rw [← Category.assoc, ← F.map_comp, h, F.map_zero, zero_comp]
      exact (biprod.lift_fst _ _).symm
    · simp only [Category.assoc, comparison_snd, biprod.lift_snd]
      have h := congrArg (fun f ↦ f ≫ biprod.snd) (roosAugment_χ q hq p)
      simp only [Category.assoc, biprod.lift_snd] at h
      rw [← Category.assoc, ← F.map_comp, h]
      exact congrArg (fun f ↦ f.f (p + 1))
        (map_lift_piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (fun n : ℕ ↦ X.asFunctor.obj (op n)) P q)

end CategoryTheory
