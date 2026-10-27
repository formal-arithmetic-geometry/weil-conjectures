/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.SmoothPurityCoordinateCategories

/-! # Composition of restricted coordinate adjunctions

Source: Local pairs in the latest smooth-purity blueprint; Mathlib Adjunction.comp.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    {PA : ObjectProperty A} {PB : ObjectProperty B} {PC : ObjectProperty C}
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ C} {I : C ⥤ B}
    {J : A ⥤ C} {R : C ⥤ A}

/-- Lift a natural isomorphism through a full subcategory using its literal
ambient arrows, without choosing preimages. Source: fully faithful inclusion
(blueprint: lem-sp-coordinate-restricted-composition). -/
def restrictedIso {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]
    (P : ObjectProperty E) {F G : D ⥤ P.FullSubcategory}
    (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents
    (fun X ↦ P.fullyFaithfulι.preimageIso (X := F.obj X) (Y := G.obj X) (e.app X))
    (fun f ↦ ObjectProperty.hom_ext P (e.hom.naturality f))

/-- Compose the adjunctions on the full subcategories, then transport both functors
through the specified ambient comparisons. Source: Local pairs, chart composition
(blueprint: lem-sp-coordinate-restricted-composition). -/
def restrictedComposite (a : RestrictedPair PA PB F G) (b : RestrictedPair PB PC H I)
    (hJ : ∀ M : PA.FullSubcategory, PC (J.obj M.obj))
    (hR : ∀ K : PC.FullSubcategory, PA (R.obj K.obj))
    (alpha : PA.ι ⋙ F ⋙ H ≅ PA.ι ⋙ J) (beta : I ⋙ G ≅ R) :
    RestrictedPair PA PC J R where
  left_closed := hJ
  right_closed := hR
  adjunction :=
    ((a.adjunction.comp b.adjunction).ofNatIsoLeft
      (restrictedIso PC (G := PC.lift (PA.ι ⋙ J) hJ) alpha)).ofNatIsoRight
        (restrictedIso PA (G := PA.lift (PC.ι ⋙ R) hR)
          (Functor.isoWhiskerLeft PC.ι beta))

/-- The ambient counit of the transported composite has the specified inverse
comparisons and the two constituent counits in their original order.
Source: Mathlib Adjunction.comp_counit_app, applied to Local pairs
(blueprint: lem-sp-coordinate-restricted-composition). -/
theorem restrictedComposite_counit
    (a : RestrictedPair PA PB F G) (b : RestrictedPair PB PC H I)
    (hJ : ∀ M : PA.FullSubcategory, PC (J.obj M.obj))
    (hR : ∀ K : PC.FullSubcategory, PA (R.obj K.obj))
    (alpha : PA.ι ⋙ F ⋙ H ≅ PA.ι ⋙ J) (beta : I ⋙ G ≅ R) :
    CompositeEquation PA PB PC F G H I J R a b
      (restrictedComposite a b hJ hR alpha beta) alpha beta := by
  intro K
  dsimp only [RestrictedPair.counit, restrictedComposite]
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
    Adjunction.comp_counit_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp]
  simp only [restrictedIso, NatIso.ofComponents_inv_app,
    Functor.FullyFaithful.preimageIso_inv]
  rfl

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
