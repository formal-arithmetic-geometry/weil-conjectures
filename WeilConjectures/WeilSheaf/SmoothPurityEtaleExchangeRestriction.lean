/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRestrict

/-! # Restricting the left exchange to full subcategories

The comparison is proved with explicit preservation data. Consequently a concrete
application never unfolds a compactification or a coefficient construction.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {PA : ObjectProperty A} {PB : ObjectProperty B} {PA' : ObjectProperty A'}
  {PB' : ObjectProperty B'}
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  {H : A ⥤ A'} {H' : B ⥤ B'}
  (adj : L ⊣ R) (adj' : L' ⊣ R') (t : R ⋙ H ≅ H' ⋙ R')
  (hL : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ L).obj K))
  (hR : ∀ K : PB.FullSubcategory, PA ((PB.ι ⋙ R).obj K))
  (hL' : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ L').obj K))
  (hR' : ∀ K : PB'.FullSubcategory, PA' ((PB'.ι ⋙ R').obj K))
  (hH : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ H).obj K))
  (hH' : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ H').obj K))

/-- Restriction of a left exchange has the original underlying component. -/
lemma purity_exchangeLeft_restrictFullyFaithful_app_hom
    (θ : PA.lift (PB.ι ⋙ R) hR ⋙ PA'.lift (PA.ι ⋙ H) hH ≅
      PB'.lift (PB.ι ⋙ H') hH' ⋙ PA'.lift (PB'.ι ⋙ R') hR')
    (hθ : ∀ K, (θ.hom.app K).hom = t.hom.app K.obj) (K : PA.FullSubcategory) :
    ((exchangeLeft
        (adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
          (PB.liftCompιIso (PA.ι ⋙ L) hL).symm (PA.liftCompιIso (PB.ι ⋙ R) hR).symm)
        (adj'.restrictFullyFaithful PA'.fullyFaithfulι PB'.fullyFaithfulι
          (PB'.liftCompιIso (PA'.ι ⋙ L') hL').symm
          (PA'.liftCompιIso (PB'.ι ⋙ R') hR').symm)
        θ).app K).hom = (exchangeLeft adj adj' t).app K.obj := by
  have hu : ((adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
      (PB.liftCompιIso (PA.ι ⋙ L) hL).symm
      (PA.liftCompιIso (PB.ι ⋙ R) hR).symm).unit.app K).hom = adj.unit.app K.obj := by
    simpa [ObjectProperty.liftCompιIso] using adj.map_restrictFullyFaithful_unit_app
      PA.fullyFaithfulι PB.fullyFaithfulι (PB.liftCompιIso (PA.ι ⋙ L) hL).symm
      (PA.liftCompιIso (PB.ι ⋙ R) hR).symm K
  have hc (N : PB'.FullSubcategory) :
      ((adj'.restrictFullyFaithful PA'.fullyFaithfulι PB'.fullyFaithfulι
        (PB'.liftCompιIso (PA'.ι ⋙ L') hL').symm
        (PA'.liftCompιIso (PB'.ι ⋙ R') hR').symm).counit.app N).hom =
      adj'.counit.app N.obj := by
    simpa [ObjectProperty.liftCompιIso] using adj'.map_restrictFullyFaithful_counit_app
      PA'.fullyFaithfulι PB'.fullyFaithfulι (PB'.liftCompιIso (PA'.ι ⋙ L') hL').symm
      (PA'.liftCompιIso (PB'.ι ⋙ R') hR').symm N
  simp only [exchangeLeft_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.lift_map, ObjectProperty.homMk_hom, Functor.comp_map,
    ObjectProperty.ι_map, hu, hc, hθ] <;> rfl

/-- Ambient invertibility descends through the full-subcategory inclusion. -/
lemma purity_isIso_exchangeLeft_restrictFullyFaithful_app
    (θ : PA.lift (PB.ι ⋙ R) hR ⋙ PA'.lift (PA.ι ⋙ H) hH ≅
      PB'.lift (PB.ι ⋙ H') hH' ⋙ PA'.lift (PB'.ι ⋙ R') hR')
    (hθ : ∀ K, (θ.hom.app K).hom = t.hom.app K.obj) (K : PA.FullSubcategory)
    (hK : IsIso ((exchangeLeft adj adj' t).app K.obj)) :
    IsIso ((exchangeLeft
        (adj.restrictFullyFaithful PA.fullyFaithfulι PB.fullyFaithfulι
          (PB.liftCompιIso (PA.ι ⋙ L) hL).symm (PA.liftCompιIso (PB.ι ⋙ R) hR).symm)
        (adj'.restrictFullyFaithful PA'.fullyFaithfulι PB'.fullyFaithfulι
          (PB'.liftCompιIso (PA'.ι ⋙ L') hL').symm
          (PA'.liftCompιIso (PB'.ι ⋙ R') hR').symm)
        θ).app K) := by
  rw [← ObjectProperty.isIso_hom_iff,
    purity_exchangeLeft_restrictFullyFaithful_app_hom adj adj' t hL hR hL' hR' hH hH' θ hθ K]
  exact hK

end CategoryTheory.Adjunction
