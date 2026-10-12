/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-!
# The presheaf of shifted maps out of free sheaves

For `L ∈ D⁺(X_ét, Λ)` and `q : ℤ`, the presheaf `W ↦ Hom(Λ[W][0], L⟦q⟧)` on the small étale site
of `X` maps to the sections of the cohomology sheaf `H^q(L)`
(`AlgebraicGeometry.Etale.shiftedHomPresheafToSheaf`); this map is locally injective and locally
surjective, and natural in `L`. For `L = Rh_* K` this presheaf is `W ↦ H^q(W ×_X Y, K|)`.

## Main definitions

- `AlgebraicGeometry.Etale.shiftedHomPresheaf`: the presheaf `W ↦ Hom(Λ[W][0], L⟦q⟧)`.
- `AlgebraicGeometry.Etale.shiftedHomPresheafToSheaf`: its map to the sections of `H^q(L)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

variable (Λ) in
/-- The presheaf `W ↦ Hom(Λ[W][0], L⟦q⟧)` of abelian groups on the small étale site of `X`. -/
noncomputable abbrev Etale.shiftedHomPresheaf
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Etale.freeSheaf Λ X ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
    preadditiveYoneda.obj (L⟦q⟧)

/-- The identification `H⁰(L⟦q⟧) ≅ H^q(L)`. -/
noncomputable abbrev Etale.homologyShiftIso
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj (L⟦q⟧) ≅
      (DerivedCategory.Plus.homologyFunctor _ q).obj L :=
  ((DerivedCategory.Plus.homologyFunctor _ 0).isoShift q).app L

/-- The map from the presheaf `W ↦ Hom(Λ[W][0], L⟦q⟧)` to the sections of `H^q(L)`: a class
`Λ[W][0] ⟶ L⟦q⟧` gives on degree-`0` homology a map `Λ[W] ⟶ H⁰(L⟦q⟧) = H^q(L)`, which is a
section of `H^q(L)` over `W`. -/
noncomputable def Etale.shiftedHomPresheafToSheaf
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    Etale.shiftedHomPresheaf Λ L q ⟶
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj L)).obj :=
  Etale.derivedHomToHomology (L⟦q⟧) ≫ Etale.freeSheafSections Λ _ ≫
    Etale.sectionsMap (Etale.homologyShiftIso L q).hom

/-- The map from `W ↦ Hom(Λ[W][0], L⟦q⟧)` to the sections of `H^q(L)` is locally injective and
locally surjective. -/
theorem Etale.isLocallyBijective_shiftedHomPresheafToSheaf
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (Etale.shiftedHomPresheafToSheaf L q) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (Etale.shiftedHomPresheafToSheaf L q) := by
  have : IsIso (Etale.sectionsMap (Etale.homologyShiftIso L q).hom) := inferInstanceAs
    (IsIso ((sheafToPresheaf _ _).map ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (Etale.homologyShiftIso L q).hom)))
  obtain ⟨_, _⟩ := Etale.isLocallyBijective_derivedHomToHomology (L⟦q⟧)
  have e : Etale.shiftedHomPresheafToSheaf L q =
      (Etale.derivedHomToHomology (L⟦q⟧) ≫ Etale.freeSheafSections Λ _) ≫
        Etale.sectionsMap (Etale.homologyShiftIso L q).hom := by
    rw [Etale.shiftedHomPresheafToSheaf, Category.assoc]
  rw [e]
  exact ⟨inferInstance, inferInstance⟩

/-- The sections map of a morphism `g : G ⟶ G'` sends the section given by `φ : Λ[W] ⟶ G` to
the section given by `φ ≫ g`. -/
lemma Etale.sectionsMap_app_freeSheafSections_app
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : G ⟶ G') (W : X.Etaleᵒᵖ)
    (φ : (Etale.freeSheaf Λ X).obj W.unop ⟶ G) :
    (Etale.sectionsMap g).app W ((Etale.freeSheafSections Λ G).app W φ) =
      (Etale.freeSheafSections Λ G').app W (φ ≫ g) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (Etale.freeSheafSections_naturality g) W) φ

/-- Naturality of `AlgebraicGeometry.Etale.shiftedHomPresheafToSheaf` in `L`, on elements: for
`f : L ⟶ L'` and a class `x : Λ[W][0] ⟶ L⟦q⟧`, the section of `H^q(L')` given by `x ≫ f⟦q⟧` is
the image under `H^q(f)` of the section given by `x`. -/
lemma Etale.shiftedHomPresheafToSheaf_app_comp
    {L L' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : L ⟶ L') (q : ℤ) (W : X.Etaleᵒᵖ)
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ X).obj W.unop) ⟶ L⟦q⟧) :
    (Etale.shiftedHomPresheafToSheaf L' q).app W (x ≫ f⟦q⟧') =
      (Etale.sectionsMap ((DerivedCategory.Plus.homologyFunctor _ q).map f)).app W
        ((Etale.shiftedHomPresheafToSheaf L q).app W x) := by
  have h₁ : (Etale.derivedHomToHomology (L'⟦q⟧)).app W (x ≫ f⟦q⟧') =
      (Etale.derivedHomToHomology (L⟦q⟧)).app W x ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map (f⟦q⟧') := by
    rw [Etale.derivedHomToHomology_app_apply, Etale.derivedHomToHomology_app_apply,
      Functor.map_comp, Category.assoc]
  have h₂ : (DerivedCategory.Plus.homologyFunctor _ 0).map (f⟦q⟧') ≫
      (Etale.homologyShiftIso L' q).hom =
      (Etale.homologyShiftIso L q).hom ≫ (DerivedCategory.Plus.homologyFunctor _ q).map f :=
    Functor.isoShift_hom_naturality _ q f
  simp only [Etale.shiftedHomPresheafToSheaf, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [h₁]
  simp only [Etale.sectionsMap_app_freeSheafSections_app, Category.assoc, h₂]

end AlgebraicGeometry
