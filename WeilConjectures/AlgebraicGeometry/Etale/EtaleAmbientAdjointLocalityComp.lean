/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality

/-!
# Étale localization of the ambient adjoint and composition

For a separated étale morphism `u : U ⟶ X` of finite type and `f : X ⟶ S`, a right adjoint `G`
of `R(u ≫ f)_!` is the restriction `F ⋙ u^*` of a right adjoint `F` of `Rf_!`, through a unique
isomorphism `e : F ⋙ u^* ≅ G` normalized by its counit
(`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`, blueprint
`lemma-affine-space-etale-localization` (6.12)): the counit of `R(u ≫ f)_! ⊣ G` is the inverse
composition comparison, followed by the counit of the extension by zero `u_! ⊣ u^*` and by the
counit of `Rf_! ⊣ F`. This normalization is the predicate
`AlgebraicGeometry.Etale.IsEtaleAmbientLocalityIso`.

For a second separated étale morphism `u' : U' ⟶ U` of finite type, the isomorphism for `u' ≫ u`
is the composite of `u'^*` of the isomorphism for `u` and of the isomorphism for `u'` and `u ≫ f`
(`AlgebraicGeometry.Etale.etaleAmbientLocalityIso_comp`, blueprint
`lemma-affine-space-etale-localization--6`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The counit normalization of the étale localization isomorphism (blueprint
`lemma-affine-space-etale-localization` (6.12)): for right adjoints `F` of `Rf_!(c)` and `G` of
`R(u ≫ f)_!(d)`, an isomorphism `e : F ⋙ u^* ≅ G` is *the* localization isomorphism if, for every
normalization `N` of compact supports, the counit of `R(u ≫ f)_!(d) ⊣ G` read through `e` is the
inverse composition comparison `R(u ≫ f)_!(d) ≅ Rf_!(c) ∘ u_!`, followed by the counit of
`u_! ⊣ u^*` and by the counit of `Rf_!(c) ⊣ F`. Such an `e` exists and is unique
(`AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`). -/
def IsEtaleAmbientLocalityIso {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    {F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U}
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G)
    (e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G) : Prop :=
  ∀ (N : EtaleCompactSupportNormalization A) (K : DerivedCategoryModule A S),
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        (e.hom.app K) ≫ adjG.counit.app K =
      (etaleAmbientLeftComparison A N u f c d).inv.app
          ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u inferInstance).counit.app (F.obj K)) ≫
        adjF.counit.app K

/-- Blueprint `lemma-affine-space-etale-localization--6`: *the étale localization isomorphism is
compatible with composition*. Let `u' : U' ⟶ U` and `u : U ⟶ X` be separated étale morphisms of
finite type and `f : X ⟶ S`, all schemes Noetherian, with compactifications `c` of `f`, `d` of
`u ≫ f` and `d'` of `u' ≫ u ≫ f`, and right adjoints `F`, `G`, `H` of the corresponding compact
support direct images. If `e₁ : F ⋙ u^* ≅ G`, `e₂ : G ⋙ u'^* ≅ H` and `e₃ : F ⋙ (u' ≫ u)^* ≅ H`
are the localization isomorphisms (6.12) for `(u, f)`, `(u', u ≫ f)` and `(u' ≫ u, f)`
(`AlgebraicGeometry.Etale.IsEtaleAmbientLocalityIso`), then `e₃` is the composite of
`(u' ≫ u)^* ≅ u^* ⋙ u'^*`, of `u'^*` applied to `e₁`, and of `e₂`. -/
theorem etaleAmbientLocalityIso_comp {U' U X S : Scheme.{u}} (u' : U' ⟶ U) (u : U ⟶ X)
    (f : X ⟶ S) [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U'] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (d' : Compactification (u' ≫ u ≫ f))
    {F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U}
    {H : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U'}
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G)
    (adjH : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d' ⊣ H)
    (e₁ : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G)
    (e₂ : G ⋙ (upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategory ≅ H)
    (e₃ : F ⋙ (upperStar (ModuleCat.{u + 1} A) (u' ≫ u)).mapDerivedCategory ≅ H)
    (h₁ : IsEtaleAmbientLocalityIso A u f c d adjF adjG e₁)
    (h₂ : IsEtaleAmbientLocalityIso A u' (u ≫ f) d d' adjG adjH e₂)
    (h₃ : IsEtaleAmbientLocalityIso A (u' ≫ u) f c (d'.copy (Category.assoc u' u f)) adjF adjH
      e₃) :
    e₃ = Functor.isoWhiskerLeft F
        (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) u' u) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) u)
            (upperStar (ModuleCat.{u + 1} A) u')).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ _ ≪≫ e₂ := by
  sorry

end AlgebraicGeometry.Etale
