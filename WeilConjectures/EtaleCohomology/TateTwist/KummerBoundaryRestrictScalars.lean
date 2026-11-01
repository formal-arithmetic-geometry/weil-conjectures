/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerBoundaryCoefficientChange

/-!
# The Kummer boundary under a change of coefficients, with scalars restricted

The isomorphism `(Res F)[0] ≅ Res (F[0])` of the restriction of scalars with the inclusion in
degree zero, stated with the derived restriction of scalars
(`AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso`), and the compatibility of the Kummer
boundaries with a change of coefficients written with it
(`AlgebraicGeometry.Etale.kummerδ_comp_changeMap_singleFunctorRestrictScalarsIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- A categorical rearrangement: if `τ = a ≫ S q ≫ s ≫ G t` with `a = i ≫ S j`,
`η ≫ r = j ≫ q` and `S r ≫ s = n ≫ G g`, then `τ = (i ≫ S η ≫ n) ≫ G k` for `k = g ≫ t`. -/
lemma comp_map_eq_of_unit_comp_eq {C T T' : Type*} [Category* C] [Category* T] [Category* T']
    (S : C ⥤ T) (G : T' ⥤ T) {P : T} {A B M N : C} {N' Y Z : T'}
    {τ : P ⟶ G.obj Z} {a : P ⟶ S.obj B} {i : P ⟶ S.obj A} {j : A ⟶ B} {q : B ⟶ M}
    {s : S.obj M ⟶ G.obj Y}
    {t : Y ⟶ Z} {η : A ⟶ N} {r : N ⟶ M} {n : S.obj N ⟶ G.obj N'} {g : N' ⟶ Y} {k : N' ⟶ Z}
    (hτ : τ = a ≫ S.map q ≫ s ≫ G.map t) (ha : a = i ≫ S.map j) (hu : η ≫ r = j ≫ q)
    (hn : S.map r ≫ s = n ≫ G.map g) (hk : k = g ≫ t) :
    τ = (i ≫ S.map η ≫ n) ≫ G.map k := by
  subst hτ ha hk
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, ← hu, S.map_comp_assoc, reassoc_of% hn, G.map_comp]

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The isomorphism `(Res (Λ' ⊗ F))[0] ≅ Res ((Λ' ⊗ F)[0])` of the restriction of scalars along
`ρ` with the inclusion in degree zero (`Functor.mapDerivedCategorySingleFunctorObjIso`), stated
with the derived restriction of scalars `Sheaf.derivedRestrictScalars`. -/
noncomputable def singleFunctorRestrictScalarsIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (DerivedCategory.singleFunctor _ 0).obj
        ((extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F) ≅
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((extendScalars Λ' X).obj F)) :=
  (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctorObjIso 0
    ((extendScalars Λ' X).obj F)

/-- The definition of `singleFunctorRestrictScalarsIso` (its equation lemma). -/
lemma singleFunctorRestrictScalarsIso_eq (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    type_of% (singleFunctorRestrictScalarsIso.eq_1 ρ X F) :=
  singleFunctorRestrictScalarsIso.eq_1 ρ X F

/-- The isomorphism `AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso` is the inverse of
`Functor.mapDerivedCategorySingleFunctor`. -/
lemma singleFunctorRestrictScalarsIso_hom (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (singleFunctorRestrictScalarsIso ρ X F).hom =
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
        ((extendScalars Λ' X).obj F) :=
  rfl

/-- The naturality of `AlgebraicGeometry.Etale.singleFunctorRestrictScalarsIso` with respect to a
morphism `f : A ⟶ Λ' ⊗ F` of sheaves of `Λ'`-modules. -/
lemma singleFunctor_map_restrictScalars_map_comp_singleFunctorRestrictScalarsIso_hom
    {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : A ⟶ (extendScalars Λ' X).obj F) :
    (DerivedCategory.singleFunctor _ 0).map ((Sheaf.restrictScalars X.smallEtaleTopology ρ).map f) ≫
        (singleFunctorRestrictScalarsIso ρ X F).hom =
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app A ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          ((DerivedCategory.singleFunctor _ 0).map f) := by
  rw [singleFunctorRestrictScalarsIso_hom]
  exact ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor
    0).inv.naturality f

variable {X} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (e : ℕ)
  (he : ringChar Λ = ringChar Λ' * e)

/-- The connecting morphism of the pulled back Kummer sequence with coefficients `Λ'` and
scalars restricted to `Λ`, with its objects written explicitly. -/
noncomputable def kummerδRestrictScalars {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    (DerivedCategory.singleFunctor _ 0).obj
        ((extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ).obj C) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        ((extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
          (X.rootsOfUnitySheaf (ringChar Λ'))))⟦(1 : ℤ)⟧ :=
  ((shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC).map_of_exact
    (Sheaf.restrictScalars X.smallEtaleTopology ρ)).singleδ

/-- `AlgebraicGeometry.Etale.kummerδ_comp_changeMap` with
`AlgebraicGeometry.Etale.kummerδRestrictScalars`. -/
lemma kummerδ_comp_changeMap_eq_kummerδRestrictScalars
    {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    kummerδ Λ φ hC ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app (X.rootsOfUnitySheaf (ringChar Λ'))))⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app C) ≫
        kummerδRestrictScalars ρ φ hC :=
  kummerδ_comp_changeMap ρ e he φ hC

end AlgebraicGeometry.Etale
