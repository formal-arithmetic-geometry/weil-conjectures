/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate2
public import WeilConjectures.TateTwist.ComparisonSingleInv

/-!
# `Rν_* ν^*` on a sheaf placed in degree zero: naturality and restriction of scalars

Auxiliary statements for
`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso`
(`Rν_* ν^* S ≅ S`):

* `CategoryTheory.Adjunction.iso_hom_comp_eq_map_comp_iso_hom`: isomorphisms `G N ≅ M` whose
  inverse is `M ⟶ G F M ⟶ G N` for an adjunction `F ⊣ G` are natural;
* `CategoryTheory.map_iso_hom_eq_mateEquiv_app_comp`: such isomorphisms are compatible with
  functors commuting with the left adjoints, through the mate of the commutation;
* `CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_singleFunctor`: the isomorphism
  induced on derived categories by a square of exact functors is, in degree zero, the given one;
* `AlgebraicGeometry.ProEtale.map_mapDerivedCategorySingleFunctor_hom_app_comp_restrictScalars`:
  the instance of the latter for the commutation of `ν^*` with the restriction of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor


namespace CategoryTheory

/-- Isomorphisms `e₁ : G N₁ ≅ M₁`, `e₂ : G N₂ ≅ M₂` whose inverses are `M ⟶ G F M ⟶ G N` for an
adjunction `F ⊣ G` are natural with respect to compatible morphisms `M₁ ⟶ M₂`, `N₁ ⟶ N₂`. -/
lemma Adjunction.iso_hom_comp_eq_map_comp_iso_hom {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M₁ M₂ : C} {N₁ N₂ : D} (e₁ : G.obj N₁ ≅ M₁)
    (e₂ : G.obj N₂ ≅ M₂) (ψ₁ : F.obj M₁ ⟶ N₁) (ψ₂ : F.obj M₂ ⟶ N₂)
    (h₁ : e₁.inv = adj.unit.app M₁ ≫ G.map ψ₁) (h₂ : e₂.inv = adj.unit.app M₂ ≫ G.map ψ₂)
    (f : M₁ ⟶ M₂) (f' : N₁ ⟶ N₂) (hf : F.map f ≫ ψ₂ = ψ₁ ≫ f') :
    e₁.hom ≫ f = G.map f' ≫ e₂.hom := by
  rw [← cancel_epi e₁.inv, Iso.inv_hom_id_assoc, h₁, Category.assoc, ← G.map_comp_assoc, ← hf,
    G.map_comp, Category.assoc, adj.unit_naturality_assoc, ← reassoc_of% h₂, Iso.inv_hom_id,
    Category.comp_id]

/-- Isomorphisms `e' : G' N ≅ M`, `e : G N₀ ≅ M₀` whose inverses are `M ⟶ G' F' M ⟶ G' N` and
`M₀ ⟶ G F M₀ ⟶ G N₀` for adjunctions `F' ⊣ G'`, `F ⊣ G` are compatible with functors
`Re`, `Rp` commuting with the left adjoints through `α : Re ⋙ F ⟶ F' ⋙ Rp`: `Re e'` is the mate
of `α`, followed by `G` of `Rp N ⟶ N₀`, `e` and `M₀ ≅ Re M`. -/
lemma map_iso_hom_eq_mateEquiv_app_comp {Ee' Ee Pe' Pe : Type*} [Category* Ee'] [Category* Ee]
    [Category* Pe'] [Category* Pe] {F' : Ee' ⥤ Pe'} {G' : Pe' ⥤ Ee'} {F : Ee ⥤ Pe} {G : Pe ⥤ Ee}
    (adj' : F' ⊣ G') (adj : F ⊣ G) (Re : Ee' ⥤ Ee) (Rp : Pe' ⥤ Pe) (α : Re ⋙ F ⟶ F' ⋙ Rp)
    {M : Ee'} {N : Pe'} {M₀ : Ee} {N₀ : Pe} (e' : G'.obj N ≅ M) (e : G.obj N₀ ≅ M₀)
    (ψ' : F'.obj M ⟶ N) (ψ : F.obj M₀ ⟶ N₀) (he' : e'.inv = adj'.unit.app M ≫ G'.map ψ')
    (he : e.inv = adj.unit.app M₀ ≫ G.map ψ) (ρ : Re.obj M ≅ M₀) (κ : Rp.obj N ⟶ N₀)
    (hα : F.map ρ.hom ≫ ψ = α.app M ≫ Rp.map ψ' ≫ κ) :
    Re.map e'.hom = (mateEquiv adj' adj α).app N ≫ G.map κ ≫ e.hom ≫ ρ.inv := by
  have hβ := (mateEquiv adj' adj α).naturality ψ'
  have hu := unit_mateEquiv adj' adj α M
  dsimp only [Functor.comp_map, Functor.comp_obj] at hβ hu
  rw [← cancel_epi (Re.map e'.inv), ← Re.map_comp, Iso.inv_hom_id, Re.map_id, he', Re.map_comp,
    Category.assoc, reassoc_of% hβ, reassoc_of% hu, ← G.map_comp_assoc, ← G.map_comp_assoc,
    Category.assoc, ← hα, G.map_comp_assoc, adj.unit_naturality_assoc, ← reassoc_of% he,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id]


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- The isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` is, on an
object placed in degree zero, `e` placed in degree zero, up to the identifications
`Functor.mapDerivedCategorySingleFunctor`. -/
lemma Functor.mapDerivedCategorySquareIso_hom_app_singleFunctor {A B B' E : Type*} [Category* A]
    [Category* B] [Category* B'] [Category* E] [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (X : A) :
    (Functor.mapDerivedCategorySquareIso e).hom.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
        G₂.mapDerivedCategory.map ((G₁.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G₂.mapDerivedCategorySingleFunctor 0).hom.app (G₁.obj X) =
      F₂.mapDerivedCategory.map ((F₁.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (F₂.mapDerivedCategorySingleFunctor 0).hom.app (F₁.obj X) ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F₁ F₂, Category.assoc,
    Iso.inv_hom_id_app_assoc, Category.assoc]

end CategoryTheory


namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/-- The commutations of the restrictions of scalars with `ν^*`, with the inclusions in degree
zero and the commutation of `ν^*` with the inclusion in degree zero are compatible. -/
lemma map_mapDerivedCategorySingleFunctor_hom_app_comp_restrictScalars
    (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (D(ν^*(X)[ModuleCat.{u + 1} Λ])).map
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).hom.app
          S) ≫
      ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj S) =
    (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj S) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map
        (((ν^*(X)[ModuleCat.{u + 1} Λ']).mapDerivedCategorySingleFunctor 0).hom.app S) ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategorySingleFunctor
          0).hom.app (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((asIso (restrictScalarsCompComparisonUpperStar φ X)).inv.app S) := by
  rw [derivedRestrictScalarsCompComparisonUpperStarIso,
    reassoc_of% (Functor.mapDerivedCategorySquareIso_hom_app_singleFunctor
      (asIso (restrictScalarsCompComparisonUpperStar φ X)) S),
    ← Functor.map_comp]
  simp

end AlgebraicGeometry.ProEtale
