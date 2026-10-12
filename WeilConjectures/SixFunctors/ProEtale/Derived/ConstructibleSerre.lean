/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible

/-!
# Constructible pro-étale sheaves at a finite coefficient ring

Let `Λ` be a finite commutative ring. Following blueprint
`def-weil-pbc-constructible-direct-image-finiteness`, a sheaf `F` of `Λ`-modules on the small
pro-étale site of `T` is *constructible* if `F ≅ ν^* F'` for a constructible étale sheaf `F'`
(`AlgebraicGeometry.ProEtale.constructibleSheaf`). This file shows:

- the bounded constructible pro-étale complexes `Dᵇc_proét(T, Λ)` (the complexes of étale origin
  `ν^* K'`, `K' ∈ Dᵇc(T, Λ)`) form a triangulated subcategory of `D(T_proét)`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_isTriangulated`): the
  extension of two objects of étale origin is of étale origin, because `D(ν^*)` is fully
  faithful on bounded below complexes (`bijective_comparisonUpperStar_mapDerivedCategory_map`);
- an object of `D(T_proét)` is bounded constructible if and only if it is bounded with
  constructible homology sheaves
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_iff_homologyProperty`);
- the constructible pro-étale sheaves are closed under kernels, cokernels and extensions: they
  form a weak Serre subcategory (blueprint `thm-constructible-serre`, transported to the
  pro-étale site through the fully faithful exact functor `ν^*`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- Blueprint `def-weil-pbc-constructible-direct-image-finiteness` (first part): a sheaf `F` of
`Λ`-modules on the small pro-étale site of `X` is *constructible* if `F ≅ ν^* F'` for a
constructible sheaf `F'` of `Λ`-modules on the small étale site of `X`. -/
def constructibleSheaf :
    ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).map ν^*(X)[ModuleCat.{u + 1} Λ]

lemma constructibleSheaf_iff (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    constructibleSheaf Λ X F ↔ ∃ F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsConstructibleSheaf F' ∧ Nonempty ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F' ≅ F) :=
  ObjectProperty.prop_map_iff _ _ _

instance : (constructibleSheaf Λ X).IsClosedUnderIsomorphisms :=
  inferInstanceAs ((Etale.constructibleSheaf _ X).map _).IsClosedUnderIsomorphisms

instance : (constructibleSheaf Λ X).ContainsZero where
  exists_zero := ⟨_, (ν^*(X)[ModuleCat.{u + 1} Λ]).map_isZero (isZero_zero _),
    ObjectProperty.prop_map_obj _ _ ((Etale.constructibleSheaf _ X).prop_of_isZero
      (isZero_zero _))⟩

variable [Finite Λ]

/-- The kernel of a morphism between constructible pro-étale sheaves is constructible: the
morphism is `ν^*` of a morphism of constructible étale sheaves, `ν^*` being full, and `ν^*`
preserves kernels. -/
instance : (constructibleSheaf Λ X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨F, hF, ⟨eF⟩⟩, ⟨G, hG, ⟨eG⟩⟩⟩
    obtain ⟨f', hf'⟩ := (ν^*(X)[ModuleCat.{u + 1} Λ]).map_surjective (eF.hom ≫ f ≫ eG.inv)
    have e : kernel f ≅ (ν^*(X)[ModuleCat.{u + 1} Λ]).obj (kernel f') :=
      (kernel.mapIso _ _ eF.symm eG.symm (by simp [hf'])) ≪≫
        (PreservesKernel.iso (ν^*(X)[ModuleCat.{u + 1} Λ]) f').symm
    exact ⟨_, (Etale.constructibleSheaf _ X).prop_kernel f' hF hG,
      ⟨e.symm ≪≫ IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk⟩⟩

/-- The cokernel of a morphism between constructible pro-étale sheaves is constructible. -/
instance : (constructibleSheaf Λ X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨F, hF, ⟨eF⟩⟩, ⟨G, hG, ⟨eG⟩⟩⟩
    obtain ⟨f', hf'⟩ := (ν^*(X)[ModuleCat.{u + 1} Λ]).map_surjective (eF.hom ≫ f ≫ eG.inv)
    have e : cokernel f ≅ (ν^*(X)[ModuleCat.{u + 1} Λ]).obj (cokernel f') :=
      (cokernel.mapIso _ _ eF.symm eG.symm (by simp [hf'])) ≪≫
        (PreservesCokernel.iso (ν^*(X)[ModuleCat.{u + 1} Λ]) f').symm
    exact ⟨_, (Etale.constructibleSheaf _ X).prop_cokernel f' hF hG,
      ⟨e.symm ≪≫ IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk⟩⟩

/-- **`Dᵇc_proét(X, Λ)` is closed under extensions.** In a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` with `K₁ ≅ ν^* K₁'` and `K₃ ≅ ν^* K₃'` bounded constructible of étale
origin, the connecting morphism is `ν^*` of a morphism `K₃' ⟶ K₁'[1]`, `D(ν^*)` being fully
faithful on bounded below complexes; its cocone `K₂'` is bounded constructible, and `K₂ ≅ ν^* K₂'`
by the uniqueness of cones. -/
instance : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₂ :=
  .mk' fun T hT ⟨K₁, h₁, ⟨e₁⟩⟩ ⟨K₃, h₃, ⟨e₃⟩⟩ ↦ by
    let F := D(ν^*(X)[ModuleCat.{u + 1} Λ])
    -- the connecting morphism, transported to `ν^* K₃ ⟶ ν^* (K₁[1])`
    obtain ⟨f, hf⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map K₃ (K₁⟦(1 : ℤ)⟧)
      (DerivedCategory.TStructure.t.plus.le_shift 1 _ h₁.1.1)).2
      (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' ≫ (F.commShiftIso (1 : ℤ)).inv.app K₁)
    obtain ⟨K₂, a, b, hT'⟩ := distinguished_cocone_triangle₂ f
    have h₂ : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K₂ :=
      (Etale.DerivedCategory.boundedConstructible _ X).ext_of_isTriangulatedClosed₂ _ hT' h₁ h₃
    have hFT := F.map_distinguished _ hT'
    have hc : T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧' =
        e₃.inv ≫ F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app K₁ := by
      rw [show F.map f = _ from hf]
      simp only [Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_assoc]
      exact (Category.comp_id (T.mor₃ ≫ e₁.inv⟦(1 : ℤ)⟧')).symm
    obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism₂ _ _ hT hFT e₁.inv e₃.inv hc
    have : IsIso c := isIso₂_of_isIso₁₃ (Triangle.homMk _ _ e₁.inv c e₃.inv hc₁ hc₂ hc) hT hFT
      (inferInstanceAs (IsIso e₁.inv)) (inferInstanceAs (IsIso e₃.inv))
    exact ⟨K₂, h₂, ⟨(asIso c).symm⟩⟩

instance : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
  ⟨fun n ↦ ⟨fun _ ⟨K', h, ⟨e⟩⟩ ↦ ⟨K'⟦n⟧, (Etale.DerivedCategory.boundedConstructible _ X).le_shift
    n _ h, ⟨(D(ν^*(X)[ModuleCat.{u + 1} Λ]).commShiftIso n).app K' ≪≫
      (shiftFunctor _ n).mapIso e⟩⟩⟩⟩

instance : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).ContainsZero where
  exists_zero := ⟨_, (D(ν^*(X)[ModuleCat.{u + 1} Λ])).map_isZero (isZero_zero _),
    DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      ((Etale.DerivedCategory.boundedConstructible _ X).prop_of_isZero (isZero_zero _))⟩

/-- **`Dᵇc_proét(X, Λ)` is a triangulated subcategory of `D(X_proét)`** at a finite
coefficient ring `Λ`. -/
instance DerivedCategory.boundedConstructible_isTriangulated :
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulated where

variable {Λ X}

omit [Finite Λ] in
/-- The homology sheaves of a bounded constructible pro-étale complex are constructible:
`Hⁿ(ν^* K') ≅ ν^* Hⁿ(K')`, `ν^*` being exact. -/
lemma DerivedCategory.boundedConstructible.homologyProperty
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    _root_.DerivedCategory.homologyProperty (constructibleSheaf Λ X) K := by
  obtain ⟨K', h, ⟨e⟩⟩ := hK
  intro n
  exact (constructibleSheaf Λ X).prop_of_iso
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app K' ≪≫
      (_root_.DerivedCategory.homologyFunctor _ n).mapIso e)
    (ObjectProperty.prop_map_obj _ _ (h.2 n))

/-- **Bounded constructible pro-étale complexes are the bounded complexes with constructible
homology sheaves.** One direction is
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible.homologyProperty`; conversely
a constructible sheaf `ν^* F'` placed in degree `0` is `D(ν^*)` of the bounded constructible
complex `F'[0]`, and `Dᵇc_proét(X, Λ)` is triangulated, so the dévissage of bounded complexes
(`DerivedCategory.prop_of_bounded`) applies. -/
lemma DerivedCategory.boundedConstructible_iff_homologyProperty
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K ↔
      _root_.DerivedCategory.TStructure.t.bounded K ∧
        _root_.DerivedCategory.homologyProperty (constructibleSheaf Λ X) K := by
  refine ⟨fun hK ↦ ⟨hK.bounded, hK.homologyProperty⟩, fun ⟨hb, hK⟩ ↦ ?_⟩
  refine _root_.DerivedCategory.prop_of_bounded _ (constructibleSheaf Λ X) ?_ K hb hK
  rintro _ ⟨F', hF', ⟨e⟩⟩
  have : IsConstructibleSheaf F' := hF'
  exact ⟨_, Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F' 0,
    ⟨((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F' ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩

variable (Λ X)

/-- **Extensions of constructible pro-étale sheaves are constructible.** For a short exact
sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` with `F₁, F₃` constructible, `F₂[0]` is an extension of
`F₃[0]` by `F₁[0]` in `D(X_proét)`, hence of étale origin, and `F₂ = H⁰(F₂[0])` is
constructible. -/
instance : (constructibleSheaf Λ X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have hQ (F) (hF : constructibleSheaf Λ X F) : DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} Λ) X ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
      refine (DerivedCategory.boundedConstructible_iff_homologyProperty _).2
        ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
      by_cases hn : n = 0
      · subst hn
        exact (constructibleSheaf Λ X).prop_of_iso
          ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
      · rcases lt_or_gt_of_ne hn with hn | hn
        · exact (constructibleSheaf Λ X).prop_of_isZero
            (_root_.DerivedCategory.isZero_of_isGE _ 0 _ hn)
        · exact (constructibleSheaf Λ X).prop_of_isZero
            (_root_.DerivedCategory.isZero_of_isLE _ 0 _ hn)
    have h₂ := (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ)
      X).ext_of_isTriangulatedClosed₂
      _ hS.singleTriangle_distinguished (hQ _ h₁) (hQ _ h₃)
    exact (constructibleSheaf Λ X).prop_of_iso
      ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app S.X₂)
      (h₂.homologyProperty 0)

end AlgebraicGeometry.ProEtale
