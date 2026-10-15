/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsExchange

/-! # Restriction of coefficients for the bounded below base change map

The coefficient comparisons already present in the live library identify the canonical
exchange maps. Restriction of scalars reflects isomorphisms on homology.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- Restriction of scalars of étale sheaves reflects isomorphisms: it is computed sectionwise,
and restriction of scalars of modules reflects isomorphisms. -/
instance (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).ReflectsIsomorphisms where
  reflects {A B} a h := by
    have (U : X.Etaleᵒᵖ) : IsIso (a.hom.app U) := by
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (a.hom.app U)) :=
        inferInstanceAs (IsIso (((sheafToPresheaf _ _).map
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).map a)).app U))
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars.{u + 1} φ)
    have : ∀ U, IsIso (((sheafToPresheaf _ _).map a).app U) := this
    have : IsIso ((sheafToPresheaf _ _).map a) := NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- Restriction of scalars on the bounded below derived categories reflects isomorphisms: it
commutes with the cohomology sheaves, and restriction of scalars of sheaves reflects
isomorphisms. -/
lemma isIso_restrictScalars_mapDerivedCategoryPlus_map_iff {X : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    (a : K ⟶ L) :
    IsIso ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map a) ↔
      IsIso a := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [DerivedCategory.Plus.isIso_iff] at h ⊢
  intro n
  have := h n
  have : IsIso ((Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((DerivedCategory.Plus.homologyFunctor _ n).map a)) := by
    exact (NatIso.isIso_map_iff
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso n)
      a).2 this
  exact isIso_of_reflects_iso _ (Sheaf.restrictScalars X.smallEtaleTopology φ)

variable {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical base change map is invertible after restricting coefficients exactly
when the original map is invertible. -/
theorem isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K)) ↔
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ') sq.toCommSq).app K) := by
  have w := derivedBaseChange_restrictScalars_exchange φ sq K
  simp only [baseChange_eq_derivedBaseChangeMapPlus] at w
  rw [← isIso_restrictScalars_mapDerivedCategoryPlus_map_iff φ,
    ← isIso_comp_left_iff (derivedBaseChangeSourceRestrictScalarsIso φ g f K).hom,
    w, isIso_comp_right_iff]

end AlgebraicGeometry.Etale
