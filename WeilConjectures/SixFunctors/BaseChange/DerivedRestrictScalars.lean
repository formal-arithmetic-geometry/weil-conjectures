/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Restriction of scalars and the derived base change map

Let `φ : Λ →+* Λ'` be a morphism of commutative rings and consider a commutative square of
schemes `g' ≫ f = f' ≫ g`. Restriction of scalars along `φ` is exact and conservative, and it
commutes with the pullbacks (`AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`), the
pushforwards and the derived pushforwards on `D⁺`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). Moreover it carries the
underived base change map over `Λ'` to the one over `Λ`
(`AlgebraicGeometry.Etale.baseChangeMap_app_restrictScalars`). Consequently, for an object
`K ∈ D⁺(X_ét, Λ')`, the derived base change map over `Λ` is an isomorphism at `res K` if and
only if the derived base change map over `Λ'` is one at `K`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_restrictScalars_iff`).

The proof represents `K` by a bounded below complex `I` of injective sheaves of `Λ'`-modules.
The derived base change maps at `I` and at `res I` are computed by the underived base change
maps followed by the units of the derived pushforwards
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_fac_app`), since the terms of `I` are
`f_*`-acyclic, and so are those of `res I`
(`AlgebraicGeometry.Etale.rightAcyclic_lowerStar_restrictScalars_obj`).

This is the change of coefficients in the proof of the proper base change theorem (blueprint
`sk-thm-reduction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

omit [HasSmallSiteSheafify A] in
/-- At a bounded below complex `K` at which the unit `f_* K ⟶ R⁺f_* K` is an isomorphism (for
instance a complex of injectives), the derived base change map is an isomorphism if and only if
the underived base change map `g^* f_* K ⟶ f'_* g'^* K` followed by the unit
`f'_* g'^* K ⟶ R⁺f'_* (g'^* K)` is one. -/
lemma isIso_derivedBaseChangeMapPlus_app_Qh_obj_iff (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A))
    [IsIso ((f)_*[A].rightDerivedFunctorPlusUnit.app K)] :
    IsIso ((derivedBaseChangeMapPlus A sq).app (DerivedCategory.Plus.Qh.obj K)) ↔
      IsIso (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap A sq)).app K) ≫
        (f')_*[A].rightDerivedFunctorPlusUnit.app (((g')^*[A]).mapHomotopyCategoryPlus.obj K)) := by
  rw [← isIso_comp_left_iff (((g)^*[A]).mapDerivedCategoryPlus.map
    ((f)_*[A].rightDerivedFunctorPlusUnit.app K)), derivedBaseChangeMapPlus_fac_app,
    isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff]

end Generic

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

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

section BaseChange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The restriction of scalars of the unit `f_* M ⟶ R⁺f_* M` over `Λ'`, followed by the
comparison `res(R⁺f_* M) ≅ R⁺f_*(res M)`, is the unit over `Λ` at `res M`. -/
lemma restrictScalars_map_rightDerivedFunctorPlusUnit_app (f : X ⟶ Y)
    (M : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        (((f)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctorPlusUnit.app M) ≫
      (rightDerivedLowerStarRestrictScalars φ f).app (DerivedCategory.Plus.Qh.obj M) =
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlusFactorsh.hom.app
        (((f)_*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj M) ≫
      ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusUnit.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj M) ≫
      ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusFactorsh.inv.app
          M) := by
  have := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (lowerStarCompRestrictScalarsIso φ f).hom) M
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, lowerStarCompRestrictScalarsIso,
    Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id] at this
  refine this.trans ?_
  erw [Category.id_comp, Category.id_comp, Category.id_comp]

/-- The compatibility `AlgebraicGeometry.Etale.baseChangeMap_app_restrictScalars` of the base
change maps with restriction of scalars, applied degreewise to a bounded below complex. -/
lemma mapHomotopyCategoryPlus_baseChangeMap_restrictScalars (sq : CommSq g' f' f g)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ) sq)).app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomotopyCategoryPlus.obj K) ≫
      ((f')_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (upperStarRestrictScalars φ g').natTrans).app K) =
    (NatTrans.mapHomotopyCategoryPlus (upperStarRestrictScalars φ g).natTrans).app
        (((f)_*[ModuleCat.{u + 1} Λ']).mapHomotopyCategoryPlus.obj K) ≫
      (Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (baseChangeMap (ModuleCat.{u + 1} Λ') sq)).app K) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  obtain ⟨⟨K⟩, hK⟩ := K
  have e₁ : ∀ {M N : HomotopyCategory.Plus (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (ψ : M ⟶ N), (HomotopyCategory.Plus.ι _).map
        (((f')_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategoryPlus.map ψ) =
      (((f')_*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.Plus.ι _).map ψ) := fun _ ↦ rfl
  have e₂ : ∀ {M N : HomotopyCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
      (ψ : M ⟶ N), (HomotopyCategory.Plus.ι _).map
        ((Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapHomotopyCategoryPlus.map ψ) =
      ((Sheaf.restrictScalars Y'.smallEtaleTopology φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((HomotopyCategory.Plus.ι _).map ψ) := fun _ ↦ rfl
  rw [Functor.map_comp, Functor.map_comp, e₁, e₂, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map _ =
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  exact baseChangeMap_app_restrictScalars φ sq (K.X n)

end BaseChange

end Etale

end AlgebraicGeometry
