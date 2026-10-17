/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-!
# Cohomology with supports and the exceptional inverse image of a closed immersion

For a closed immersion `i : Z ⟶ X` the cohomology with supports `H^a_Z(X, K)` of
`AlgebraicGeometry.Etale.derivedSupportCohomology` is `Hom(Λ_Z, Ri^!(K[a]))`
(`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`): by `H^a_Z(X, K) ≅ Hom(i_* Λ_Z, K[a])`
(`AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`), `i_* Λ_Z ≅ Ri_! Λ_Z` and the
adjunction `Ri_! ⊣ Ri^!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section SupportHom

variable [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- `Ri_! Λ_Z ≅ i_* Λ_Z`, placed in degree zero, for a closed immersion `i`. -/
noncomputable def rightDerivedLowerShriekConstantComplexIso :
    (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app _ ≪≫
    (rightDerivedFunctorLowerStarIsoMapDerivedCategory _ i).app _ ≪≫
    ((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.mapIso (constantComplexIsoSingleFunctor Λ Z) ≪≫
    (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _

/-- Blueprint `lem-pur-gysin-structure`: Structure of the exceptional inverse image of the zero
section (the identification of cohomology with supports with morphisms into `Ri^!`).

For a closed immersion `i : Z ⟶ X`, the cohomology with supports is
`H^a_Z(X, K) ≅ Hom(Λ_Z, Ri^!(K[a]))`. -/
noncomputable def supportCohomologyAddEquiv
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K ≃+
      (constantComplex Λ Z ⟶ (R(i)^![ModuleCat.{u + 1} Λ]).obj (K⟦a⟧)) :=
  (derivedSupportCohomologyAddEquiv Λ i K a).trans
    ((AddEquiv.mk ((rightDerivedLowerShriekConstantComplexIso Λ i).homCongr
      (Iso.refl (K⟦a⟧))).symm (fun f g ↦ by simp [Iso.homCongr])).trans
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).homAddEquiv _ _))

end SupportHom

section Endomorphisms

variable {Z : Scheme.{u}}

/-- On a connected scheme, the endomorphisms of the constant complex `Λ_Z` are the scalars. -/
theorem bijective_smul_id_constantComplex [Finite Λ] [ConnectedSpace Z] :
    Function.Bijective (fun c : Λ ↦ c • 𝟙 (constantComplex Λ Z)) := by
  let S := _root_.DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  let P := (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  let e : constantComplex Λ Z ≅ S.obj P := constantComplexIsoSingleFunctor Λ Z
  have hS : ∀ c : Λ, c • 𝟙 (constantComplex Λ Z) = e.hom ≫ S.map (c • 𝟙 P) ≫ e.inv := by
    intro c
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, e.hom_inv_id]
  constructor
  · intro c c' h
    simp only at h
    rw [hS, hS] at h
    have h' : S.map (c • 𝟙 P) = S.map (c' • 𝟙 P) := by
      simpa using congrArg (fun φ ↦ e.inv ≫ φ ≫ e.hom) h
    have h'' := S.map_injective h'
    have hz : (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((c - c') • 𝟙 (ModuleCat.of Λ Λ)) = 0 := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, sub_smul]
      exact sub_eq_zero.2 h''
    have := (ConnectedSpace.toNonempty (α := Z))
    have h0 := eq_zero_of_constantSheaf_map_eq_zero Λ _ hz
    have h1 := congrArg (fun φ : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ ↦ φ.hom (1 : Λ)) h0
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply,
      smul_eq_mul, mul_one, ModuleCat.hom_zero, LinearMap.zero_apply] at h1
    exact sub_eq_zero.1 h1
  · intro f
    obtain ⟨c, hc⟩ := exists_eq_smul_id_constantSheaf Λ (S.preimage (e.inv ≫ f ≫ e.hom))
    refine ⟨c, ?_⟩
    simp only
    rw [hS, ← hc, S.map_preimage]
    simp

end Endomorphisms

end Etale

end AlgebraicGeometry
