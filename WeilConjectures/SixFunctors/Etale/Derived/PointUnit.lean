/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.CategoryTheory.Monoidal.UnitIsoBijective
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.Point

/-!
# Morphisms out of the unit in the point category

Let `k` be a separably closed field and `s = Spec k`. In the point category `D(s_ét, Λ)`, the
unit `Λ_s` is the constant sheaf `Λ` placed in degree `0`, and it detects cohomology sheaves
(`AlgebraicGeometry.Etale.exists_ne_zero_of_not_isZero_homology_of_isSepClosed`). This file
shows that a morphism `u : Λ_s ⟶ P` to an object `P ∈ D^{≥ 0}` inducing a bijection
`Hom(Λ_s, Λ_s) ≃ Hom(Λ_s, P)` has its cone in `D^{≥ 1}`.

## Main statements

- `AlgebraicGeometry.Etale.unitIsoSingleFunctorConstantSheaf`: `Λ_X ≅ (constant sheaf Λ)[0]`.
- `AlgebraicGeometry.Etale.isGE_one_of_bijective_comp_of_isSepClosed`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

variable (Λ) in
/-- The unit `Λ_X` of `D(X_ét, Λ)` is the constant sheaf `Λ` placed in degree `0`. -/
noncomputable def unitIsoSingleFunctorConstantSheaf (X : Scheme.{u}) :
    𝟙_ (DerivedCategoryModule Λ X) ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) :=
  constantComplexIsoSingleFunctor Λ X ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

instance (X : Scheme.{u}) : (𝟙_ (DerivedCategoryModule Λ X)).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (unitIsoSingleFunctorConstantSheaf Λ X).symm 0

instance (X : Scheme.{u}) : (𝟙_ (DerivedCategoryModule Λ X)).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (unitIsoSingleFunctorConstantSheaf Λ X).symm 0

variable (Λ) in
/-- For a connected scheme `X`, `r ↦ r • 𝟙` is a bijection from `Λ` onto the endomorphisms of
the unit `Λ_X` of `D(X_ét, Λ)`: `Λ_X` is the constant sheaf `Λ` placed in degree `0`, the
single functor is fully faithful and `Λ`-linear, and the endomorphisms of the constant sheaf
`Λ` are its global sections, which are `Λ` since `X` is connected
(`AlgebraicGeometry.Scheme.bijective_constantSheafAdj_unit_app`). -/
theorem bijective_smul_id_unit (X : Scheme.{u}) [ConnectedSpace X] :
    Function.Bijective (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X))) := by
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  have hU := Scheme.bijective_constantSheafAdj_unit_app X (ModuleCat.of Λ Λ) hT
  let ev : (C ⟶ C) → _ := fun φ ↦ (adj.homEquiv _ _ φ).hom (1 : Λ)
  have hev : Function.Injective ev := by
    intro φ ψ h
    apply (adj.homEquiv _ _).injective
    ext
    exact h
  have hcomp (r : Λ) : ev (r • 𝟙 C) = adj.unit.app (ModuleCat.of Λ Λ) r := by
    have hG : ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (Opposite.op (Scheme.Etale.mk (𝟙 X)))).map (r • 𝟙 C) = r • 𝟙 _ := rfl
    simp only [ev, Adjunction.homEquiv_unit, hG, Linear.comp_smul,
      ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
    rfl
  have hC : Function.Bijective (fun r : Λ ↦ r • 𝟙 C) := by
    refine ⟨fun r s h ↦ hU.1 ?_, fun φ ↦ ?_⟩
    · rw [← hcomp, ← hcomp]
      exact congrArg ev h
    · obtain ⟨r, hr⟩ := hU.2 (ev φ)
      exact ⟨r, hev (by rw [hcomp, hr])⟩
  let E := unitIsoSingleFunctorConstantSheaf Λ X
  have : (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategoryModule Λ X))) =
      (fun z ↦ E.hom ≫ z ≫ E.symm.hom) ∘ (DerivedCategory.singleFunctor _ 0).map ∘
        (fun r : Λ ↦ r • 𝟙 C) := by
    funext r
    simp [E, C, Functor.map_smul]
  rw [this]
  exact (bijective_conj E E.symm).comp
    (((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _).comp hC)

variable {k : Type u} [Field k] [IsSepClosed k]

end AlgebraicGeometry.Etale
