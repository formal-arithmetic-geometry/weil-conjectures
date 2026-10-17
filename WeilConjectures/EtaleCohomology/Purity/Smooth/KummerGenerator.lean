/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-!
# Detecting generators of direct images at geometric points

Tools to show that a class `κ ∈ Hom(Λ_X, K)` on the source of a morphism `π : X ⟶ Y`
generates a cohomology sheaf of `Rπ_* K`, by pulling back to geometric points of `Y`:

* the derived base change map `Lg^* Rπ_* ⟶ Rπ'_* Lg'^*` carries the pullback of the adjoint
  `Λ_Y ⟶ Rπ_* K` of a class to the adjoint of the pulled-back class
  (`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_homEquiv`);
* over a separably closed field, a morphism `β : Λ ⟶ N` with `c • β ≠ 0` for every `c ≠ 0`
  induces a monomorphism `H⁰(β)` (`AlgebraicGeometry.Etale.mono_homologyFunctor_zero_map`);
* over a separably closed field, a monomorphism of sheaves between sheaves with finite global
  sections of the same cardinality is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_of_mono_of_card_sections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Mate

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived base change map carries the pullback of the adjoint `M ⟶ Rf_* K` of a morphism
`α : Lf^* M ⟶ K` to the adjoint of the pulled-back morphism `Lf'^* Lg^* M ≅ Lg'^* Lf^* M ⟶
Lg'^* K`. -/
lemma derivedBaseChangeMap_app_homEquiv (sq : CommSq g' f' f g)
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (α : (L((f)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ K) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ α) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').homEquiv _ _
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app M ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map α) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have h := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).naturality α
  simp only [Functor.comp_map] at h
  rw [h, ← Category.assoc, map_unit_derivedBaseChangeMap_app, Category.assoc,
    ← Functor.map_comp]

end Mate

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K]

/-- The global sections functor on `Spec K`, `K` separably closed: an equivalence. -/
local notation "Γ₀" => (sheafSections (Spec (.of K)).smallEtaleTopology
  (ModuleCat.{u + 1} Λ)).obj (op (etalePoint K))

/-- Over a separably closed field, a monomorphism of étale sheaves of `Λ`-modules whose
global sections are finite of the same cardinality is an isomorphism. -/
theorem isIso_of_mono_of_card_sections
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : F ⟶ G) [Mono ψ]
    [Finite (Γ₀.obj F)] [Finite (Γ₀.obj G)] (h : Nat.card (Γ₀.obj G) ≤ Nat.card (Γ₀.obj F)) :
    IsIso ψ := by
  have hinj : Function.Injective (Γ₀.map ψ) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : IsIso (Γ₀.map ψ) :=
    (LinearEquiv.ofBijective (Γ₀.map ψ).hom (hinj.bijective_of_nat_card_le h)).toModuleIso.isIso_hom
  exact isIso_of_reflects_iso ψ Γ₀

/-- Over a separably closed field, a morphism `f : Λ ⟶ G` out of the constant sheaf `Λ` with
`c • f ≠ 0` for every `c ≠ 0` is a monomorphism. -/
theorem mono_of_smul_eq_zero
    {G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (constantSheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ) ⟶ G) (hf : ∀ c : Λ, c • f = 0 → c = 0) : Mono f := by
  let E := constantSheafEquivalenceOfIsSepClosed Λ (k := K)
  let η := E.unitIso.app (ModuleCat.of Λ Λ)
  suffices hinj : Function.Injective (Γ₀.map f) from
    Functor.mono_of_mono_map Γ₀ ((ModuleCat.mono_iff_injective _).2 hinj)
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨c, rfl⟩ : ∃ c : Λ, η.hom c = m := ⟨η.inv m, by simp⟩
  have h1 : η.hom c = c • η.hom 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hc : Γ₀.map (c • f) = 0 := by
    ext x
    obtain ⟨d, rfl⟩ : ∃ d : Λ, η.hom d = x := ⟨η.inv x, by simp⟩
    have hd : η.hom d = d • η.hom 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [Functor.map_smul, ModuleCat.hom_smul, LinearMap.smul_apply, hd, map_smul, smul_comm,
      ← map_smul, ← h1, hm]
    simp
  rw [hf c (Γ₀.map_injective (by rw [hc, Functor.map_zero]))]
  simp

end SepClosed

end Etale

end AlgebraicGeometry
