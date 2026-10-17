/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.OpenClosed.Conservative
public import WeilConjectures.SixFunctors.ProEtale.Comparison.SiteComparison

/-!
# Detecting isomorphisms of étale origin at geometric points

This file proves clause (3) of blueprint `lem-cbc-proetale-stalk-conservative`: for a morphism
`φ : K ⟶ L` of bounded below complexes of étale sheaves of `Λ`-modules on a scheme `X`, the
comparison pullback `ν^* φ` is an isomorphism of `D⁺(X_proét, Λ)` if and only if `φ` is an
isomorphism at every geometric point `x : Spec Ω ⟶ X` of `X`, that is, if and only if all the
pullbacks `x^* φ` are isomorphisms.

The comparison pullback is fully faithful on bounded below complexes
(`AlgebraicGeometry.ProEtale.fullyFaithfulComparisonUpperStarMapDerivedCategoryPlus`), so it
reflects isomorphisms, and the geometric points at algebraic closures of the residue fields
jointly detect isomorphisms of étale sheaves
(`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`), hence of bounded
below complexes, by passing to cohomology sheaves.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Isomorphisms of `D⁺(X_ét, Λ)` are detected at the geometric points `x : Spec Ω ⟶ X` of `X`
with separably closed `Ω`. -/
theorem isIso_iff_forall_isIso_mapDerivedCategoryPlus_upperStar_map
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ L) :
    IsIso φ ↔ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
      IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlus.map φ) := by
  refine ⟨fun _ _ _ _ _ ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun s : X ↦ X.algClosurePoint s) (fun s ↦ ⟨s, default, by simp⟩) _ fun s ↦ ?_
  exact (NatIso.isIso_map_iff ((Etale.upperStar (ModuleCat.{u + 1} Λ)
    (X.algClosurePoint s)).mapDerivedCategoryPlusHomologyFunctorIso n) φ).2 (Functor.map_isIso (DerivedCategory.Plus.homologyFunctor _ n) _)

/-- Blueprint `lem-cbc-proetale-stalk-conservative` (3): *complexes of étale origin*.

Let `φ : K ⟶ L` be a morphism of bounded below complexes of étale sheaves of `Λ`-modules on
`X`. Then `ν^* φ` is an isomorphism of `D⁺(X_proét, Λ)` if and only if `φ` is an isomorphism at
every geometric point `x : Spec Ω ⟶ X`, that is, `x^* φ` is an isomorphism for every separably
closed field `Ω` and every `x`. -/
theorem isIso_mapDerivedCategoryPlus_comparisonUpperStar_map_iff
    {K L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ L) :
    IsIso (D+(ν^*(X)[ModuleCat.{u + 1} Λ]).map φ) ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) x).mapDerivedCategoryPlus.map φ) := by
  rw [← isIso_iff_forall_isIso_mapDerivedCategoryPlus_upperStar_map]
  exact ⟨fun _ ↦ isIso_of_fully_faithful D+(ν^*(X)[ModuleCat.{u + 1} Λ]) φ,
    fun _ ↦ inferInstance⟩

end AlgebraicGeometry.ProEtale
