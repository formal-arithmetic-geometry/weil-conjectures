/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.Extension
public import WeilConjectures.SixFunctors.ProEtale.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.Constructible

/-!
# The integral and rational bounded constructible categories

Let `T` be a scheme, `E` a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, `𝒪_E` its ring of integers
and `𝔪_E` its maximal ideal. This file defines the categories

```
  D^b_c(T_proét, 𝒪_E) ⊆ D(T_proét, 𝒪_E)       and       D^b_c(T, E) = D^b_c(T_proét, 𝒪_E)[1/ϖ]
```

of the blueprint (`def-weil-pbc-bounded-constructible-complete` and
`def-weil-pbc-rational-category`, subsection `sk-thm-properbasechange`).

An object `K` of `D(T_proét, 𝒪_E)` lies in `D^b_c(T_proét, 𝒪_E)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleComplete`) if it is derived
complete for `𝔪_E` (`DerivedCategory.derivedCompleteIntegral`), bounded, and its reductions
`K_n = K ⊗ᴸ 𝒪_E/𝔪_Eⁿ⁺¹` are bounded constructible of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`) with cohomology in one
common interval `[a, b]`. These objects form a triangulated subcategory
(`AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructibleComplete`), and
`D^b_c(T, E)` is its rationalization (`CategoryTheory.Rationalization`): the Verdier quotient
by the objects killed by a nonzero element of `𝒪_E`, whose morphisms are the fractions `g / m`
(`CategoryTheory.Rationalization.exists_smul_eq_map`), so that
`Hom(K, L)[1/ϖ] = Hom(K, L) ⊗_{𝒪_E} E`.

## Implementation notes

The blueprint takes the coefficients to be modules over the pro-étale sheaf of rings
`A_T = lim_n (𝒪_E/𝔪_Eⁿ)_T`, and records the reductions as a tower with local models
(`def-weil-pbc-bounded-constructible-tower`). Here, as in the rest of the repository
(`DerivedCategoryDerivedCompleteIntegral`), the coefficients are the sheaves of
`𝒪_E`-modules, and the derived complete objects are taken in their derived category: a
derived complete complex is the derived limit of its reductions, which are modules over the
finite rings `𝒪_E/𝔪_Eⁿ`, so it carries the structure of a complex of `A_T`-modules. The
uniformly bounded constructible tower is recorded through its consequences: the reductions
are bounded constructible of étale origin with cohomology in one interval `[a, b]`, and `K`
itself is bounded (by the uniform-tower reconstruction `lem-weil-pbc-reconstruction-uniform-tower`
this is a consequence of the tower condition).

Constructibility of the reductions is that of sheaves of `𝒪_E`-modules, whose stalks are
finitely generated `𝒪_E`-modules killed by a power of `𝔪_E`, hence finite. Extensions of such
sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_isNoetherianRing`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

/-- Constructible sheaves of modules over a noetherian ring are closed under extensions
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_isNoetherianRing`). -/
instance Etale.isClosedUnderExtensions_constructibleSheaf (X : Scheme.{u}) :
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := (Etale.constructibleSheaf_iff _ _ _).mp h₁
    have := (Etale.constructibleSheaf_iff _ _ _).mp h₃
    exact (Etale.constructibleSheaf_iff _ _ _).mpr
      (Scheme.IsConstructibleSheaf.of_shortExact_of_isNoetherianRing hS)

namespace ProEtale.DerivedCategory

/-- Over a noetherian coefficient ring, the bounded constructible pro-étale complexes (those of
étale origin) form a triangulated subcategory of `D(X_proét)`: the cone of a map between
complexes of étale origin is `ν^*` of the cone of a lift of this map, since `ν^*` is
triangulated and fully faithful on bounded below complexes
(`AlgebraicGeometry.ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`). -/
instance isTriangulated_boundedConstructible_of_isNoetherianRing (X : Scheme.{u}) :
    (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulated := by
  let F := D(ν^*(X)[ModuleCat.{u + 1} Λ])
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₃ := by
    refine ObjectProperty.IsTriangulatedClosed₃.mk' fun T hT ⟨A, hA, ⟨e₁⟩⟩ ⟨B, hB, ⟨e₂⟩⟩ ↦ ?_
    obtain ⟨f, hf⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map A B hB.1.1).2
      (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    obtain ⟨Z, g, h, hZ⟩ := Pretriangulated.distinguished_cocone_triangle f
    obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ T
      (F.map_distinguished _ hZ) hT (Arrow.isoMk e₁ e₂ (by
        have hf' : F.map f = e₁.hom ≫ T.mor₁ ≫ e₂.inv := hf
        change e₁.hom ≫ T.mor₁ = F.map f ≫ e₂.hom
        simp [hf']))
    exact ⟨Z, (Etale.DerivedCategory.boundedConstructible _ X).ext_of_isTriangulatedClosed₃ _
      hZ hA hB, ⟨Pretriangulated.Triangle.π₃.mapIso e⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun K ⟨A, hA, ⟨e⟩⟩ ↦ ⟨A⟦n⟧,
      (Etale.DerivedCategory.boundedConstructible _ X).le_shift n _ hA,
      ⟨(F.commShiftIso n).app A ≪≫ (shiftFunctor _ n).mapIso e⟩⟩⟩⟩
  have : (boundedConstructible (ModuleCat.{u + 1} Λ) X).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  obtain ⟨Z, hZ, hZP⟩ := ObjectProperty.ContainsZero.exists_zero
    (P := Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X)
  exact { exists_zero := ⟨F.obj Z, F.map_isZero hZ,
    boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hZP⟩ }

end ProEtale.DerivedCategory

end AlgebraicGeometry
