/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BoundedWithHomology
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Constructible

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of sheaves
of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
Its *bounded constructible* part is the full subcategory of complexes `K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval;
2. every cohomology sheaf `Hⁱ(K)` is constructible.

Morphisms are computed in `D(X_proét, R)`. Following the two notions of constructibility of
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.Constructible`:

* `ProEtale.DerivedCategoryConsLisse R`, with constructible meaning lisse on the strata of a
  stratification. For `R = E_X` with `E/ℚ_ℓ` algebraic, this is `D_cons(X_proét, E)`.
* `ProEtale.DerivedCategoryConsOfFinitePresentation φ`, for a ring homomorphism
  `φ : Λ →+* Γ R`, with constructible meaning pro-étale locally of the form `Λ' ⊗_Λ R` with `Λ'`
  finitely presented on the strata of a stratification. For `R = 𝒪_{E,X}` and
  `φ : 𝒪_E ⟶ Γ(X, 𝒪_{E,X})`, this is `D_cons(X_proét, 𝒪_E)`.

No derived completeness condition is imposed.

## Sorried input

Both subcategories are triangulated (`ProEtale.isTriangulated_boundedConstructibleLisse`,
`ProEtale.isTriangulated_boundedConstructibleOfFinitePresentation`). This rests on the fact that
constructible sheaves form a weak Serre subcategory (closed under kernels, cokernels and
extensions) of the sheaves of `R`-modules, which is not formalized; both instances are
`sorry`ed. The derived category itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe w u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

/-- The bounded complexes of sheaves of `R`-modules on `X_proét` whose cohomology sheaves are
constructible in the lisse sense. -/
noncomputable def boundedConstructibleLisse :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.boundedWithHomology (IsConstructibleLisse R)

/-- The bounded constructible derived category `D_cons(X_proét, R)`, with constructible
meaning lisse on the strata of a stratification. -/
abbrev DerivedCategoryConsLisse : Type _ := (boundedConstructibleLisse R).FullSubcategory

/-- The bounded constructible complexes (lisse sense) form a triangulated subcategory. -/
instance isTriangulated_boundedConstructibleLisse :
    (boundedConstructibleLisse R).IsTriangulated :=
  sorry

variable {Λ : Type w} [Ring Λ] {R} (φ : Λ →+* Γ R)

/-- The bounded complexes of sheaves of `R`-modules on `X_proét` whose cohomology sheaves are
constructible in the finitely presented sense, relative to `φ : Λ →+* Γ R`. -/
noncomputable def boundedConstructibleOfFinitePresentation :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.boundedWithHomology (IsConstructibleOfFinitePresentation R φ)

/-- The bounded constructible derived category `D_cons(X_proét, R)` relative to
`φ : Λ →+* Γ R`, with constructible meaning pro-étale locally `Λ' ⊗_Λ R` with `Λ'` finitely
presented on the strata of a stratification. -/
abbrev DerivedCategoryConsOfFinitePresentation : Type _ :=
  (boundedConstructibleOfFinitePresentation φ).FullSubcategory

/-- The bounded constructible complexes (finitely presented sense) form a triangulated
subcategory. -/
instance isTriangulated_boundedConstructibleOfFinitePresentation :
    (boundedConstructibleOfFinitePresentation φ).IsTriangulated :=
  sorry

end AlgebraicGeometry.ProEtale
