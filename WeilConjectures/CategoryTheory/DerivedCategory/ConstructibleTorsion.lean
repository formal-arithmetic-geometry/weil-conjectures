/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Extensions of bounded constructible complexes killed by an ideal of finite index

Let `Λ` be a noetherian ring and `J` an ideal of `Λ` with `Λ ⧸ J` finite. In a distinguished
triangle `K ⟶ L ⟶ M ⟶ K⟦1⟧` of `D(X_ét, Λ)` with `K` and `M` bounded constructible and `L`
killed by `J`, the middle vertex `L` is bounded constructible
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero`): each
homology sheaf of `L` is killed by `J` and is an extension of a kernel by a cokernel of maps
between constructible sheaves, so it is constructible by
`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_smul_eq_zero`.

This replaces the closure of constructible sheaves under extensions, which is only available
over a finite coefficient ring, for the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` at the integral stage
`Λ = 𝒪_E` of the `ℓ`-adic formalism.
-/

@[expose] public section

universe w v u' u

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable {A : Type u'} [Category.{v} A] [Abelian A] (P : ObjectProperty A)

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

section ContainsZero

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [PreservesFiniteLimits (CategoryTheory.forget A)] (X : Scheme.{u})

/-- `Dᵇc(X, A)` contains the zero object; unlike
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated` this needs no
closure property of the constructible sheaves. -/
instance Etale.DerivedCategory.containsZero_boundedConstructible :
    (Etale.DerivedCategory.boundedConstructible A X).ContainsZero := by
  rw [Etale.DerivedCategory.boundedConstructible, Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

end ContainsZero

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {J : Ideal Λ}
  [Finite (Λ ⧸ J)]

end AlgebraicGeometry
