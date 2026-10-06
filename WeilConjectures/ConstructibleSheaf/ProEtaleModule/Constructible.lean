/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Pullback

/-!

# Lisse and constructible sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`, so that `R`-module objects are the sheaves of
`R`-modules on `X_proét`.

## Local conditions

* `ProEtale.IsLisse R M`: `M` is *locally free of finite rank*, i.e. there is a pro-étale
  cover `{Uᵢ ⟶ X}` with `M|_{Uᵢ} ≅ (R|_{Uᵢ})^{rᵢ}`. For `R = E_X` such sheaves are the lisse
  `E`-sheaves (`E`-local systems).
* `ProEtale.IsLocallyTensorOfFinitePresentation φ M`, for a ring homomorphism
  `φ : Λ →+* Γ R` from an abstract ring `Λ` to the global sections of `R` (for instance
  `𝒪_E ⟶ Γ(X, 𝒪_{E,X})`): there is a pro-étale cover `{Uᵢ ⟶ X}` with `M|_{Uᵢ} ≅ Λᵢ ⊗_Λ R|_{Uᵢ}`
  for finitely presented `Λ`-modules `Λᵢ`. Torsion is allowed: `Λᵢ` need not be free.

## Constructibility

Constructibility is defined with respect to a finite stratification `X = ∐ₐ Xₐ` by locally
closed subschemes, using the existing notion `Scheme.Stratification` (`ConstructibleSheaf.Defs`);
restriction to a stratum is the pullback along its immersion `Xₐ ⟶ X`.

* `ProEtale.IsConstructibleLisse R M`: there is a stratification such that every `M|_{Xₐ}` is
  lisse. For `R = E_X` these are the constructible `E`-sheaves.
* `ProEtale.IsConstructibleOfFinitePresentation φ M`: there is a stratification such that every
  `M|_{Xₐ}` is pro-étale locally of the form `Λₐ ⊗_Λ R` with `Λₐ` finitely presented. For
  `R = 𝒪_{E,X}` and `φ : 𝒪_E ⟶ Γ(X, 𝒪_{E,X})` these are the constructible `𝒪_E`-sheaves.

-/

@[expose] public section

universe w u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

section Local

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *lisse* (locally free of finite rank) if it is
pro-étale locally isomorphic to a free module of finite rank. -/
def IsLisse (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFree ((ProEtale.upperStar A (𝒰.f i)).obj R) ((modPullback (𝒰.f i) R).obj M)

/-- Given a ring homomorphism `φ : Λ →+* Γ R`, a sheaf of `R`-modules on `X_proét` is *locally
of the form `Λ' ⊗_Λ R` for finitely presented `Λ'`* if it is so on the members of a pro-étale
cover. -/
def IsLocallyTensorOfFinitePresentation {Λ : Type w} [Ring Λ] (φ : Λ →+* Γ R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsTensorOfFinitePresentation ((ProEtale.upperStar A (𝒰.f i)).obj R)
      ((ΓPullback (𝒰.f i) R).comp φ) ((modPullback (𝒰.f i) R).obj M)

end Local

section Constructible

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *constructible* (in the lisse sense) if its
restrictions to the strata of some finite stratification of `X` are lisse. -/
def IsConstructibleLisse (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    IsLisse ((ProEtale.upperStar A (S.immersion a)).obj R)
      ((modPullback (S.immersion a) R).obj M)

/-- Given a ring homomorphism `φ : Λ →+* Γ R`, a sheaf of `R`-modules on `X_proét` is
*constructible* (in the finitely presented sense) if its restrictions to the strata of some
finite stratification of `X` are pro-étale locally of the form `Λ' ⊗_Λ R` for finitely
presented `Λ`-modules `Λ'`. -/
def IsConstructibleOfFinitePresentation {Λ : Type w} [Ring Λ] (φ : Λ →+* Γ R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    IsLocallyTensorOfFinitePresentation ((ProEtale.upperStar A (S.immersion a)).obj R)
      ((ΓPullback (S.immersion a) R).comp φ) ((modPullback (S.immersion a) R).obj M)

end Constructible

end AlgebraicGeometry.ProEtale
