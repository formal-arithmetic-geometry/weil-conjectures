/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

/-!

# Lisse and constructible sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme and `R` a
ring object of `Sheaf (Scheme.ProEt.topology X) A`, so that `R`-module objects are the sheaves of
`R`-modules on `X_proét`.

## Local conditions

* `ProEtale.IsLisse R M`: `M` is *locally free of finite rank*, i.e. there is a pro-étale
  cover `{Uᵢ ⟶ X}` with `M|_{Uᵢ} ≅ (R|_{Uᵢ})^{rᵢ}`. For `R = E_X` such sheaves are the lisse
  `E`-sheaves (`E`-local systems).
* `ProEtale.IsLocallyTensor φ P M`, for a ring homomorphism `φ : Λ →+* Γ R` from an abstract
  ring `Λ` to the global sections of `R` (for instance `𝒪_E ⟶ Γ(X, 𝒪_{E,X})`) and a matrix `P`
  over `Λ` presenting the finitely presented `Λ`-module `Λ' = coker P`: `M` is pro-étale
  locally isomorphic to `Λ' ⊗_Λ R`. Torsion is allowed: `Λ'` need not be free.

## Constructibility

Constructibility is defined with respect to a finite stratification `X = ∐ₐ Xₐ` by locally
closed subschemes, using the existing notion `Scheme.Stratification` (`ConstructibleSheaf.Defs`);
restriction to a stratum is the pullback along its immersion `Xₐ ⟶ X`. Restriction along a
morphism `g` of schemes (to a stratum, or to a member of a pro-étale cover) uses only that the
pullback `g^*` of pro-étale sheaves is lax monoidal (`ProEtale.monoidal_upperStar`): it
sends `R` to a ring object `g^* R`, `R`-modules to `g^* R`-modules (`Functor.mapMod`) and
global sections of `R` to global sections of `g^* R` (`MonObj.Γ.mapFunctor`).

`ProEtale.IsConstructible φ M`: there is a stratification and, for each stratum `Xₐ`, a finitely
presented `Λ`-module `Λₐ` such that `M|_{Xₐ}` is pro-étale locally isomorphic to
`Λₐ ⊗_Λ R|_{Xₐ}`. For `R = 𝒪_{E,X}` these are the constructible `𝒪_E`-sheaves; for `R = E_X`
(with `E` a field) they are the constructible `E`-sheaves, lisse on the strata.

-/

@[expose] public section

universe w u' u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- Tensoring with a pro-étale sheaf is right exact, since the tensor product is closed. -/
instance preservesFiniteColimits_tensorLeft {Y : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology Y) A) :
    PreservesFiniteColimits (tensorLeft F) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

section Local

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A sheaf of `R`-modules on `X_proét` is *lisse* (locally free of finite rank) if it is
pro-étale locally isomorphic to a free module of finite rank. -/
def IsLisse (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Mod.IsFree ((ProEtale.upperStar A (𝒰.f i)).obj R)
      (((ProEtale.upperStar A (𝒰.f i)).mapMod R).obj M)

/-- Given a ring homomorphism `φ : Λ →+* Γ R` and a matrix `P` over `Λ` presenting the finitely
presented `Λ`-module `Λ' = coker P`, a sheaf of `R`-modules on `X_proét` is *pro-étale locally
isomorphic to `Λ' ⊗_Λ R`* if there is a pro-étale cover `{Uᵢ ⟶ X}` with
`M|_{Uᵢ} ≅ Λ' ⊗_Λ R|_{Uᵢ} = coker (P : R|_{Uᵢ}^m ⟶ R|_{Uᵢ}^n)` for every `i`. -/
def IsLocallyTensor {Λ : Type w} [Ring Λ] (φ : Λ →+* Γ R) {n m : ℕ}
    (P : Matrix (Fin n) (Fin m) Λ) (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    Nonempty (((ProEtale.upperStar A (𝒰.f i)).mapMod R).obj M ≅
      Mod.cokernelMatrixMap ((ProEtale.upperStar A (𝒰.f i)).obj R)
        (P.map ((Γ.mapFunctor (ProEtale.upperStar A (𝒰.f i)) (R := R)).comp φ)))

end Local

section Constructible

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- Given a ring homomorphism `φ : Λ →+* Γ R`, a sheaf of `R`-modules `C` on `X_proét` is
*constructible* if there is a finite stratification `X = ∐ₐ Xₐ` such that for every stratum
`Xₐ` there is a finitely presented `Λ`-module `Λₐ` (given by a presentation matrix) with
`C|_{Xₐ}` pro-étale locally isomorphic to `Λₐ ⊗_Λ R|_{Xₐ}`.

For `R = 𝒪_{E,X}` and `φ : 𝒪_E ⟶ Γ(X, 𝒪_{E,X})` these are the constructible `𝒪_E`-sheaves.
For `R = E_X` and `φ : E ⟶ Γ(X, E_X)` these are the constructible `E`-sheaves, i.e. the sheaves
whose restrictions to the strata of a stratification are lisse: a finitely presented module
over the field `E` is free, so `Λₐ ⊗_E E_{Xₐ} ≅ E_{Xₐ}^{rₐ}`. -/
def IsConstructible {Λ : Type w} [Ring Λ] (φ : Λ →+* Γ R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    ∃ (n m : ℕ) (P : Matrix (Fin n) (Fin m) Λ),
      IsLocallyTensor ((ProEtale.upperStar A (S.immersion a)).obj R)
        ((Γ.mapFunctor (ProEtale.upperStar A (S.immersion a)) (R := R)).comp φ) P
        (((ProEtale.upperStar A (S.immersion a)).mapMod R).obj M)

end Constructible

end AlgebraicGeometry.ProEtale
