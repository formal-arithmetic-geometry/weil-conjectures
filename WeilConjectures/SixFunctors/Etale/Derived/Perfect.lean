/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!

# Perfect complexes of étale sheaves and their coefficient duals

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_ét)` of `A`-valued étale sheaves on `X` is monoidal closed, with tensor
product `- ⊗ᴸ -` and internal hom `RHom(-, -)`.

A complex is *site-perfect* — in the `ℓ`-adic formalism, quasi-isomorphic locally on the small
étale site to a bounded complex of finite projective `Λ_X`-modules — exactly when it is
dualizable for `- ⊗ᴸ -`, and this is how the property is recorded here: a site-perfect complex
is one admitting an exact pairing with another complex, the evaluation and coevaluation of the
pairing being the unit and the counit of the tensor–internal-hom adjunction. The *coefficient
dual* is `K^∨ = RHom(K, Λ_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`: `K ↦ K^∨ = RHom(K, Λ_X)`.
- `AlgebraicGeometry.Etale.DerivedCategory.sitePerfect`: dualizability for `- ⊗ᴸ -`.
- `AlgebraicGeometry.Etale.DerivedCategory.invertible`: the invertible objects, i.e. the
  `⊗ᴸ`-invertible complexes, of which the Tate twists `Λ(m)` are examples.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_coefficientDual`
  (`sk-prop-sf-dualizable-biduality`): biduality and the comparison
  `K^∨ ⊗ᴸ M ≅ RHom(K, M)` for a perfect `K`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_derivedHom_tensor_iso`
  (`sk-lem-sf-twist-interchange`): the internal hom commutes with an invertible twist.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

/-- The coefficient dual `K^∨ = RHom(K, Λ_X)` of a complex of étale sheaves, where `Λ_X` is
the monoidal unit of `D(X_ét)`. -/
noncomputable def coefficientDual :
    (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (RHom(X)[A]).flip.obj (𝟙_ _)

/-- An object of `D(X_ét)` is *site-perfect* if it is dualizable for the derived tensor
product, i.e. if it admits an exact pairing with some other object. In the `ℓ`-adic formalism
this is the class of complexes that are, locally on the small étale site, bounded complexes of
finite projective `Λ`-modules. -/
def sitePerfect : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun K ↦ ∃ K', Nonempty (ExactPairing K K')

/-- An object of `D(X_ét)` is *invertible* if it admits a tensor inverse. The Tate twists
`Λ(m)`, invertible locally constant of rank one, are the examples used in the `ℓ`-adic
formalism. -/
def invertible : ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun T ↦ ∃ T', Nonempty (T ⊗ T' ≅ 𝟙_ _)

variable {A X}

/-- Blueprint `sk-prop-sf-dualizable-biduality`: Biduality of a perfect complex.

For a site-perfect `K` — one that is, locally on the site of `X`, a bounded complex of finite
projective `Λ_X`-modules — the coefficient dual `K^∨` is again site-perfect, the biduality map
`K ⟶ K^∨∨` is an isomorphism, and for every `M` the canonical map
`K^∨ ⊗ᴸ M ⟶ RHom(K, M)` is an isomorphism. -/
theorem nonempty_iso_coefficientDual_coefficientDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : sitePerfect A X K) :
    sitePerfect A X ((coefficientDual A X).obj (op K)) ∧
      Nonempty (K ≅ (coefficientDual A X).obj
        (op ((coefficientDual A X).obj (op K)))) ∧
      ∀ M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
        Nonempty ((coefficientDual A X).obj (op K) ⊗ M ≅ (RHom(X)[A].obj (op K)).obj M) :=
  sorry

/-- Blueprint `sk-lem-sf-twist-interchange`: Internal Hom with an invertible twist.

For a site-perfect `K`, an invertible twist `T` — in the `ℓ`-adic formalism a Tate twist
`Λ(m)_X`, invertible locally constant of rank one — and any `M`, the canonical map
`RHom(K, M ⊗ᴸ T) ⟶ RHom(K, M) ⊗ᴸ T` is an isomorphism. In particular
`RHom(K, Λ_X(m)) ≅ K^∨(m)`. -/
theorem nonempty_derivedHom_tensor_iso
    {K T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : sitePerfect A X K)
    (hT : invertible A X T) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op K)).obj (M ⊗ T) ≅ (RHom(X)[A].obj (op K)).obj M ⊗ T) :=
  sorry

end Etale.DerivedCategory

end AlgebraicGeometry
