/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# External products and the Künneth formulas on the étale site

Let `A` be a monoidal Grothendieck abelian coefficient category. For two schemes `X`, `Y` over
a base `B`, with projections `p : X ×_B Y ⟶ X` and `q : X ×_B Y ⟶ Y`, the *external product*
of `K ∈ D(X_ét)` and `M ∈ D(Y_ét)` is

`K ⊠ M = Lp^* K ⊗ᴸ Lq^* M ∈ D((X ×_B Y)_ét)`.

This file introduces the external product and states the Künneth package of the six-functor
formalism: the ordinary Künneth formula with an identity factor, the relative product theorem
for `Rf_!`, the four product comparison maps, and the Künneth–Verdier isomorphism.

Since constructing the canonical comparison maps is out of scope here, all comparisons are
stated in the form `Nonempty (_ ≅ _)`, following the convention of this development. The
absolute case of a product over the base `S` is the special case `B = S` of the definitions
below.

## Main definitions

- `AlgebraicGeometry.Etale.externalProduct`: `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M`.
- `AlgebraicGeometry.Etale.pullbackToBase`: the structure morphism `f ×_B g : X ×_B Y ⟶ B`.
- `AlgebraicGeometry.Etale.prodMapOver`: the product `f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂`.
- `AlgebraicGeometry.Etale.prodMapRight`: the product `f × id_Z : X ×_S Z ⟶ Y ×_S Z`.
- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`sk-def-sf-kv-maps`): the conjunction of
  the four product comparison assertions `Ku_!`, `α`, `β`, `κ`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`sk-lem-sf-kunneth-star`): `Rf_* L ⊠ Q ≅ R(f × id_Z)_* (L ⊠ Q)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
  (`sk-thm-sf-kunneth-relative`): `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`.
- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`sk-thm-sf-kunneth-verdier`): the four
  comparison maps are isomorphisms.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_verdierDual`
  (`sk-thm-sf-kunneth-verdier`): `M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Definitions

variable {S B X Y Z X₁ X₂ Y₁ Y₂ : Scheme.{u}}

/-- The external product `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M` of `K ∈ D(X_ét)` and `M ∈ D(Y_ét)`,
an object of `D((X ×_B Y)_ét)`, where `p : X ×_B Y ⟶ X` and `q : X ×_B Y ⟶ Y` are the two
projections of the fibre product of `f : X ⟶ B` and `g : Y ⟶ B`.

The absolute external product over a base scheme `S` is the case where `f` and `g` are the
structure morphisms of `X` and `Y`. -/
noncomputable def externalProduct (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    _root_.DerivedCategory (Sheaf (pullback f g).smallEtaleTopology A) :=
  (L((pullback.fst f g)^*[A])).obj K ⊗ (L((pullback.snd f g)^*[A])).obj M

/-- The structure morphism `f ×_B g : X ×_B Y ⟶ B` of the fibre product, the common composite
of either projection with the corresponding leg. -/
noncomputable def pullbackToBase (f : X ⟶ B) (g : Y ⟶ B) : pullback f g ⟶ B :=
  pullback.fst f g ≫ f

/-- The product `f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂` of two morphisms `f₁ : X₁ ⟶ Y₁` and
`f₂ : X₂ ⟶ Y₂` over a base `S`, where `X₁` and `X₂` are viewed over `S` through
`f₁ ≫ b₁` and `f₂ ≫ b₂`. -/
noncomputable def prodMapOver (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    pullback (f₁ ≫ b₁) (f₂ ≫ b₂) ⟶ pullback b₁ b₂ :=
  pullback.map _ _ _ _ f₁ f₂ (𝟙 S) (by simp) (by simp)

/-- The product `f × id_Z : X ×_S Z ⟶ Y ×_S Z` of a morphism `f : X ⟶ Y` with the identity of
a further scheme `Z` over `S`, where `X` is viewed over `S` through `f ≫ b`. -/
noncomputable def prodMapRight (b : Y ⟶ S) (c : Z ⟶ S) (f : X ⟶ Y) :
    pullback (f ≫ b) c ⟶ pullback b c :=
  pullback.map _ _ _ _ f (𝟙 Z) (𝟙 S) (by simp) (by simp)

end Definitions

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `sk-lem-sf-kunneth-star`: Ordinary Künneth with an identity factor.

Let `f : X ⟶ Y` be a separated morphism of finite type between schemes over a base `S`, where
`X` is viewed over `S` through `f ≫ b`, and let `c : Z ⟶ S` be a further such scheme. For
`M` on `X` and `Q` on `Z` bounded constructible of finite Tor amplitude — that is, objects of
`Dctf(X, A)` and `Dctf(Z, A)` — the canonical comparison

`Rf_* M ⊠ Q ⟶ R(f × id_Z)_* (M ⊠ Q)`

is an isomorphism, natural in `M` and `Q`. Here both external products are taken over `S`,
and `f × id_Z : X ×_S Z ⟶ Y ×_S Z` is `AlgebraicGeometry.Etale.prodMapRight`. The proof is
smooth base change along the projection `Y ×_S Z ⟶ Y` followed by the projection formula. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar
    {S X Y Z : Scheme.{u}} (b : Y ⟶ S) (c : Z ⟶ S) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    (hM : DerivedCategory.boundedConstructible A X M ∧ DerivedCategory.finiteTorAmplitude A X M)
    (hQ : DerivedCategory.boundedConstructible A Z Q ∧
      DerivedCategory.finiteTorAmplitude A Z Q) :
    Nonempty (externalProduct A b c ((R((f)_*[A])).obj M) Q ≅
      (R((prodMapRight b c f)_*[A])).obj (externalProduct A (f ≫ b) c M Q)) :=
  sorry

/-- Blueprint `sk-thm-sf-kunneth-relative`: Relative product theorem.

Let `f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type over a base scheme `B`, and let
`K` on `X` and `M` on `Y` be bounded constructible of finite Tor amplitude, i.e. objects of
`Dctf(X, A)` and `Dctf(Y, A)`. Writing `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M` for the external product
over `B` and `f ×_B g : X ×_B Y ⟶ B` for the structure morphism of the fibre product, the
canonical map

`R(f ×_B g)_! (K ⊠ M) ⟶ Rf_! K ⊗ᴸ Rg_! M`

in `D(B_ét)` is an isomorphism, natural in `K` and `M`. It is compatible with base change
along `B' ⟶ B`, with finite reduction and scalar extension of the coefficients, and with the
identification `Rf_! ≅ Rf_*` for proper `f`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    [HasCompactification f] [HasCompactification g]
    [HasCompactification (pullbackToBase f g)]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.boundedConstructible A X K ∧ DerivedCategory.finiteTorAmplitude A X K)
    (hM : DerivedCategory.boundedConstructible A Y M ∧
      DerivedCategory.finiteTorAmplitude A Y M) :
    Nonempty ((R(pullbackToBase f g)_![A]).obj (externalProduct A f g K M) ≅
      (R(f)_![A]).obj K ⊗ (R(g)_![A]).obj M) :=
  sorry

/-- Blueprint `sk-def-sf-kv-maps`: The product comparison maps.

The four product comparison maps of the six-functor formalism over a base scheme `S`,
recorded as the conjunction of the four assertions that they exist as isomorphisms. All
external products are taken over `S`.

* **(i)** the `!`-Künneth map
  `Ku_! : Rf_! (M₁ ⊠ M₂) ⟶ Rf_{1!} M₁ ⊠ Rf_{2!} M₂` for `f = f₁ × f₂`, which is
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
  `Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_S Y₂) ×_{Y₁ ×_S Y₂} (Y₁ ×_S X₂)`; it is an
  isomorphism *by construction*, being built out of isomorphisms;
* **(ii)** the exceptional Künneth map
  `α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ⟶ Rf^! (N₁ ⊠ N₂)`, the exceptional adjoint of `Ku_!` followed by
  the two counits of `Rf_{i!} ⊣ Rf_i^!`;
* **(iii)** the external Hom map
  `β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`, the tensor–Hom transpose of
  the two evaluation maps;
* **(iv)** the Künneth–Verdier map
  `κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Rp_X^! M)` on `X ×_S Y`, the composite of `β` applied to the
  pairs `(Λ_X, M)` and `(N, ω_Y)` with `RHom(1, α)` for `id_X × a_Y`, using the unit
  identifications `RHom(Λ_X, M) = M` and `Λ_X ⊠ N = p_Y^* N`.

Only `Ku_!` is built from isomorphisms; that `α`, `β` and `κ` are invertible is the content of
`AlgebraicGeometry.Etale.hasKunnethComparisons`, i.e. of `sk-thm-sf-kunneth-verdier`. -/
def HasKunnethComparisons (S : Scheme.{u}) : Prop :=
  -- (i) the `!`-Künneth map `Ku_!`
  (∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      [HasCompactification f₁] [HasCompactification f₂]
      [HasCompactification (prodMapOver b₁ b₂ f₁ f₂)]
      (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
      (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)),
      DerivedCategory.boundedConstructible A X₁ M₁ ∧
        DerivedCategory.finiteTorAmplitude A X₁ M₁ →
      DerivedCategory.boundedConstructible A X₂ M₂ ∧
        DerivedCategory.finiteTorAmplitude A X₂ M₂ →
      Nonempty ((R(prodMapOver b₁ b₂ f₁ f₂)_![A]).obj
          (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
        externalProduct A b₁ b₂ ((R(f₁)_![A]).obj M₁) ((R(f₂)_![A]).obj M₂))) ∧
  -- (ii) the exceptional Künneth map `α`
  (∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      [HasCompactification f₁] [HasCompactification f₂]
      [HasCompactification (prodMapOver b₁ b₂ f₁ f₂)]
      (N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology A))
      (N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology A)),
      DerivedCategory.boundedConstructible A Y₁ N₁ ∧
        DerivedCategory.finiteTorAmplitude A Y₁ N₁ →
      DerivedCategory.boundedConstructible A Y₂ N₂ ∧
        DerivedCategory.finiteTorAmplitude A Y₂ N₂ →
      Nonempty (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂)
          ((R(f₁)^![A]).obj N₁) ((R(f₂)^![A]).obj N₂) ≅
        (R(prodMapOver b₁ b₂ f₁ f₂)^![A]).obj (externalProduct A b₁ b₂ N₁ N₂))) ∧
  -- (iii) the external Hom map `β`
  (∀ {Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
      (E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A))
      (E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)),
      DerivedCategory.boundedConstructible A Z₁ E₁ ∧
        DerivedCategory.finiteTorAmplitude A Z₁ E₁ →
      DerivedCategory.boundedConstructible A Z₂ E₂ ∧
        DerivedCategory.finiteTorAmplitude A Z₂ E₂ →
      Nonempty (externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj N₁)
          ((RHom(Z₂)[A].obj (op E₂)).obj N₂) ≅
        (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
          (externalProduct A c₁ c₂ N₁ N₂))) ∧
  -- (iv) the Künneth–Verdier map `κ`
  (∀ {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) [HasCompactification b]
      [HasCompactification (pullback.fst a b)]
      (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      DerivedCategory.boundedConstructible A X M ∧ DerivedCategory.finiteTorAmplitude A X M →
      DerivedCategory.boundedConstructible A Y N ∧ DerivedCategory.finiteTorAmplitude A Y N →
      Nonempty (externalProduct A a b M ((verdierDual A b).obj (op N)) ≅
        (RHom(pullback a b)[A].obj (op ((L((pullback.snd a b)^*[A])).obj N))).obj
          ((R(pullback.fst a b)^![A]).obj M)))

/-- Blueprint `sk-thm-sf-kunneth-verdier`: Künneth–Verdier isomorphism.

The four product comparison maps of `AlgebraicGeometry.Etale.HasKunnethComparisons` are
isomorphisms, naturally in their variables: besides the `!`-Künneth map `Ku_!`, which is an
isomorphism by construction, this asserts the invertibility of the exceptional Künneth map
`α`, of the external Hom map `β`, and of the Künneth–Verdier map `κ`.

The proof runs through smooth purity and supported localization for `α`, dévissage along the
generators `Rh_! Λ_U` of `Dctf` for `β`, and the composite `β` then `RHom(1, α)` for `κ`. -/
theorem hasKunnethComparisons (S : Scheme.{u}) : HasKunnethComparisons A S :=
  sorry

/-- Blueprint `sk-thm-sf-kunneth-verdier`: Künneth–Verdier isomorphism.

The headline case of `AlgebraicGeometry.Etale.hasKunnethComparisons`: for `X` and `Y`
separated of finite type over a base `S`, with projections `p_X : X ×_S Y ⟶ X` and
`p_Y : X ×_S Y ⟶ Y`, and for `M` on `X` and `N` on `Y` bounded constructible of finite Tor
amplitude — objects of `Dctf(X, A)` and `Dctf(Y, A)` — the Künneth–Verdier map

`κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Rp_X^! M)`

is an isomorphism on `X ×_S Y`, naturally in `M` and `N`. Here `𝔻_Y = RHom(-, ω_Y)` is the
Verdier dual `AlgebraicGeometry.Etale.verdierDual` relative to `b : Y ⟶ S`. -/
theorem nonempty_iso_externalProduct_verdierDual
    {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [IsSeparated a] [LocallyOfFiniteType a] [IsSeparated b] [LocallyOfFiniteType b]
    [HasCompactification b] [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : DerivedCategory.boundedConstructible A X M ∧ DerivedCategory.finiteTorAmplitude A X M)
    (hN : DerivedCategory.boundedConstructible A Y N ∧
      DerivedCategory.finiteTorAmplitude A Y N) :
    Nonempty (externalProduct A a b M ((verdierDual A b).obj (op N)) ≅
      (RHom(pullback a b)[A].obj (op ((L((pullback.snd a b)^*[A])).obj N))).obj
        ((R(pullback.fst a b)^![A]).obj M)) :=
  sorry

end Etale

end AlgebraicGeometry
