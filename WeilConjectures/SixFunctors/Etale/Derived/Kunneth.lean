/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
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

## Main definitions

- `AlgebraicGeometry.Etale.externalProduct`: `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M`.
- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`sk-def-sf-kv-maps`): the four product
  comparison assertions `Ku_!`, `α`, `β`, `κ`, one per field.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`sk-lem-sf-kunneth-star`): `Rf_* M ⊠ Q ≅ R(f × id_Z)_* (M ⊠ Q)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
  (`sk-thm-sf-kunneth-relative`): `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct`:
  `L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`:
  `(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L` for closed immersions `i`, `j`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
  (`sk-thm-product`): the relative product theorem for complexes supported on closed
  subschemes.
- `AlgebraicGeometry.Etale.nonempty_iso_compactlySupported_externalProduct_closedImmersion`
  (`sk-thm-product`): the Künneth formula for `RΓ_c(Z × W, -)` over a field.
- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`sk-thm-sf-kunneth-verdier`): the four
  comparison maps are isomorphisms.

## Implementation notes

The fibre-product morphisms `X ×_B Y ⟶ B`, `f₁ × f₂` and `f × 𝟙_Z` are not étale notions and
are not defined here: they are `CategoryTheory.Limits.pullback.toBase`,
`CategoryTheory.Limits.pullback.mapOverBase` and
`CategoryTheory.Limits.pullback.mapOverBaseRight` of
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.

Constructing the canonical comparison maps is out of scope here, so all comparisons are
stated in the form `Nonempty (_ ≅ _)`; the blueprint's naturality clauses, and the
compatibilities of the relative product theorem with base change, finite reduction, scalar
extension and the identification `Rf_! ≅ Rf_*` for proper `f`, are therefore **not stated**.
The absolute case of a product over the base `S` is the special case `B = S` of the
definitions below.

A morphism admitting a compactification is separated and locally of finite type
(`AlgebraicGeometry.HasCompactification.isSeparated` and `.locallyOfFiniteType`), so the
blueprint hypothesis "separated of finite type" is spelled `[HasCompactification f]`
together with `[QuasiCompact f]` wherever `Rf_!` occurs, and as the triple
`[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` otherwise.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {B X Y : Scheme.{u}}

/-- The external product of `K ∈ D(X_ét)` and `M ∈ D(Y_ét)` along the fibre-product square

```
  X ×_B Y --q--> Y
     |           |
     p           g
     v           v
     X ---f----> B
```

namely `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M`, an object of `D((X ×_B Y)_ét)`.

The absolute external product over a base scheme `S` is the case where `f` and `g` are the
structure morphisms of `X` and `Y`. -/
noncomputable def externalProduct (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    _root_.DerivedCategory (Sheaf (pullback f g).smallEtaleTopology A) :=
  (L((pullback.fst f g)^*[A])).obj K ⊗ (L((pullback.snd f g)^*[A])).obj M

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `sk-lem-sf-kunneth-star`: Ordinary Künneth with an identity factor.

Let `f : X ⟶ Y` be separated of finite type between schemes over a base `S`, where `X` is
viewed over `S` through `f ≫ b`, and let `c : Z ⟶ S` be a further such scheme, so that `f`
induces `f × 𝟙_Z` across the square

```
  X ×_S Z --f × 𝟙--> Y ×_S Z --pr--> Y
     |                  |            |
     |                  |            f
     v                  v            v
     Z ------c------->  S <----b---- Y
```

For `M` in `Dctf(X, A)` and `Q` in `Dctf(Z, A)` the canonical comparison

`Rf_* M ⊠ Q ⟶ R(f × id_Z)_* (M ⊠ Q)`

is an isomorphism. Here both external products are taken over `S`. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar
    {S Z : Scheme.{u}} (b : Y ⟶ S) (c : Z ⟶ S) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    (hM : DerivedCategory.constructibleFiniteTor A X M)
    (hQ : DerivedCategory.constructibleFiniteTor A Z Q) :
    Nonempty (externalProduct A b c ((R((f)_*[A])).obj M) Q ≅
      (R((pullback.mapOverBaseRight f b c)_*[A])).obj
        (externalProduct A (f ≫ b) c M Q)) :=
  sorry

/-- Blueprint `sk-thm-sf-kunneth-relative`: Relative product theorem.

Let `f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type over a base scheme `B`, and let
`K` be in `Dctf(X, A)` and `M` in `Dctf(Y, A)`. Writing `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M` for the
external product over `B` and `f ×_B g : X ×_B Y ⟶ B` for the structure morphism
`CategoryTheory.Limits.pullback.toBase` of the fibre product, the canonical map

`R(f ×_B g)_! (K ⊠ M) ⟶ Rf_! K ⊗ᴸ Rg_! M`

in `D(B_ét)` is an isomorphism. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct (f : X ⟶ B) (g : Y ⟶ B)
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hM : DerivedCategory.constructibleFiniteTor A Y M) :
    Nonempty ((R(pullback.toBase f g)_![A]).obj (externalProduct A f g K M) ≅
      (R(f)_![A]).obj K ⊗ (R(g)_![A]).obj M) :=
  sorry

/-- The external product is compatible with pullback: for morphisms `i : Z ⟶ X`, `j : W ⟶ Y`
over `B`, with product `i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`,

the external product on the right being taken along `i ≫ f` and `j ≫ g`. -/
theorem nonempty_iso_leftDerivedUpperStar_externalProduct (f : X ⟶ B) (g : Y ⟶ B)
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L) ≅
      externalProduct A (i ≫ f) (j ≫ g) ((L((i)^*[A])).obj K) ((L((j)^*[A])).obj L)) :=
  -- Proof sketch: `K ⊠ L = Lp^* K ⊗ᴸ Lq^* L`; the derived pullback is monoidal, and
  -- `p ∘ (i ×_B j) = i ∘ p'`, `q ∘ (i ×_B j) = j ∘ q'` for the projections `p'`, `q'` of
  -- `Z ×_B W`.
  sorry

/-- The external product is compatible with restriction to closed subschemes: for closed
immersions `i : Z ⟶ X`, `j : W ⟶ Y` over `B`, with product `i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L`. -/
theorem nonempty_iso_externalProduct_closedImmersion (f : X ⟶ B) (g : Y ⟶ B)
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((R((pullback.mapOverBase i j f g)_*[A])).obj
        ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L)) ≅
      externalProduct A f g ((R((i)_*[A])).obj ((L((i)^*[A])).obj K))
        ((R((j)_*[A])).obj ((L((j)^*[A])).obj L))) :=
  -- Proof sketch: both sides are `K ⊠ L` tensored with the constant sheaf of the closed
  -- subscheme `Z ×_B W = p⁻¹ Z ∩ q⁻¹ W`, by the projection formula for closed immersions and
  -- proper base change along the projections `p`, `q`.
  sorry

/-- Blueprint `sk-thm-product`: Supported product over a relative base.

Let `f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type, `h = f ×_B g`, and let
`i : Z ⟶ X`, `j : W ⟶ Y` be closed immersions, with product
`i ×_B j : Z ×_B W ⟶ X ×_B Y`. For `K` in `Dctf(X, A)` and `L` in `Dctf(Y, A)`,

`Rf_!(i_* i^* K) ⊗ᴸ Rg_!(j_* j^* L) ≅ Rh_!((i ×_B j)_* (i ×_B j)^* (K ⊠ L))`.

This is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the
complexes `i_* i^* K` and `j_* j^* L`, rewritten with
`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`. Over `B = Spec k` it
is the Künneth formula for the compactly supported cohomology of `Z ×_k W`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion
    (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g] [HasCompactification (pullback.toBase f g)]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hL : DerivedCategory.constructibleFiniteTor A Y L) :
    Nonempty ((R(f)_![A]).obj ((R((i)_*[A])).obj ((L((i)^*[A])).obj K)) ⊗
        (R(g)_![A]).obj ((R((j)_*[A])).obj ((L((j)^*[A])).obj L)) ≅
      (R(pullback.toBase f g)_![A]).obj
        ((R((pullback.mapOverBase i j f g)_*[A])).obj
          ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L)))) := by
  obtain ⟨e⟩ := nonempty_iso_externalProduct_closedImmersion A f g i j K L
  obtain ⟨k⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct A f g
    (constructibleFiniteTor_rightDerivedLowerStar A i
      (constructibleFiniteTor_leftDerivedUpperStar A i hK))
    (constructibleFiniteTor_rightDerivedLowerStar A j
      (constructibleFiniteTor_leftDerivedUpperStar A j hL))
  exact ⟨k.symm ≪≫ (R(pullback.toBase f g)_![A]).mapIso e.symm⟩

/-- Blueprint `sk-thm-product`: Supported product over a relative base.

The Künneth formula with closed supports over a field: for `X`, `Y` separated of finite type
over a field `k` and closed subschemes `i : Z ⟶ X`, `j : W ⟶ Y`,

`RΓ_c(Z, i^* K) ⊗ᴸ RΓ_c(W, j^* L) ≅ RΓ_c(Z × W, (K ⊠ L)|_{Z × W})`,

written one step earlier, in `D((Spec k)_ét)`, with the structure morphisms `i ≫ f`,
`j ≫ g` of `Z`, `W` and `Z × W ⟶ Spec k`.

It is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for `i ≫ f`,
`j ≫ g` and the complexes `i^* K`, `j^* L`, rewritten with
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct`. Comparing it with
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
over `B = Spec k` would also need `R(i ≫ f)_! ≅ Rf_! Ri_*`, the composition of compactly
supported direct images. -/
theorem nonempty_iso_compactlySupported_externalProduct_closedImmersion
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [HasCompactification (i ≫ f)] [HasCompactification (j ≫ g)]
    [HasCompactification (pullback.toBase (i ≫ f) (j ≫ g))]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hL : DerivedCategory.constructibleFiniteTor A Y L) :
    Nonempty ((R(i ≫ f)_![A]).obj ((L((i)^*[A])).obj K) ⊗
        (R(j ≫ g)_![A]).obj ((L((j)^*[A])).obj L) ≅
      (R(pullback.toBase (i ≫ f) (j ≫ g))_![A]).obj
        ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L))) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_externalProduct A f g i j K L
  obtain ⟨k⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct A (i ≫ f) (j ≫ g)
    (constructibleFiniteTor_leftDerivedUpperStar A i hK)
    (constructibleFiniteTor_leftDerivedUpperStar A j hL)
  exact ⟨k.symm ≪≫ (R(pullback.toBase (i ≫ f) (j ≫ g))_![A]).mapIso e.symm⟩

/-- Blueprint `sk-def-sf-kv-maps`: The product comparison maps.

The four product comparison maps of the six-functor formalism over a base scheme `S`, each
recorded as the assertion that it is an isomorphism. All external products are taken over
`S`.

* `kunnethShriek` is the `!`-Künneth map
  `Ku_! : Rf_! (M₁ ⊠ M₂) ⟶ Rf_{1!} M₁ ⊠ Rf_{2!} M₂` for `f = f₁ × f₂`, which is
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
  `Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_S Y₂) ×_{Y₁ ×_S Y₂} (Y₁ ×_S X₂)`; it is an
  isomorphism *by construction*, being built out of isomorphisms;
* `exceptional` is the exceptional Künneth map
  `α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ⟶ Rf^! (N₁ ⊠ N₂)`, the exceptional adjoint of `Ku_!` followed by
  the two counits of `Rf_{i!} ⊣ Rf_i^!`;
* `externalHom` is the external Hom map
  `β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`, the tensor–Hom transpose of
  the two evaluation maps;
* `kunnethVerdier` is the Künneth–Verdier map
  `κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Rp_X^! M)` on `X ×_S Y`, the composite of `β` applied to the
  pairs `(Λ_X, M)` and `(N, ω_Y)` with `RHom(1, α)` for `id_X × a_Y`, using the unit
  identifications `RHom(Λ_X, M) = M` and `Λ_X ⊠ N = p_Y^* N`.

Only `Ku_!` is built from isomorphisms; that `α`, `β` and `κ` are invertible is the content of
`AlgebraicGeometry.Etale.hasKunnethComparisons`, i.e. of `sk-thm-sf-kunneth-verdier`. -/
structure HasKunnethComparisons (S : Scheme.{u}) : Prop where
  /-- The `!`-Künneth map `Ku_!` is an isomorphism. -/
  kunnethShriek : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A)}
      {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A X₁ M₁ →
      DerivedCategory.constructibleFiniteTor A X₂ M₂ →
      Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).obj
          (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
        externalProduct A b₁ b₂ ((R(f₁)_![A]).obj M₁) ((R(f₂)_![A]).obj M₂))
  /-- The exceptional Künneth map `α` is an isomorphism. -/
  exceptional : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology A)}
      {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A Y₁ N₁ →
      DerivedCategory.constructibleFiniteTor A Y₂ N₂ →
      Nonempty (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂)
          ((R(f₁)^![A]).obj N₁) ((R(f₂)^![A]).obj N₂) ≅
        (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![A]).obj (externalProduct A b₁ b₂ N₁ N₂))
  /-- The external Hom map `β` is an isomorphism. -/
  externalHom : ∀ {Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
      [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
      [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
      {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A)}
      {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A Z₁ E₁ →
      DerivedCategory.constructibleFiniteTor A Z₂ E₂ →
      DerivedCategory.constructibleFiniteTor A Z₁ N₁ →
      DerivedCategory.constructibleFiniteTor A Z₂ N₂ →
      Nonempty (externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj N₁)
          ((RHom(Z₂)[A].obj (op E₂)).obj N₂) ≅
        (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
          (externalProduct A c₁ c₂ N₁ N₂))
  /-- The Künneth–Verdier map `κ` is an isomorphism. -/
  kunnethVerdier : ∀ {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
      {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
      {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A X M →
      DerivedCategory.constructibleFiniteTor A Y N →
      Nonempty (externalProduct A a b M ((verdierDual A b).obj (op N)) ≅
        (RHom(pullback a b)[A].obj (op ((L((pullback.snd a b)^*[A])).obj N))).obj
          ((R(pullback.fst a b)^![A]).obj M))

/-- Blueprint `sk-thm-sf-kunneth-verdier`: Künneth–Verdier isomorphism.

The four product comparison maps of `AlgebraicGeometry.Etale.HasKunnethComparisons` are
isomorphisms: besides the `!`-Künneth map `Ku_!`, which is an isomorphism by construction,
this asserts the invertibility of the exceptional Künneth map `α`, of the external Hom map
`β`, and of the Künneth–Verdier map `κ`.

The headline case is `kunnethVerdier`: for `X` and `Y` separated of finite type over `S`,
with projections `p_X : X ×_S Y ⟶ X` and `p_Y : X ×_S Y ⟶ Y`, and for `M` in `Dctf(X, A)`
and `N` in `Dctf(Y, A)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`

on `X ×_S Y`, where `𝔻_Y = RHom(-, ω_Y)` is the Verdier dual relative to `b : Y ⟶ S`. -/
theorem hasKunnethComparisons (S : Scheme.{u}) : HasKunnethComparisons A S :=
  sorry

end Etale

end AlgebraicGeometry
