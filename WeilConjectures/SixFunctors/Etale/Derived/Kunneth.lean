/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
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
- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`sk-def-sf-kv-maps`, `def-sf-kv-maps`): the
  four product comparison assertions `Ku_!`, `α`, `β`, `κ`, one per field.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`sk-lem-sf-kunneth-star`, `lem-trf-ordinary-kunneth`): `Rf_* M ⊠ Q ≅ R(f × id_Z)_* (M ⊠ Q)`
  over a field, for a finite coefficient ring of invertible exponent.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
  (`sk-thm-sf-kunneth-relative`): `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`
  (`sk-def-sf-kv-maps` (i)): the `!`-Künneth isomorphism
  `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` for a finite coefficient ring.
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

/-- Blueprint `sk-lem-sf-kunneth-star` (detailed node `lem-trf-ordinary-kunneth`): Ordinary
Künneth with an identity factor.

Let `k` be a field, `Λ` a finite coefficient ring whose exponent is invertible in `k` (for
instance the finite stage `A_{E,n}`), and let `f : X ⟶ Y` be a morphism of separated
finite-type `k`-schemes, where `Y` has structure morphism `b` and `X` is viewed over `k`
through `f ≫ b`. Let `c : Z ⟶ Spec k` be a further separated finite-type `k`-scheme, so that
`f` induces `f × 𝟙_Z` across the square

```
  X ×_k Z --f × 𝟙--> Y ×_k Z --pr--> Y
     |                  |            |
     |                  |            f
     v                  v            v
     Z ------c------> Spec k <--b--- Y
```

For `M` in `Dctf(X, Λ)` and `Q` in `Dctf(Z, Λ)` the canonical comparison

`Rf_* M ⊠ Q ⟶ R(f × id_Z)_* (M ⊠ Q)`

is an isomorphism. Here both external products are taken over `Spec k`.

The base has to be a field and the exponent of `Λ` invertible: over the base `𝔸¹_k`, with
`Z` the origin and `f` the inclusion of `𝔾_m`, the right-hand side vanishes while the
left-hand side is the stalk of `Rf_* Λ` at the origin; and for `Λ = 𝔽_p` in characteristic
`p` the Artin–Schreier cohomology of the affine line already defeats the formula. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Z : Scheme.{u}}
    (b : Y ⟶ Spec (.of k)) (c : Z ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z Q) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) b c
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M) Q ≅
      (R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (f ≫ b) c M Q)) :=
  sorry

/-- Blueprint `sk-thm-sf-kunneth-relative`: Relative product theorem.

Let `f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type over a base scheme `B`, and let
`K` be in `Dctf(X, A)` and `M` in `Dctf(Y, A)`. Writing `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M` for the
external product over `B` and `f ×_B g : X ×_B Y ⟶ B` for the structure morphism
`CategoryTheory.Limits.pullback.toBase` of the fibre product, the canonical map

`R(f ×_B g)_! (K ⊠ M) ⟶ Rf_! K ⊗ᴸ Rg_! M`

in `D(B_ét)` is an isomorphism. The coefficients are torsion, finitely generated objects of `A`
being finite (`CategoryTheory.ConcreteCategory.FiniteOfIsFinitelyGenerated`): with coefficients
`ℤ` the statement fails, proper base change failing for a regular proper curve over a strictly
henselian discrete valuation ring with nodal special fibre. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct (f : X ⟶ B) (g : Y ⟶ B)
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A]
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
`i ×_B j : Z ×_B W ⟶ X ×_B Y`. For `K` and `L` on `X` and `Y` such that `i_* i^* K` and `j_* j^* L`
lie in `Dctf`,

`Rf_!(i_* i^* K) ⊗ᴸ Rg_!(j_* j^* L) ≅ Rh_!((i ×_B j)_* (i ×_B j)^* (K ⊠ L))`.

This is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the
complexes `i_* i^* K` and `j_* j^* L`, rewritten with
`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`. Over `B = Spec k` it
is the Künneth formula for the compactly supported cohomology of `Z ×_k W`.

The hypotheses are on `i_* i^* K` and `j_* j^* L` rather than on `K` and `L`: that `Ri_*` preserves
`Dctf` is a finiteness theorem for torsion coefficients of exponent invertible on the base
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`), which in the blueprint's
setting turns `K, L ∈ Dctf` into these hypotheses. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A] [UpperStarPreservesFlat A]
    (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g] [HasCompactification (pullback.toBase f g)]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X ((R((i)_*[A])).obj ((L((i)^*[A])).obj K)))
    (hL : DerivedCategory.constructibleFiniteTor A Y ((R((j)_*[A])).obj ((L((j)^*[A])).obj L))) :
    Nonempty ((R(f)_![A]).obj ((R((i)_*[A])).obj ((L((i)^*[A])).obj K)) ⊗
        (R(g)_![A]).obj ((R((j)_*[A])).obj ((L((j)^*[A])).obj L)) ≅
      (R(pullback.toBase f g)_![A]).obj
        ((R((pullback.mapOverBase i j f g)_*[A])).obj
          ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L)))) := by
  obtain ⟨e⟩ := nonempty_iso_externalProduct_closedImmersion A f g i j K L
  obtain ⟨k⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct A f g hK hL
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
    [ConcreteCategory.FiniteOfIsFinitelyGenerated A] [UpperStarPreservesFlat A]
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

section KunnethShriek

/-! ### The `!`-Künneth isomorphism

Item (i) of `sk-def-sf-kv-maps`: for `fᵢ : Xᵢ ⟶ Yᵢ` over `S`, the `!`-Künneth isomorphism
`Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` is the relative product theorem over
`B = Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)`
(`CategoryTheory.Limits.pullback.mapOverBaseIso`) and compact-support base change. -/

/-- For an isomorphism `e : Y ≅ Y'` of schemes, the derived pushforward `R(e_*)` is the
derived pullback `L((e⁻¹)^*)`: both are computed by the exact functor `e_* ≅ (e⁻¹)^*`. -/
noncomputable def rightDerivedLowerStarIsoLeftDerivedUpperStarInv {Y Y' : Scheme.{u}}
    (e : Y ≅ Y') : R((e.hom)_*[A]) ≅ L((e.inv)^*[A]) :=
  have : PreservesFiniteColimits (e.hom)_*[A] :=
    preservesFiniteColimits_of_natIso (upperStarInvIsoLowerStarHom A e)
  Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarInvIsoLowerStarHom A e).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory A e.inv).symm

variable {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁)
  (f₂ : X₂ ⟶ Y₂)

/-- Transport of `R(f₁ × f₂)_!` along `pullback.mapOverBaseIso`: for `Z` in
`D((X₁ ×_S X₂)_ét)`, writing `e : X₁ ×_S X₂ ≅ (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)` with
`B = Y₁ ×_S Y₂` and `h` for the structure morphism of the fibre product over `B`,

`R(f₁ × f₂)_! Z ≅ Rh_! (L(e⁻¹)^* Z)`, given the composition isomorphism
`R(f₁ × f₂)_! ≅ Re_! ⋙ Rh_!` (`hcomp`), which holds for torsion coefficients
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`). -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    [HasCompactification (pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂)))]
    [HasCompactification (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom]
    (hcomp : Nonempty (R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A] ≅
      R((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom)_![A] ⋙
        R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
          (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]))
    (Z : _root_.DerivedCategory (Sheaf (pullback (f₁ ≫ b₁) (f₂ ≫ b₂)).smallEtaleTopology A)) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).obj Z ≅
      (R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]).obj
        ((L(((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv)^*[A])).obj Z)) := by
  set e := pullback.mapOverBaseIso f₁ f₂ b₁ b₂
  set h := pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂))
  obtain ⟨c₁⟩ := hcomp
  obtain ⟨c₂⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar A e.hom
  exact ⟨c₁.app Z ≪≫ (R(h)_![A]).mapIso
    (c₂.app Z ≪≫ (rightDerivedLowerStarIsoLeftDerivedUpperStarInv A e).app Z)⟩

omit [HasSmallSiteSheafify A] in
/-- The external product is compatible with `pullback.mapOverBaseIso`: writing
`e : X₁ ×_S X₂ ≅ (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)` with `B = Y₁ ×_S Y₂` and `hᵢ` for the
projections `Xᵢ ×_{Yᵢ} B ⟶ Xᵢ`,

`L(e⁻¹)^* (M₁ ⊠_S M₂) ≅ Lh₁^* M₁ ⊠_B Lh₂^* M₂`. -/
theorem nonempty_iso_leftDerivedUpperStar_mapOverBaseIso_externalProduct
    [UpperStarPreservesFlat A]
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    Nonempty ((L(((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).inv)^*[A])).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct A (pullback.snd f₁ (pullback.fst b₁ b₂))
        (pullback.snd f₂ (pullback.snd b₁ b₂))
        ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁)
        ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂)) := by
  set e := pullback.mapOverBaseIso f₁ f₂ b₁ b₂
  let pb₁ := ((leftDerivedUpperStarComp A e.inv (pullback.fst _ _)).app M₁).symm ≪≫
      (leftDerivedUpperStarComp A (pullback.fst _ _) (pullback.fst f₁ (pullback.fst b₁ b₂))
        (e.inv ≫ pullback.fst _ _) (by simp [e])).app M₁
  let pb₂ := ((leftDerivedUpperStarComp A e.inv (pullback.snd _ _)).app M₂).symm ≪≫
      (leftDerivedUpperStarComp A (pullback.snd _ _) (pullback.fst f₂ (pullback.snd b₁ b₂))
        (e.inv ≫ pullback.snd _ _) (by simp [e])).app M₂
  exact ⟨leftDerivedUpperStarTensorIso A e.inv _ _ ≪≫ (pb₁ ⊗ᵢ pb₂)⟩

/-- The `!`-Künneth isomorphism `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` for
general coefficients, given compact-support base change of `Rfᵢ_! Mᵢ` along the projections
`Y₁ ×_S Y₂ ⟶ Yᵢ` and the composition isomorphism `R(f₁ × f₂)_! ≅ Re_! ⋙ Rh_!` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase`; both hold for torsion
coefficients. It is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` over
`B = Y₁ ×_S Y₂`, transported along `pullback.mapOverBaseIso`. -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct_of_baseChange
    [UpperStarPreservesFlat A] [ConcreteCategory.FiniteOfIsFinitelyGenerated A]
    [HasCompactification f₁] [HasCompactification f₂] [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A)}
    {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)}
    (hM₁ : DerivedCategory.constructibleFiniteTor A X₁ M₁)
    (hM₂ : DerivedCategory.constructibleFiniteTor A X₂ M₂)
    [HasCompactification (pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom]
    [HasCompactification (pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂)))]
    (hcomp : Nonempty (R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A] ≅
      R((pullback.mapOverBaseIso f₁ f₂ b₁ b₂).hom)_![A] ⋙
        R(pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
          (pullback.snd f₂ (pullback.snd b₁ b₂)))_![A]))
    (hbc₁ : Nonempty ((L((pullback.fst b₁ b₂)^*[A])).obj ((R(f₁)_![A]).obj M₁) ≅
      (R(pullback.snd f₁ (pullback.fst b₁ b₂))_![A]).obj
        ((L((pullback.fst f₁ (pullback.fst b₁ b₂))^*[A])).obj M₁)))
    (hbc₂ : Nonempty ((L((pullback.snd b₁ b₂)^*[A])).obj ((R(f₂)_![A]).obj M₂) ≅
      (R(pullback.snd f₂ (pullback.snd b₁ b₂))_![A]).obj
        ((L((pullback.fst f₂ (pullback.snd b₁ b₂))^*[A])).obj M₂))) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct A b₁ b₂ ((R(f₁)_![A]).obj M₁) ((R(f₂)_![A]).obj M₂)) := by
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_mapOverBase A b₁ b₂ f₁ f₂ hcomp
    (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂)
  obtain ⟨p⟩ := nonempty_iso_leftDerivedUpperStar_mapOverBaseIso_externalProduct A b₁ b₂ f₁ f₂
    M₁ M₂
  obtain ⟨ku⟩ := nonempty_iso_rightDerivedLowerShriek_externalProduct A
    (pullback.snd f₁ (pullback.fst b₁ b₂)) (pullback.snd f₂ (pullback.snd b₁ b₂))
    (constructibleFiniteTor_leftDerivedUpperStar A (pullback.fst f₁ _) hM₁)
    (constructibleFiniteTor_leftDerivedUpperStar A (pullback.fst f₂ _) hM₂)
  obtain ⟨e₁⟩ := hbc₁
  obtain ⟨e₂⟩ := hbc₂
  exact ⟨t ≪≫ (R(_)_![A]).mapIso p ≪≫ ku ≪≫ (e₁.symm ⊗ᵢ e₂.symm)⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] in
/-- Blueprint `sk-def-sf-kv-maps` (i), `def-sf-kv-maps` (i): the `!`-Künneth isomorphism.

Let `fᵢ : Xᵢ ⟶ Yᵢ` be separated of finite type between schemes over `S`, let `Λ` be a finite
coefficient ring and `Mᵢ` in `Dctf(Xᵢ, Λ)`. Writing `f = f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂`,

`Ku_! : Rf_!(M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂`.

This is the relative product theorem
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
`B = Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)`, together with
compact-support base change `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
along the projections `B ⟶ Yᵢ`. The finiteness of `Λ` is the hypothesis of that base change
theorem. -/
theorem nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct
    [HasCompactification f₁] [HasCompactification f₂] [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM₁ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₁ M₁)
    (hM₂ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X₂ M₂) :
    Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
      externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂
        ((R(f₁)_![ModuleCat.{u + 1} Λ]).obj M₁) ((R(f₂)_![ModuleCat.{u + 1} Λ]).obj M₂)) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback f₁ (pullback.fst b₁ b₂))
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback f₂ (pullback.snd b₁ b₂))
  set e := pullback.mapOverBaseIso f₁ f₂ b₁ b₂
  set h := pullback.toBase (pullback.snd f₁ (pullback.fst b₁ b₂))
      (pullback.snd f₂ (pullback.snd b₁ b₂))
  have he : e.hom ≫ h = pullback.mapOverBase f₁ f₂ b₁ b₂ :=
    pullback.mapOverBaseIso_hom_toBase ..
  have : HasCompactification h :=
    ((HasCompactification.compactification (pullback.mapOverBase f₁ f₂ b₁ b₂)).transport
      e (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id, he])).hasCompactification
  have : HasCompactification (e.hom ≫ h) := .of_eq he.symm
  have hcongr : ∀ (ψ : _ ⟶ _) [HasCompactification ψ], ψ = pullback.mapOverBase f₁ f₂ b₁ b₂ →
      Nonempty (R(ψ)_![ModuleCat.{u + 1} Λ] ≅
        R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![ModuleCat.{u + 1} Λ]) := by
    rintro ψ _ rfl; exact ⟨Iso.refl _⟩
  obtain ⟨c₀⟩ := hcongr _ he
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ e.hom h
  exact nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct_of_baseChange _
    b₁ b₂ f₁ f₂ hM₁ hM₂ ⟨c₀.symm ≪≫ c₁⟩
    ⟨asIso ((rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback f₁ (pullback.fst b₁ b₂))).app M₁)⟩
    ⟨asIso ((rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback f₂ (pullback.snd b₁ b₂))).app M₂)⟩

end KunnethShriek

/-- Blueprint `sk-def-sf-kv-maps`, `def-sf-kv-maps`: The product comparison maps.

The four product comparison maps of the six-functor formalism over a base scheme `S`, each
recorded as the assertion that it is an isomorphism. All external products are taken over
`S`.

* `kunnethShriek` is the `!`-Künneth map
  `Ku_! : Rf_! (M₁ ⊠ M₂) ⟶ Rf_{1!} M₁ ⊠ Rf_{2!} M₂` for `f = f₁ × f₂`, which is
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
  `Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_S Y₂) ×_{Y₁ ×_S Y₂} (Y₁ ×_S X₂)`; it is an
  isomorphism *by construction*, being built out of isomorphisms. For a finite coefficient
  ring this is proved, from the relative product theorem and compact-support base change, as
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`;
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
`AlgebraicGeometry.Etale.hasKunnethComparisons`, i.e. of `sk-thm-sf-kunneth-verdier`, which
holds over a field for finite coefficients of invertible exponent. Over a more general base the
comparisons fail: over `S = 𝔸¹_k`, with `E₁ = E₂ = i_*Λ` the skyscraper at the origin and
`N₁ = N₂ = Λ_S`, the source of `β` is `i_*Λ(-2)[-4]` and its target `i_*Λ(-1)[-2]`. -/
structure HasKunnethComparisons (S : Scheme.{u}) : Prop where
  /-- The `!`-Künneth map `Ku_!` is an isomorphism. -/
  kunnethShriek : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
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
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      [(R(f₁)_![A]).IsLeftAdjoint] [(R(f₂)_![A]).IsLeftAdjoint]
      [(R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).IsLeftAdjoint]
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
      [(R(b)_![A]).IsLeftAdjoint] [(R(pullback.fst a b)_![A]).IsLeftAdjoint]
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

It is stated over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible
in `k`, as in the blueprint. The headline case is `kunnethVerdier`: for `X` and `Y` separated of
finite type over `S = Spec k`,
with projections `p_X : X ×_S Y ⟶ X` and `p_Y : X ×_S Y ⟶ Y`, and for `M` in `Dctf(X, A)`
and `N` in `Dctf(Y, A)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`

on `X ×_S Y`, where `𝔻_Y = RHom(-, ω_Y)` is the Verdier dual relative to `b : Y ⟶ S`. -/
theorem hasKunnethComparisons (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (k : Type u)
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] :
    HasKunnethComparisons (ModuleCat.{u + 1} Λ) (Spec (.of k)) :=
  sorry

end Etale

end AlgebraicGeometry
