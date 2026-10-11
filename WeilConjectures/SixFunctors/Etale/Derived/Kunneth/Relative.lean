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
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs

/-!

# The relative product theorem on the étale site

The ordinary Künneth formula with an identity factor, the relative product theorem for `Rf_!`
and its variants for complexes supported on closed subschemes, for the external product
`AlgebraicGeometry.Etale.externalProduct`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`sk-lem-sf-kunneth-star`, `lem-trf-ordinary-kunneth`): `Rf_* M ⊠ Q ≅ R(f × id_Z)_* (M ⊠ Q)`
  over a field, for a finite coefficient ring of invertible exponent.
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

See `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` for the implementation notes.

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

omit [HasSmallSiteSheafify A] in
/-- The assembly step of the relative product theorem `sk-thm-sf-kunneth-relative`: with
`p`, `q` the projections of `X ×_B Y`, a composition isomorphism
`R(f ×_B g)_! ≅ Rq_! ⋙ Rg_!`, the projection formula for `q` at `(Lp^*K, M)`, compact-support
base change `Lg^* Rf_! K ≅ Rq_! Lp^* K` and the projection formula for `g` at `(M, Rf_! K)` give
`R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_of_iso [UpperStarPreservesFlat A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
    [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (e₁ : R(pullback.toBase f g)_![A] ≅ R(pullback.snd f g)_![A] ⋙ R(g)_![A])
    (h₂ : HasProjectionFormula A (pullback.snd f g)
      ((L((pullback.fst f g)^*[A])).obj K) M)
    (e₃ : (L((g)^*[A])).obj ((R(f)_![A]).obj K) ≅
      (R(pullback.snd f g)_![A]).obj ((L((pullback.fst f g)^*[A])).obj K))
    (h₄ : HasProjectionFormula A g M ((R(f)_![A]).obj K)) :
    Nonempty ((R(pullback.toBase f g)_![A]).obj (externalProduct A f g K M) ≅
      ((-⊗ᴸ-(B)[A]).obj ((R(f)_![A]).obj K)).obj ((R(g)_![A]).obj M)) := by
  have : IsIso (((projectionMap A (pullback.snd f g)).app
    ((L((pullback.fst f g)^*[A])).obj K)).app M) := h₂
  have : IsIso (((projectionMap A g).app M).app ((R(f)_![A]).obj K)) := h₄
  obtain ⟨βY⟩ := nonempty_iso_derivedTensor_flip A Y
  obtain ⟨βB⟩ := nonempty_iso_derivedTensor_flip A B
  exact ⟨e₁.app _ ≪≫ (R(g)_![A]).mapIso
    ((asIso (((projectionMap A (pullback.snd f g)).app
      ((L((pullback.fst f g)^*[A])).obj K)).app M)).symm ≪≫
    ((-⊗ᴸ-(Y)[A]).mapIso e₃.symm).app M ≪≫ (βY.app _).app M) ≪≫
    (asIso (((projectionMap A g).app M).app ((R(f)_![A]).obj K))).symm ≪≫ (βB.app _).app _⟩

/-- The relative product theorem `sk-thm-sf-kunneth-relative` for a finite coefficient ring:
`R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M` for every `K` and `M`. This is the case of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` with
coefficients `ModuleCat Λ`, by the four steps of the blueprint proof: the composition law for
`f ×_B g = q ≫ g`, the projection formula for `q`, compact-support base change for the
cartesian square of `f` and `g`, and the projection formula for `g`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_of_finite (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f]
    [HasCompactification g] [QuasiCompact f] [HasCompactification (pullback.toBase f g)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(pullback.toBase f g)_![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) f g K M) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj M)) := by
  have sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : QuasiCompact (pullback.snd f g) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hcomp : ∀ (t : pullback f g ⟶ B) [HasCompactification t], pullback.snd f g ≫ g = t →
      Nonempty (R(t)_![ModuleCat.{u + 1} Λ] ≅
        R(pullback.snd f g)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) := by
    rintro t _ rfl
    exact nonempty_iso_rightDerivedLowerShriek_comp Λ (pullback.snd f g) g
  obtain ⟨e₁⟩ := hcomp (pullback.toBase f g) (by simp)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  exact nonempty_iso_rightDerivedLowerShriek_externalProduct_of_iso (ModuleCat.{u + 1} Λ) f g K M e₁
    (hasProjectionFormula_of_finite Λ _ _ _)
    ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app K)
    (hasProjectionFormula_of_finite Λ _ _ _)

omit [HasSmallSiteSheafify A] in
/-- The external product is compatible with pullback: for morphisms `i : Z ⟶ X`, `j : W ⟶ Y`
over `B`, with product `i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`,

the external product on the right being taken along `i ≫ f` and `j ≫ g`. The pullbacks are
assumed to preserve flat sheaves (`AlgebraicGeometry.Etale.UpperStarPreservesFlat`, true for
`ModuleCat Λ`), which is what makes the derived pullback monoidal
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`). -/
theorem nonempty_iso_leftDerivedUpperStar_externalProduct [UpperStarPreservesFlat A]
    (f : X ⟶ B) (g : Y ⟶ B) {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Nonempty ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L) ≅
      externalProduct A (i ≫ f) (j ≫ g) ((L((i)^*[A])).obj K) ((L((j)^*[A])).obj L)) := by
  -- `K ⊠ L = Lp^* K ⊗ᴸ Lq^* L`; the derived pullback is monoidal, and
  -- `p ∘ (i ×_B j) = i ∘ p'`, `q ∘ (i ×_B j) = j ∘ q'` for the projections `p'`, `q'` of
  -- `Z ×_B W`.
  let e : pullback (i ≫ f) (j ≫ g) ⟶ pullback f g := pullback.mapOverBase i j f g
  let pb₁ : (L((e)^*[A])).obj ((L((pullback.fst f g)^*[A])).obj K) ≅
      (L((pullback.fst (i ≫ f) (j ≫ g))^*[A])).obj ((L((i)^*[A])).obj K) :=
    ((leftDerivedUpperStarComp A e (pullback.fst _ _)).app K).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (e ≫ pullback.fst _ _) (by simp [e])).app K
  let pb₂ : (L((e)^*[A])).obj ((L((pullback.snd f g)^*[A])).obj L) ≅
      (L((pullback.snd (i ≫ f) (j ≫ g))^*[A])).obj ((L((j)^*[A])).obj L) :=
    ((leftDerivedUpperStarComp A e (pullback.snd _ _)).app L).symm ≪≫
      (leftDerivedUpperStarComp A _ _ (e ≫ pullback.snd _ _) (by simp [e])).app L
  exact ⟨leftDerivedUpperStarTensorIso A e _ _ ≪≫ ((derivedTensor A _).mapIso pb₁).app _ ≪≫
    ((derivedTensor A _).obj _).mapIso pb₂⟩

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

end Etale

end AlgebraicGeometry
