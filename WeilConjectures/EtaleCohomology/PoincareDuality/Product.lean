/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth

/-!
# The supported product over a relative base

The relative product theorem for compact supports
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`,
`sk-thm-sf-kunneth-relative`), applied to complexes supported on closed subschemes: for
`f : X ⟶ B`, `g : Y ⟶ B` and closed immersions `i : Z ⟶ X`, `j : W ⟶ Y`,

`Rf_!(i_* i^* K) ⊗ᴸ Rg_!(j_* j^* L) ≅ Rh_!((i ×_B j)_* (i ×_B j)^* (K ⊠ L))`,

where `h = f ×_B g : X ×_B Y ⟶ B` is `CategoryTheory.Limits.pullback.toBase`,
`i ×_B j : Z ×_B W ⟶ X ×_B Y` is `CategoryTheory.Limits.pullback.mapOverBase` and
`K ⊠ L = Lp^* K ⊗ᴸ Lq^* L` is `AlgebraicGeometry.Etale.externalProduct`. Over `B = Spec k`
this is the Künneth formula for the compactly supported cohomology of `Z × W`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
  (`sk-thm-product`).
- `AlgebraicGeometry.Etale.nonempty_iso_compactlySupported_externalProduct_closedImmersion`
  (`sk-thm-product`, the case `B = Spec k`).

## Implementation notes

As in `WeilConjectures.SixFunctors.Etale.Derived.Kunneth`, the comparison map is not
constructed and the statements record the existence of the isomorphisms. The coefficient
category is the abstract `A` of the six-functor formalism; the chapter's finite coefficients
are `A = ModuleCat Λ`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

variable {B X Y Z W : Scheme.{u}}

/-- Blueprint `sk-thm-product`: Supported product over a relative base.

Let `f : X ⟶ B` and `g : Y ⟶ B` be separated of finite type, `h = f ×_B g`, and let
`i : Z ⟶ X`, `j : W ⟶ Y` be closed immersions, with product
`i ×_B j : Z ×_B W ⟶ X ×_B Y`. For `K` in `Dctf(X, A)` and `L` in `Dctf(Y, A)`,

`Rf_!(i_* i^* K) ⊗ᴸ Rg_!(j_* j^* L) ≅ Rh_!((i ×_B j)_* (i ×_B j)^* (K ⊠ L))`.

This is the relative product theorem `sk-thm-sf-kunneth-relative` for the complexes
`i_* i^* K` and `j_* j^* L`. -/
theorem nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion
    (f : X ⟶ B) (g : Y ⟶ B) [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g] [HasCompactification (pullback.toBase f g)]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hL : DerivedCategory.constructibleFiniteTor A Y L) :
    Nonempty ((R(f)_![A]).obj ((R((i)_*[A])).obj ((L((i)^*[A])).obj K)) ⊗
        (R(g)_![A]).obj ((R((j)_*[A])).obj ((L((j)^*[A])).obj L)) ≅
      (R(pullback.toBase f g)_![A]).obj
        ((R((pullback.mapOverBase i j f g)_*[A])).obj
          ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L)))) :=
  sorry

/-- Blueprint `sk-thm-product`: Supported product over a relative base.

The case `B = Spec k`: for `X`, `Y` separated of finite type over a field `k` and closed
subschemes `i : Z ⟶ X`, `j : W ⟶ Y`,

`RΓ_c(Z, i^* K) ⊗ᴸ RΓ_c(W, j^* L) ≅ RΓ_c(Z × W, (K ⊠ L)|_{Z × W})`,

written one step earlier, in `D((Spec k)_ét)`, with the structure morphisms `i ≫ f`,
`j ≫ g` of `Z`, `W` and `Z × W ⟶ Spec k`. -/
theorem nonempty_iso_compactlySupported_externalProduct_closedImmersion
    {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [HasCompactification (i ≫ f)] [HasCompactification (j ≫ g)]
    [HasCompactification (pullback.toBase (i ≫ f) (j ≫ g))]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hL : DerivedCategory.constructibleFiniteTor A Y L) :
    Nonempty ((R(i ≫ f)_![A]).obj ((L((i)^*[A])).obj K) ⊗
        (R(j ≫ g)_![A]).obj ((L((j)^*[A])).obj L) ≅
      (R(pullback.toBase (i ≫ f) (j ≫ g))_![A]).obj
        ((L((pullback.mapOverBase i j f g)^*[A])).obj (externalProduct A f g K L))) :=
  sorry

end Etale

end AlgebraicGeometry
