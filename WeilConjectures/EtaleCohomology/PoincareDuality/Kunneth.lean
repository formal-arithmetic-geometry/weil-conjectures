/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.EtaleCohomology.PoincareDuality.Operations
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!

# The supported product over a relative base

The relative Künneth formula for compact supports, applied to complexes supported on closed
subschemes: for closed immersions `i : Z ↪ X` and `j : W ↪ Y` over a base `B`,

`Rf_!(i_* i^* K) ⊗ᴸ Rg_!(j_* j^* L) ≅ Rh_!((i ×_B j)_* (i ×_B j)^* (K ⊠ L))`,

where `h = f ×_B g : X ×_B Y ⟶ B` and `K ⊠ L = Lp^* K ⊗ᴸ Lq^* L` is the exterior product
along the two projections. For `B = Spec k` this reads

`RΓ_c(Z, i^* K) ⊗ᴸ RΓ_c(W, j^* L) ≅ RΓ_c(Z × W, (K ⊠ L)|_{Z × W})`.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.externalProduct`: the exterior product `K ⊠ L` over `B`.
- `AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_externalProduct_iso`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/-- The exterior product `K ⊠ L = Lp^* K ⊗ᴸ Lq^* L` over a base `B`, along the projections
`p` and `q` of the fibre product `X ×_B Y`. -/
noncomputable def externalProduct
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback f g)) A) :=
  ((-⊗ᴸ-(pullback f g)[A]).obj ((L((pullback.fst f g)^*[A])).obj K)).obj
    ((L((pullback.snd f g)^*[A])).obj M)

/-- Blueprint `sk-thm-product`: Supported product over a relative base.

For closed immersions `i : Z ↪ X` and `j : W ↪ Y` over a base `B`, the compactly supported
pushforwards of the complexes supported on `Z` and on `W` multiply to the compactly supported
pushforward of the exterior product supported on `Z ×_B W`. -/
theorem nonempty_rightDerivedLowerShriek_externalProduct_iso
    [HasCompactification f] [HasCompactification g]
    [HasCompactification (pullback.fst f g ≫ f)]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    Nonempty
      (((-⊗ᴸ-(B)[A]).obj
          ((R(f)_![A]).obj ((R((i)_*[A])).obj ((L((i)^*[A])).obj K)))).obj
        ((R(g)_![A]).obj ((R((j)_*[A])).obj ((L((j)^*[A])).obj M))) ≅
      (R(pullback.fst f g ≫ f)_![A]).obj
        ((R(((pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 B) (by simp) (by simp)))_*[A])).obj
          ((L(((pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 B) (by simp) (by simp)))^*[A])).obj
            (externalProduct A f g K M)))) :=
  sorry

end ProEtale

end AlgebraicGeometry
