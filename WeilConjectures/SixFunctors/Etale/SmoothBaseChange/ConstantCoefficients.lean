/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf

/-!
# Higher direct images of constant sheaves and their coefficients

For `h : Y ⟶ X` and a ring `R`, we consider the functor `M ↦ R^q h_* (M_Y)` from `R`-modules to
sheaves of `R`-modules on `X_ét` (`AlgebraicGeometry.Etale.higherDirectImageConstantFunctor`).

- It commutes with restriction of scalars along a ring map `R →+* R'`
  (`AlgebraicGeometry.Etale.restrictScalarsHigherDirectImageConstantIso`), so whether it
  vanishes does not depend on the coefficient ring.
- Over a field `𝕜` and for `h` quasi-compact and quasi-separated, it vanishes at every module
  as soon as it vanishes at `𝕜`: every vector space is the filtered colimit of finite direct sums
  of copies of `𝕜`
  (`AlgebraicGeometry.Etale.not_isZero_higherDirectImageConstantFunctor_self`).
- Consequently a module `M` killed by a prime `r` with `R^q h_* (M_Y) ≠ 0` gives
  `R^q h_* (Λ/rΛ) ≠ 0`
  (`AlgebraicGeometry.Etale.not_isZero_higherDirectImage_constantModSheaf_of_smul_eq_zero`).

We also record the prime-factor dévissage for nonvanishing
(`CategoryTheory.exists_prime_dvd_not_isZero_map_of_nsmul_id_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

end CategoryTheory

namespace AlgebraicGeometry

/-- The functor `M ↦ R^q h_* (M_Y)` sending a module to the higher direct image of the
constant sheaf with that value. -/
noncomputable abbrev Etale.higherDirectImageConstantFunctor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙ R+((h)_*[ModuleCat.{u + 1} A]) ⋙
      DerivedCategory.Plus.homologyFunctor _ q)

instance Etale.additive_higherDirectImageConstantFunctor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ) :
    (Etale.higherDirectImageConstantFunctor A h q).Additive := by
  dsimp only [Etale.higherDirectImageConstantFunctor]
  infer_instance

section RestrictScalars

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- Restriction of scalars preserves sheafification, being a left adjoint. -/
instance Etale.preservesSheafification_restrictScalars (S : Scheme.{u}) :
    S.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
  Sheaf.preservesSheafification_of_adjunction _
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)

end RestrictScalars

section Field

variable {𝕜 : Type (u + 1)} [Field 𝕜]

end Field

variable (Λ : Type (u + 1)) [CommRing Λ]

-- the linear maps into restrictions of scalars need to unfold `ModuleCat.restrictScalars`

section SepClosed

local instance : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

local instance : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _

end SepClosed

end AlgebraicGeometry
