/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Compact supports and ordinary direct image for a proper morphism

For a proper morphism `f` the compactly supported direct image `Rf_!` is the ordinary one
`Rf_*`. This is what lets the Poincaré duality chapter replace `H_c` by `H` for proper `X`
(`sk-def-trace-cup`, `sk-cor-trace`, the proper clause of `sk-thm-derived-duality`).

For the chosen compactification `(i, g)` of `f` the forget-supports map
`Rf_! ⟶ Rg_* Ri_*` is `AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`, and
`Rg_* Ri_* ≅ R(i ≫ g)_* = Rf_*` is the conjugate of the composition isomorphism of the
derived pullbacks.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStarCompIso`: `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoLowerStar`: `Rf_! ≅ Rf_*` for proper `f`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*` of the derived direct images:
the conjugate, under the adjunctions `Lg^* ⊣ Rg_*`, of the composition isomorphism
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp` of the derived pullbacks. -/
noncomputable def rightDerivedLowerStarCompIso {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) :
    R((g₁)_*[A]) ⋙ R((g₂)_*[A]) ≅ R((g₁ ≫ g₂)_*[A]) :=
  (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction A (g₁ ≫ g₂))
    ((derivedUpperStarLowerStarAdjunction A g₂).comp
      (derivedUpperStarLowerStarAdjunction A g₁))
    (leftDerivedUpperStarComp A g₁ g₂).symm).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [HasCompactification f]

/-- For a proper morphism `f` the forget-supports map `Rf_! ⟶ Rg_* Ri_*` of the chosen
compactification `(i, g)` is an isomorphism. The open immersion `i : X ⟶ X̄` is then also
closed, since `X` is proper over `Y` and `X̄` is separated over `Y`, so `X` is open and closed
in `X̄` and the comparison `D(i_!) ⟶ Ri_*` is an isomorphism. This generalises
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isClosedImmersion`. -/
theorem isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper :
    IsIso (rightDerivedLowerShriekToLowerStarComp A f) :=
  sorry

/-- For a proper morphism `f`, compactly supported and ordinary direct image agree,
`Rf_! ≅ Rf_*`: the forget-supports map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper`, followed
by `Rg_* Ri_* ≅ R(i ≫ g)_* = Rf_*`. -/
noncomputable def rightDerivedLowerShriekIsoLowerStar : R(f)_![A] ≅ R((f)_*[A]) :=
  haveI := isIso_rightDerivedLowerShriekToLowerStarComp_of_isProper A f
  asIso (rightDerivedLowerShriekToLowerStarComp A f) ≪≫
    rightDerivedLowerStarCompIso A _ _ ≪≫
      eqToIso (congrArg (fun h ↦ R((h)_*[A])) (HasCompactification.compactification f).comm.symm)

end Etale

end AlgebraicGeometry
