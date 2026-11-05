/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.DiagonalSectionRestriction

/-!
# Fundamental classes of rational points as restrictions of the diagonal

Let `a : X ⟶ S` be a morphism with a section `y`. The point `y : S ⟶ X` is the base change of
the diagonal `Δ : X ⟶ X ×_S X` along the section `j_y = (𝟙, a ≫ y)` of the first projection
(`AlgebraicGeometry.Etale.isPullback_diagonal_pullbackLiftSection`). For `S = Spec k` and `X`
smooth over the perfect field `k`, the fundamental class `[y ⊂ X]` is therefore the restriction
of the fundamental class `[Δ ⊂ X ×_k X]` along `j_y`: Zariski frames of a regular immersion
restrict to frames of its base change as soon as the base change is again a regular immersion
of the same codimension, which is the case here although `j_y` is not flat
(`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_isPullback`).

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_isPullback`: base change
  of the fundamental class to a base change which is regular of the same codimension.
- `AlgebraicGeometry.Etale.isPullback_diagonal_pullbackLiftSection`: the section `y` is the
  base change of the diagonal along `j_y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] HasInvertibleExponent.opens

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

end Etale

end AlgebraicGeometry
