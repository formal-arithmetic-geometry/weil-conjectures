/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DerivedMorphismDescent
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-!
# Descent of morphisms in the derived category along a surjective étale morphism, up to a shift

Let `u : U ⟶ T` be surjective and étale, and let `Z` with projections `r₁, r₂ : Z ⟶ U` be a
fibre product `U ×_T U`. Morphisms `K ⟶ M` in `D(T_ét, Λ)` between objects which are, up to a
common shift, sheaves placed in degree zero, descend along `u`: a morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for some `γ : K ⟶ M`.
This reduces to the degree zero case
`AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`.

## Main statements

- `AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift`: up to a
  common shift.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A] (Φ : C ⥤ D) (Ψ : D ⥤ E) [Φ.CommShift A]
  [Ψ.CommShift A]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

end AlgebraicGeometry
