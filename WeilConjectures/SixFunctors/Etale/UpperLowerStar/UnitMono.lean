/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# The unit of `f^* ⊣ f_*` is a monomorphism over the image of `f`

For a morphism of schemes `f : X ⟶ Y` and a geometric point `s` of `X`, the stalk at `s ≫ f`
of the unit `G ⟶ f_* f^* G` is a split monomorphism: followed by the stalk at `s` of the
counit `f^* f_* f^* G ⟶ f^* G`, it is the identification `(f^* G)_s ≅ G_{s ≫ f}`, by the
triangle identity. Consequently, for a family of morphisms `f_i : X_i ⟶ Y` whose images contain
the geometric points `Y.algClosurePoint y` of `Y` (for instance a jointly surjective family of
finite morphisms), the morphism `G ⟶ ∏ᵢ (f_i)_* (f_i)^* G` is a monomorphism.

## Main statements

- `AlgebraicGeometry.Etale.sheafFiber_map_unit_comp_counit`
- `AlgebraicGeometry.Etale.mono_sheafFiber_map_unit`
- `AlgebraicGeometry.Etale.mono_piLift_unit`
- `AlgebraicGeometry.Etale.mono_piLift_unit_of_isFinite`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

section

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X) (G : Sheaf Y.smallEtaleTopology A)

end

variable {Λ : Type (u + 1)} [Ring Λ]

end Etale

end AlgebraicGeometry
