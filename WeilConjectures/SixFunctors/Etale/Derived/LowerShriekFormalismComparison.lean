/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-!
# The comparison isomorphisms of the compact support formalism on `D⁺(X_ét)`

The compact support formalism `AlgebraicGeometry.Etale.derivedPlusFormalism` compares the
compactly supported direct images attached to two compactifications through its own comparison
along a refinement, `CompactSupportFormalism.refinementComparison`, built from the base change map
of the formalism (a mate of the composition isomorphisms of the pullbacks). This file shows that
it is the comparison
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`, built from
the base change isomorphism of the extension by zero on étale sheaves. Hence the
comparison isomorphism `CompactSupportFormalism.shriekIso` of the formalism is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`, and the coherences of
blueprint `sk-prop-sf-comp-coherence` proved for one hold for the other.

The two base change maps are compared through their transposes under the derived adjunction
`D(c.i)_! ⊣ D(c.i)^*`: both are the unit of `D(d.i)_! ⊣ D(d.i)^*` followed by the composition
isomorphism `D(d.i)^* ≅ D(r.hom)^* ⋙ D(c.i)^*`
(`AlgebraicGeometry.Etale.unit_map_refinementLowerShriekBaseChangeDerivedPlusIso_hom_app`), which
is checked on complexes, where the derived unit is the levelwise unit
(`CategoryTheory.Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac`).

## Main results

- `AlgebraicGeometry.Etale.derivedPlusFormalism_refinementComparison`: the comparison along a
  refinement of the formalism is
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`.
- `AlgebraicGeometry.Etale.derivedPlusFormalism_shriekIso`: the comparison isomorphism of the
  formalism is `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

section Derived

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

end Derived

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  {c d : Compactification f}

end Torsion

end Etale

end AlgebraicGeometry
