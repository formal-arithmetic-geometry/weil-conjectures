/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange

/-!

# The comparison of derived lower shrieks along a refinement: definitions

## Main definitions

- `AlgebraicGeometry.Etale.refinementLowerStarComp`: the composition isomorphism
  `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards attached to a refinement.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the
  comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+`. (blueprint: `BA43-RHO`)

See `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison` for the construction and
the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The composition isomorphism `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards on étale
sheaves attached to a refinement `r : c.Refinement d`, coming from
`Etale.lowerStarComp` and the relation `r.hom ≫ d.g = c.g`. -/
noncomputable def refinementLowerStarComp : (r.hom)_*[A] ⋙ (d.g)_*[A] ≅ (c.g)_*[A] :=
  Etale.lowerStarComp A r.hom d.g ≪≫ eqToIso (by rw [r.hom_g])

end Etale

end AlgebraicGeometry
