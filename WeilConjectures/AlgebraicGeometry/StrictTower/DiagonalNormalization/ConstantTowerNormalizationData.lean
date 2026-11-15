/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization

/-! # Canonical constant-tower diagonal comparisons

These abbreviations expose the existing constructions through a definition-owned interface.
They do not use the conclusion of `constantTowerDirectImageNormalization` or its coefficient
completeness hypothesis. The diagonal K-injective instance is re-exported with the same data.

## References

* [Stacks Project](https://stacks.math.columbia.edu), Tags 08BJ, 070K, 07A7
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower.DiagonalNormalization

variable (A : Type (u + 1)) [CommRing A]

/-- The exact localization of the ordinary constant-diagram functor. -/
abbrev delta (X : Scheme.{u}) : DerivedCategory (Modules A X) ⥤ Derived A X :=
  ConstantNormalization.delta A X

/-- The total right derived single-level direct image with its existing derived unit. -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules A X) ⥤ DerivedCategory (Modules A Y) :=
  ConstantNormalization.push A f

/-- The fixed derived-unit composition isomorphism from push followed by the diagonal
to the diagonal followed by tower direct image. Its ordinary middle square is compConstIso. -/
abbrev chi {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ delta A Y ≅ delta A X ⋙ R A f :=
  ConstantNormalization.chi A f

end AlgebraicGeometry.ProEtale.StrictTower.DiagonalNormalization
