/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantTowerDirectImageNormalization

/-! # Canonical constant-tower diagonal comparisons

Source: Stacks Project, Tags 08BJ, 070K and 07A7; the explicit constructions in
`WeilConjectures.AlgebraicGeometry.ConstantTowerDirectImageNormalization`, lines 1016–1100.
(blueprint: def-sf-constant-tower-normalization-data)

These abbreviations expose the existing constructions through a definition-owned interface.
They do not use the conclusion of `constantTowerDirectImageNormalization` or its coefficient
completeness hypothesis. The diagonal K-injective instance is re-exported with the same data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower.DiagonalNormalization

variable (A : Type (u + 1)) [CommRing A]

/-- The exact localization of the ordinary constant-diagram functor.
Source: Stacks 070K; ConstantNormalization.delta.
(blueprint: def-sf-constant-tower-normalization-data) -/
abbrev delta (X : Scheme.{u}) : DerivedCategory (Modules A X) ⥤ Derived A X :=
  ConstantNormalization.delta A X

/-- The total right derived single-level direct image with its existing derived unit.
Source: Stacks 070K; ConstantNormalization.push.
(blueprint: def-sf-constant-tower-normalization-data) -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Modules A X) ⥤ DerivedCategory (Modules A Y) :=
  ConstantNormalization.push A f

/-- The exact-localization square from the identity-component constant/pullback square.
Source: Stacks 07A7; ConstantNormalization.deltaPull, with its specified orientation.
(blueprint: def-sf-constant-tower-normalization-data) -/
abbrev deltaPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    delta A Y ⋙ G A f ≅ (modulePullback A f).mapDerivedCategory ⋙ delta A X :=
  ConstantNormalization.deltaPull A f

/-- Re-export of the existing diagonal K-injective instance used by the composition
comparison defining chi. Source: Stacks 08BJ; ConstantNormalization.delta_preservesKInjective.
(blueprint: def-sf-constant-tower-normalization-data) -/
instance diagonalPreservesKInjective (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).PreservesKInjectiveComplexes :=
  ConstantNormalization.delta_preservesKInjective A X

/-- The fixed derived-unit composition isomorphism from push followed by the diagonal
to the diagonal followed by tower direct image. Its ordinary middle square is compConstIso.
Source: Stacks 070K and 08BJ; ConstantNormalization.chi.
(blueprint: def-sf-constant-tower-normalization-data) -/
abbrev chi {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ delta A Y ≅ delta A X ⋙ R A f :=
  ConstantNormalization.chi A f

end AlgebraicGeometry.ProEtale.StrictTower.DiagonalNormalization
