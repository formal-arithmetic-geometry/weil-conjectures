/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Equivalence

/-!
# Ordinary varying-ring pullback along isomorphisms and cartesian lifts

Source: Stacks Project, Categories Tags 001J and 02C3, Schemes Tag 01JP,
and More on Étale Cohomology Tag 0F7B (cartesian open setting)
(blueprint: lem-sp-varying-ring-cartesian-lift-pullback-equivalence).

## Main definitions

- `pullIsoSourceComparison`, `pullIsoTargetComparison`: the specified ordinary
  compositor--equality-transport--identity inverse comparisons, on actual semilinear systems.

## Main statements

The isomorphism equivalence is the existing `pull_equivalence` imported from proper/open pasting.

- `cartesianLift_pull_isEquivalence`: the canonical lift of a cartesian proper/open square
  is an isomorphism and its ordinary inverse image is an equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The inverse comparison on systems over the target of a scheme isomorphism.
It first inverts the ordinary compositor, transports along `inv s ≫ s = 𝟙 X`,
and applies the ordinary identity comparison fixed by the adjunction and `modulePId`.
Thus `pull R φ (inv s)` is the specified quasi-inverse, at the level of whole systems.
Source: Stacks, Categories Tag 001J, with the comparisons of varying-ring operations
(blueprint: lem-sp-varying-ring-cartesian-lift-pullback-equivalence). -/
def pullIsoSourceComparison {U X : Scheme.{u}} (s : U ⟶ X) [IsIso s] :
    pull R φ s ⋙ pull R φ (inv s) ≅ 𝟭 (Modules R φ X) :=
  (moduleGComp R φ (inv s) s).symm ≪≫
    eqToIso (congrArg (pull R φ) (IsIso.inv_hom_id s)) ≪≫
    Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)

/-- The inverse comparison on systems over the source of a scheme isomorphism.
It first inverts the ordinary compositor, transports along `s ≫ inv s = 𝟙 U`,
and applies the specified ordinary identity comparison. These are natural isomorphisms
of semilinear systems, with no triangle identity imposed on the specified comparisons.
Source: Stacks, Categories Tag 001J, with the comparisons of varying-ring operations
(blueprint: lem-sp-varying-ring-cartesian-lift-pullback-equivalence). -/
def pullIsoTargetComparison {U X : Scheme.{u}} (s : U ⟶ X) [IsIso s] :
    pull R φ (inv s) ⋙ pull R φ s ≅ 𝟭 (Modules R φ U) :=
  (moduleGComp R φ s (inv s)).symm ≪≫
    eqToIso (congrArg (pull R φ) (IsIso.hom_inv_id s)) ≪≫
    Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 U)) (modulePId R φ U)

/-- The canonical lift of a cartesian square with quasi-compact open horizontal maps
and proper vertical maps is an isomorphism; its ordinary inverse image is an equivalence.
The quasi-inverse and both comparisons are those above, applied to this very lift.
Source: Stacks, Schemes Tag 01JP and Categories Tags 001J and 02C3;
More on Étale Cohomology Tag 0F7B, cartesian open setting
(blueprint: lem-sp-varying-ring-cartesian-lift-pullback-equivalence).

Proof: the universal property of the cartesian square produces a map from `pullback p i`
back to V compatible with both projections. Uniqueness in the given cartesian square
proves that the lift followed by this map is the identity on V. Uniqueness in the chosen
pullback proves the other inverse identity on `pullback p i`.
Apply the existing `pull_equivalence R φ` from varying-ring proper/open pasting.
Its inverse comparisons use exactly
the ordinary compositor, equality transport and identity comparison already specified.
Only cartesianness is needed for the geometric calculation; all the stated proper/open
hypotheses are retained. No coefficient flatness or finiteness hypothesis is used. -/
theorem cartesianLift_pull_isEquivalence {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper p] [IsProper r] (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    IsIso (pullback.lift k r h) ∧
      (pull R φ (pullback.lift k r h)).IsEquivalence := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
