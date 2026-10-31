/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedReindexingData

/-! # PurReindexingDerivedMates

Source: Stacks Project and the extracted proof of
lem-pur-isomorphism-completed-reduction-reindexing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The ordinary isomorphism-square mate localizes to the two specified derived
mates, with their K-injective representative equations.
Source: extracted proof, steps 7 and 8; Stacks Tags 08BJ, 0FND and 07A7.
(blueprint: lem-pur-reindexing-derived-mate-localization).
Proof: reverse module reindexing is an exact left adjoint, so pullback by v
preserves K-injective complexes. On such a complex the ordinary mate therefore
computes the derived exchange. Localize its adjunction transpose; the canonical
composition comparison is computed degreewise on exact pullbacks, and the
derived adjunction fraction formula identifies that transpose with the specified
ambient mate. The right-derived units and exact-functor factorization give the
first displayed representative equation. For towers, whisker the ordinary mate
on the index category. Its components commute with every transition by naturality,
so this is a single invertible map of strict diagrams. The ringed diagram-site
realization identifies its transpose with the specified tower square followed
by its counit. Exact reverse tower reindexing again preserves K-injectives.
The same localized transpose argument gives exchangeTowerMate and its displayed
unit equation. Localizations preserve the inverse ordinary transformations,
so both specified derived mates are isomorphisms. -/
theorem purReindexingDerivedMates
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso v] [IsIso g] (sq : ChosenCartesianSquare v p' p g)
    [IsIso (purReindexingModuleMate d sq)] :
  PurCompletedReindexingSquareDerived d sq ∧
  PurCompletedReindexingSquareDerivedTowers d sq ∧
  PurCompletedReindexingSquareDerivedUnits d sq ∧
  PurCompletedReindexingSquareDerivedTowerUnits d sq := by sorry

end AlgebraicGeometry.Scheme
